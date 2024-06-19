-----------------------------------------------------------------------------
-- Copyright 2024, Tim Whiting.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

module Core.FlowAnalysis.Demand.DemandMonad(
  AFixChange(..), FixInput(..), FixOutput(..),
  FixDemandR, FixDemand, PostFixR, PostFix, TypeChecker,
  AnalysisKind(..),
  -- Cache / State stuff
  DemandState(..), State, toAChange, toEnv, getAllRefines, getAllStates, addResult, setResults, updateAdditionalState, getDemandState, updateDemandState,
  -- Context stuff
  getModule, getModuleR, getResults, getTopDefCtx, getQueryString, addContextId, addSpecialId, newContextId, newModContextId, addChildrenContexts,
  focusParam, focusBody, focusChild, focusFun, enterBod, succAEnv, 
  childrenContexts, visitChildrenCtxs, visitEachChild, topBindExpr, 
  -- Env stuff
  DEnv(..), DemandEnv(..), getUnique, newQuery, analysisLog, getDemandEnv,
  -- Query stuff
  Query(..), queryCtx, queryEnv, queryKind, queryKindCaps,
  emptyEnv, emptyState, transformState, loadModule, maybeLoadModule, withModuleCtx,
  setGas, useGas, decGas, withGas
  ) where

import Control.Monad.State (gets, MonadState (..))
import Control.Monad.Reader
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Set (Set)
import Data.Maybe (fromMaybe, fromJust, maybeToList)
import Core.FlowAnalysis.Demand.AbstractValue
import Core.FlowAnalysis.StaticContext
import Core.FlowAnalysis.FixpointMonad
import Core.FlowAnalysis.Monad
import Compile.Options
import Compile.BuildMonad hiding (liftIO)
import Common.Name
import Core.Core
import Compile.Module
import qualified Core.Core as C
import Control.Monad (zipWithM, when)
import Debug.Trace (trace)
import Data.List (find, intercalate)
import Common.Failure (assertion, HasCallStack)
import Common.Error (Errors)
import Type.Type (Type)

type FixDemandR r s e a = FixT (DEnv e) (State r e s) FixInput FixOutput AFixChange a
type FixDemand r s e = FixDemandR r s e (FixOutput AFixChange)
type PostFixR r s e a = FixIn (DEnv e) (State r e s) FixInput FixOutput AFixChange a
type PostFix r s e = PostFixR r s e (FixOutput AFixChange)

-- The fixpoint input is either a query to get an abstract value result, or an environment to get a set of refined environments
data FixInput =
  QueryInput Query
  | EnvInput EnvCtx deriving (Ord, Eq, Show)

-- The output of the fixpoint is either a value, or set of environments 
-- (depending on whether the input is a query or wanting the refined environments for a particular environment)
data FixOutput d =
  A AbValue
  | E (S.Set EnvCtx)
  | N deriving (Show, Eq)

data AFixChange =
  FA AChange
  | FE EnvCtx
  | B
  deriving (Show, Eq)

data AnalysisKind = BasicEnvs | LightweightEnvs | HybridEnvs deriving (Eq, Ord, Show)

type DEnv x = AnalysisEnv (DemandEnv x)
data DemandEnv x = DemandEnv {
  analysisKind :: !AnalysisKind,
  currentQuery :: !String,
  currentQueryId :: !Int,
  queryIndentation :: !String,
  additionalEnv2 :: x
}

type State r e s = BasicState r (DemandState r e s) 
data DemandState r e s = DemandState {
  -- Evaluators given an application site / environment of a primitive (what does the application evaluate to)
  primitives :: M.Map Name ((ExprContext,EnvCtx) -> FixDemandR r s e AChange),
  -- Expression relation for an application site / environment of a primitive (where does the i'th parameter flow to)
  eprimitives :: M.Map Name (Int -> (ExprContext,EnvCtx) -> FixDemandR r s e AChange),
  gas :: Int,
  outOfGas :: Bool,
  additionalState2 :: s
}

-- A query type representing the mutually recursive queries we can make that result in an abstract value
data Query =
  CallQ (ExprContext, EnvCtx) |
  ExprQ (ExprContext, EnvCtx) |
  EvalQ (ExprContext, EnvCtx) |
  EvalxQ (ExprContext, EnvCtx, Name, Type) | -- Find Applications for the type
  ExprxQ (ExprContext, EnvCtx, Type) -- Find Handler for the operation's effect type
  deriving (Eq, Ord)

getDemandState :: FixDemandR r s e (DemandState r e s)
getDemandState = additionalState <$> getState

setDemandState :: DemandState r e s ->  FixDemandR r s e ()
setDemandState ds = do
  updateDemandState (const ds) 

updateDemandState :: (DemandState r e s -> DemandState r e s) -> FixDemandR r s e ()
updateDemandState f = do
  st <- getState
  setState (st{additionalState = f (additionalState st)})

setGas :: Int -> FixDemandR r s e ()
setGas g = do
  updateDemandState $ \s ->
    s{gas = g, outOfGas = False}

useGas :: Int -> FixDemandR r s e Bool
useGas g = do
  st <- getState
  let ds = additionalState st
  let newGas = gas ds - g
  if newGas < 0 && (gas ds /= (-1)) then
    do
      trace (show $ gas ds) $ return ()
      setDemandState ds{gas = 0, outOfGas=True}
      return True
  else
    do
      setDemandState ds{gas = if gas ds < 0 then gas ds else newGas}
      return False

decGas :: FixDemandR r s e Bool
decGas = useGas 1

withGas :: FixDemandR r s e a -> FixDemandR r s e a
withGas f = do
  allout <- decGas
  if allout then trace "All out of gas" doBottom else f

emptyState :: BuildContext -> Int -> s -> State r e s
emptyState bc g s =
  emptyBasicState bc (DemandState M.empty M.empty g False s)

transformState :: (s -> x) -> (Set r -> Set b) -> Int -> State r e s -> State b e x
transformState f final gas st =
  transformBasicState (\ad -> DemandState M.empty M.empty gas False (f (additionalState2 ad))) final st

updateAdditionalState :: (s -> s) -> FixDemandR r s e ()
updateAdditionalState f = do
  st <- getState
  setState st{additionalState = (additionalState st){additionalState2 = f (additionalState2 (additionalState st))}}


emptyEnv :: HasCallStack => Int -> AnalysisKind -> TypeChecker -> Bool -> e -> DEnv e
emptyEnv m kind build log e = emptyBasicEnv m build log (DemandEnv kind "" (-1) "" e) 

-- Gets a string representing the current query
getQueryString :: FixDemandR x s e String
getQueryString = do
  denv <- getDemandEnv
  env <- getEnv
  return $ queryIndentation denv ++ show (contextId $ currentContext env) ++ " " ++ currentQuery denv ++ " "

-- Unwraps query pieces
queryCtx :: Query -> ExprContext
queryCtx (CallQ (ctx, _)) = ctx
queryCtx (ExprQ (ctx, _)) = ctx
queryCtx (EvalQ (ctx, _)) = ctx
queryCtx (EvalxQ (ctx, _, _, _)) = ctx
queryCtx (ExprxQ (ctx, _, _)) = ctx

refineQuery :: Query -> EnvCtx -> Query
refineQuery (CallQ (ctx, _)) env = CallQ (ctx, env)
refineQuery (ExprQ (ctx, _)) env = ExprQ (ctx, env)
refineQuery (EvalQ (ctx, _)) env = EvalQ (ctx, env)
refineQuery (EvalxQ (ctx, _, n, t)) env = EvalxQ (ctx, env, n, t)
refineQuery (ExprxQ (ctx, _, t)) env = ExprxQ (ctx, env, t)

queryEnv :: Query -> EnvCtx
queryEnv (CallQ (_, env)) = env
queryEnv (ExprQ (_, env)) = env
queryEnv (EvalQ (_, env)) = env
queryEnv (EvalxQ (_, env, _, _)) = env
queryEnv (ExprxQ (_, env, _)) = env

queryKind :: Query -> String
queryKind (CallQ _) = "call"
queryKind (ExprQ _) = "expr"
queryKind (EvalQ _) = "eval"
queryKind (EvalxQ _) = "evalx"
queryKind (ExprxQ _) = "exprx"

queryKindCaps :: Query -> String
queryKindCaps (CallQ _) = "CALL"
queryKindCaps (ExprQ _) = "EXPR"
queryKindCaps (EvalQ _) = "EVAL"
queryKindCaps (EvalxQ _) = "EVALX"
queryKindCaps (ExprxQ _) = "EXPRX"

instance Show Query where
  show q = queryKindCaps q ++ ": " ++ showSimpleEnv (queryEnv q) ++ " " ++ showSimpleContext (queryCtx q)


toAChange :: AFixChange -> AChange
toAChange (FA a) = a

toEnv :: AFixChange -> EnvCtx
toEnv (FE e) = e

getAllRefines :: EnvCtx -> PostFixR x s e(Set EnvCtx)
getAllRefines env = do
  res <- cacheLookup (EnvInput env)
  let res' = fmap (\v ->
                case v of
                  E e -> e
                  N -> S.empty
                  ) res
  return (S.insert env (fromMaybe S.empty res'))

getAllStates :: Query -> PostFixR x s e AbValue
getAllStates q = do
  res <- cacheLookup (QueryInput q)
  let res' = fmap (\v ->
                case v of
                  A a -> a
                  N -> emptyAbValue
                  ) res
  return $ fromMaybe emptyAbValue res'

instance Lattice FixOutput AFixChange where
  bottom = N
  join N x = x
  join x N = x
  join (A a) (A b) = A (a `joinAbValue` b)
  join (E e) (E e1) = E (S.union e e1)
  insert (FA a) N = A $ addChange emptyAbValue a
  insert (FA a) (A b) = A (addChange b a)
  insert (FE e) N = E $ S.singleton e
  insert (FE e) (E e1) = E (S.insert e e1)
  lte B N = True
  lte (FA ch) (A a) = ch `changeIn` a
  lte (FE e) (E e1) = e `S.member` e1
  lte _ _ = False
  elems (A a) = map FA $ changes a
  elems (E e) = map FE $ S.toList e
  elems N = []
  isBottom N = True
  isBottom _ = False


-- Implement the needed operations for the output to be a lattice
instance Semigroup (FixOutput d) where
  (<>) (A a) (A b) = A (a <> b)
  (<>) (E e) (E e1) = E (e <> e1)
  (<>) N x = x
  (<>) x N = x
  (<>) x y = error $ "Unexpected semigroup combination " ++ show x ++ " " ++ show y

instance Contains (FixOutput d) where
  contains (A a) (A b) = a `contains` b
  contains (E e) (E e1) = e1 `S.isSubsetOf` e
  contains _ N = True
  contains _ _ = False

instance Monoid (FixOutput d) where
  mempty = N

--- Wraps a computation with a new environment that represents the query indentation and dependencies for easier following and debugging

withDemandEnv :: (DemandEnv e -> DemandEnv e) -> FixDemandR x s e a -> FixDemandR x s e a
withDemandEnv f m =
  withEnv (\env -> env{additionalEnv = f $ additionalEnv env}) m

newQuery :: Bool -> Query -> (String -> FixDemandR x s e AChange) -> FixDemandR x s e AFixChange
newQuery isRefined q d = do
  unique <- getUnique
  withEnv (\env -> env{
      currentContext = queryCtx q, 
      additionalEnv = (additionalEnv env){
        currentQueryId = unique, 
        currentQuery = (if isRefined then "qr" else "q") ++ queryKindCaps q ++ "(" ++ show unique ++ ")" ++ ": ", 
        queryIndentation = queryIndentation (additionalEnv env) ++ " "}
      }) $ do
    query <- getQueryString
    res <- d query
    return $ FA res

getDemandEnv :: FixAR x s (DemandEnv e) i o c (DemandEnv e)
getDemandEnv = additionalEnv <$> getEnv

-- Environment helper
succAEnv :: ExprContext -> EnvCtx -> FixAR x s (DemandEnv e) i o c Ctx
succAEnv newctx p' = do
  length <- contextLength <$> getEnv
  kind <- analysisKind <$> getDemandEnv
  case kind of
    BasicEnvs -> return $ limitm (BCallCtx newctx (envhead p')) length

enterBod :: ExprContext -> EnvCtx -> ExprContext -> EnvCtx -> FixAR x s (DemandEnv e) i o c (ExprContext, EnvCtx)
enterBod lam lamenv callctx callenv = do
  bd <- focusBody lam
  -- trace (query ++ "APP: Lambda body is " ++ show lamctx) $ return []
  -- In the subevaluation if a binding for the parameter is requested, we should return the parameter in this context, 
  succ <- succAEnv callctx callenv
  let newEnv = EnvCtx succ lamenv
  return (bd, newEnv)