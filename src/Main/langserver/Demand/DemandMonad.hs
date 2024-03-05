{-# LANGUAGE MultiParamTypeClasses #-}

module Demand.DemandMonad(
  FixDemandR, FixDemand, State(..),  
  AnalysisKind, DEnv(..), Query(..),
  getState, getCache, cacheLookup) where

import Control.Monad.State (gets, MonadState (..))
import Control.Monad.Reader
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Set (Set)
import Data.Maybe (fromMaybe)
import Demand.AbstractValue
import Demand.StaticContext
import Demand.FixpointMonad
import Compile.Options
import Compile.BuildContext
import Common.Name

type FixDemand x s e = FixDemandR x s e AFixChange
type FixDemandR x s e a = FixTR (DEnv e) (State x s) FixInput FixOutput AFixChange a

data State a x = State{
  buildc :: BuildContext,
  states :: M.Map ExprContextId ExprContext,
  maxContextId :: Int,
  childrenIds :: M.Map ExprContextId (Set ExprContextId),
  unique :: Int,
  finalResult :: Maybe a,
  primitives :: M.Map Name ExprContext,
  additionalState :: x
}

getState :: FixDemandR x s e (State x s)
getState = gets snd

getCache :: FixDemandR x s e (M.Map FixInput (FixOutput AFixChange))
getCache = do 
  res <- gets fst
  return $ M.map fst res

cacheLookup :: FixInput -> FixDemandR x s e (Maybe (FixOutput AFixChange))
cacheLookup i = do
  res <- getCache
  return $ M.lookup i res

setState :: State x s -> FixDemandR x s e ()
setState x = do
  st <- get
  put (fst st, x)

data AnalysisKind = BasicEnvs | LightweightEnvs | HybridEnvs deriving (Eq, Ord, Show)

data DEnv x = DEnv{
  contextLength :: !Int,
  term :: !Terminal,
  flags :: !Flags,
  analysisKind :: !AnalysisKind,
  currentContext :: !ExprContext,
  currentModContext :: !ExprContext,
  currentEnv :: !EnvCtx,
  currentQuery :: !String,
  queryIndentation :: !String,
  additionalEnv :: x
}

withEnv :: (DEnv e -> DEnv e) -> FixDemandR x s e a -> FixDemandR x s e a
withEnv = local

getEnv :: FixDemandR x s e (DEnv e)
getEnv = ask

-- A query type representing the mutually recursive queries we can make that result in an abstract value
data Query =
  CallQ (ExprContext, EnvCtx) |
  ExprQ (ExprContext, EnvCtx) |
  EvalQ (ExprContext, EnvCtx) deriving (Eq, Ord)

-- Unwraps query pieces
queryCtx :: Query -> ExprContext
queryCtx (CallQ (ctx, _)) = ctx
queryCtx (ExprQ (ctx, _)) = ctx
queryCtx (EvalQ (ctx, _)) = ctx

queryEnv :: Query -> EnvCtx
queryEnv (CallQ (_, env)) = env
queryEnv (ExprQ (_, env)) = env
queryEnv (EvalQ (_, env)) = env

queryKind :: Query -> String
queryKind (CallQ _) = "call"
queryKind (ExprQ _) = "expr"
queryKind (EvalQ _) = "eval"

queryKindCaps :: Query -> String
queryKindCaps (CallQ _) = "CALL"
queryKindCaps (ExprQ _) = "EXPR"
queryKindCaps (EvalQ _) = "EVAL"

instance Show Query where
  show q = queryKindCaps q ++ ": " ++ showSimpleEnv (queryEnv q) ++ " " ++ showSimpleContext (queryCtx q)

-- The fixpoint input is either a query to get an abstract value result, or an environment to get a set of refined environments
data FixInput =
  QueryInput Query
  | EnvInput EnvCtx deriving (Ord, Eq, Show)

data AFixChange =
  FA AChange
  | FE EnvCtx
  | B
  deriving (Show, Eq)

toAbValue :: AFixChange -> AChange
toAbValue (FA a) = a

toEnv :: AFixChange -> EnvCtx
toEnv (FE e) = e

-- The output of the fixpoint is either a value, or set of environments 
-- (depending on whether the input is a query or wanting the refined environments for a particular environment)
data FixOutput d =
  A AbValue
  | E (S.Set EnvCtx)
  | N deriving (Show, Eq)

getAllRefines :: EnvCtx -> FixDemandR x s e (Set EnvCtx)
getAllRefines env = do
  res <- cacheLookup (EnvInput env)
  let res' = fmap (\(E e) -> e) res
  return $ fromMaybe S.empty res'

instance Lattice FixOutput AFixChange where
  bottom = N
  join N x = x
  join x N = x
  join (A a) (A b) = A (a `join` b)
  join (E e) (E e1) = E (e `join` e1)
  insert (FA a) N = bottom `join` a

-- Implement the needed operations for the output to be a lattice
instance Semigroup (FixOutput d) where
  (<>) (A a) (A b) = A (a <> b)
  (<>) (E e) (E e1) = E (e <> e1)
  (<>) N x = x
  (<>) x N = x
  (<>) x y = error $ "Unexpected semigroup combination " ++ show x ++ " " ++ show y

instance Contains (FixOutput d) where
  contains (A (BL a)) (A (BL b)) = a `contains` b
  contains (E e) (E e1) = e1 `S.isSubsetOf` e
  contains _ N = True
  contains _ _ = False

instance Monoid (FixOutput d) where
  mempty = N

------------------------ Navigating the syntax tree ----------------------------------
focusParam :: Maybe Int -> ExprContext -> FixDemandR x s e (Maybe ExprContext)
focusParam index e = do
  children <- childrenContexts e
  query <- getQueryString
  return $ case index of
    Just x | x + 1 < length children -> Just $ children !! (x + 1) -- Parameters are the not the first child of an application (that is the function)
    _ -> error (query ++ "Children looking for param " ++ show children ++ " in " ++ show e ++ " index " ++ show index) Nothing

focusBody :: ExprContext -> FixDemandR x s e (Maybe ExprContext)
focusBody e = do
  children <- childrenContexts e
  query <- getQueryString
  return $ case find (\x -> case x of
              LamCBody{} -> True
              _ -> False) children of
    Just x -> Just x
    Nothing -> error (query ++ "Children looking for body " ++ show children) Nothing

focusChild :: ExprContext -> Int -> FixDemandR x s e (Maybe ExprContext)
focusChild e index = do
  children <- childrenContexts e
  query <- getQueryString
  return $ if index < length children then
    -- trace (query ++ "Focused child " ++ show (children !! index) ++ " " ++ show index ++ " " ++ show children) $
      Just (children !! index)
    else error (query ++ "Children looking for child at " ++ show index ++ " " ++ show children) Nothing


------------------ State and Environment Helpers -----------------------------------

-- Gets a string representing the current query
getQueryString :: FixDemandR x s e String
getQueryString = do
  env <- getEnv
  return $ queryIndentation env ++ currentQuery env ++ show (contextId $ currentContext env) ++ " "

getUnique :: FixDemandR x s e Int
getUnique = do
  st <- getState
  let u = unique st
  setState st{unique = u + 1}
  return u

updateState :: (State x s -> State x s) -> FixDemandR x s e ()
updateState update = do
  st <- getState
  setState $ update st

setResult :: x -> FixDemand x s e
setResult x = do
  updateState (\st -> st{finalResult = Just x})
  return B

instantiate :: String -> EnvCtx -> EnvCtx -> FixDemandR x s e ()
instantiate query c1 c0 = if c1 == c0 then return () else do
  trace (query ++ "INST: " ++ showSimpleEnv c0 ++ " to " ++ showSimpleEnv c1) $ return ()
  loop (EnvInput c0)
  push (EnvInput c0) (FE c1)
  return ()

--- Wraps a computation with a new environment that represents the query indentation and dependencies for easier following and debugging
newQuery :: Query -> (String -> FixDemandR x s e AChange) -> FixDemandR x s e AFixChange
newQuery q d = do
  unique <- getUnique
  withEnv (\env -> env{currentContext = queryCtx q, currentEnv = queryEnv q, currentQuery = "q" ++ show unique ++ "(" ++ queryKindCaps q ++ ")" ++ ": ", queryIndentation = queryIndentation env ++ " "}) $ do
    query <- getQueryString
    res <- d query
    return $ A $ FA res