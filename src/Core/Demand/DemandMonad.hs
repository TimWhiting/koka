-----------------------------------------------------------------------------
-- Copyright 2024, Tim Whiting.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{-# LANGUAGE MultiParamTypeClasses #-}

module Core.Demand.DemandMonad(
  AFixChange(..), FixInput(..), FixOutput(..),
  FixDemandR, FixDemand,
  AnalysisKind(..),
  -- Cache / State stuff
  State(..), toAChange, toEnv, getAllRefines, getAllStates, getState, getCache, cacheLookup, updateState, setResult,
  -- Context stuff
  getModule, getTopDefCtx, getQueryString, addContextId, newContextId, newModContextId, addChildrenContexts,
  childrenContexts, focusParam, focusBody, focusChild, visitChildrenCtxs, visitEachChild,
  -- Env stuff
  DEnv(..), getEnv, withEnv, getUnique, newQuery,
  -- Query stuff
  Query(..), queryCtx, queryEnv, queryKind, queryKindCaps, queryVal
  ) where

import Control.Monad.State (gets, MonadState (..))
import Control.Monad.Reader
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Set (Set)
import Data.Maybe (fromMaybe, fromJust, maybeToList)
import Core.Demand.AbstractValue
import Core.Demand.StaticContext
import Core.Demand.FixpointMonad
import Compile.Options
import Compile.BuildContext
import Common.Name
import Core.Core
import Compile.Module
import qualified Core.Core as C
import Control.Monad (zipWithM)
import Debug.Trace (trace)
import Data.List (find)

type FixDemand x s e = FixDemandR x s e (FixOutput AFixChange)
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
  M.lookup i <$> getCache

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

queryVal :: Query -> (ExprContext, EnvCtx)
queryVal (CallQ x) = x
queryVal (ExprQ x) = x
queryVal (EvalQ x) = x

-- Unwraps query pieces
queryCtx :: Query -> ExprContext
queryCtx (CallQ (ctx, _)) = ctx
queryCtx (ExprQ (ctx, _)) = ctx
queryCtx (EvalQ (ctx, _)) = ctx

refineQuery :: Query -> EnvCtx -> Query
refineQuery (CallQ (ctx, _)) env = CallQ (ctx, env)
refineQuery (ExprQ (ctx, _)) env = ExprQ (ctx, env)
refineQuery (EvalQ (ctx, _)) env = EvalQ (ctx, env)

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

toAChange :: AFixChange -> AChange
toAChange (FA a) = a

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
  return (S.insert env (fromMaybe S.empty res'))

getAllStates :: Query -> FixDemandR x s e AbValue
getAllStates q = do
  res <- cacheLookup (QueryInput q)
  let res' = fmap (\(A a) -> a) res
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


changes :: AbValue -> [AChange]
changes (AbValue clos constrs lits) =
  closs ++ constrss ++ litss
  where
    closs = map (uncurry AChangeClos) $ S.toList clos
    constrss = map (uncurry AChangeConstr) $ S.toList constrs
    litss = concatMap (\(env,lat) -> changesLit lat env) $ M.toList lits

changesLit :: LiteralLattice -> EnvCtx -> [AChange]
changesLit (LiteralLattice ints floats chars strings) env =
  intChanges ++ floatChanges ++ charChanges ++ stringChanges
  where
    intChanges = map (\x -> AChangeLit (LiteralChangeInt x) env) $ elems ints
    floatChanges = map (\x -> AChangeLit (LiteralChangeFloat x) env) $ elems floats
    charChanges = map (\x -> AChangeLit (LiteralChangeChar x) env) $ elems chars
    stringChanges = map (\x -> AChangeLit (LiteralChangeString x) env) $ elems strings

changeIn :: AChange -> AbValue -> Bool
changeIn (AChangeClos ctx env) (AbValue clos _ _) = S.member (ctx,env) clos
changeIn (AChangeConstr ctx env) (AbValue _ constr _) = S.member (ctx,env) constr
changeIn (AChangeLit lit env) (AbValue _ _ lits) =
  case M.lookup env lits of
    Just (LiteralLattice ints floats chars strings) ->
      case lit of
        LiteralChangeInt i -> i `lte` ints
        LiteralChangeFloat f -> f `lte` floats
        LiteralChangeChar c -> c `lte` chars
        LiteralChangeString s -> s `lte` strings
    Nothing -> False

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

------------------------ Navigating the syntax tree ----------------------------------
focusParam :: Maybe Int -> ExprContext -> FixDemandR x s e ExprContext
focusParam index e = do
  children <- childrenContexts e
  query <- getQueryString
  return $ case index of
    Just x | x + 1 < length children -> children !! (x + 1) -- Parameters are the not the first child of an application (that is the function)
    _ -> error (query ++ "Children looking for param " ++ show children ++ " in " ++ show e ++ " index " ++ show index) Nothing

focusBody :: ExprContext -> FixDemandR x s e ExprContext
focusBody e = do
  children <- childrenContexts e
  query <- getQueryString
  return $ case find (\x -> case x of
              LamCBody{} -> True
              _ -> False) children of
    Just x -> x
    Nothing -> error (query ++ "Children looking for body " ++ show children) Nothing

focusChild :: ExprContext -> Int -> FixDemandR x s e ExprContext
focusChild e index = do
  children <- childrenContexts e
  query <- getQueryString
  return $ if index < length children then
    -- trace (query ++ "Focused child " ++ show (children !! index) ++ " " ++ show index ++ " " ++ show children) $
      children !! index
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
  return N


--- Wraps a computation with a new environment that represents the query indentation and dependencies for easier following and debugging
newQuery :: Query -> (String -> FixDemandR x s e AChange) -> FixDemandR x s e AFixChange
newQuery q d = do
  unique <- getUnique
  withEnv (\env -> env{currentContext = queryCtx q, currentEnv = queryEnv q, currentQuery = "q" ++ show unique ++ "(" ++ queryKindCaps q ++ ")" ++ ": ", queryIndentation = queryIndentation env ++ " "}) $ do
    query <- getQueryString
    res <- d query
    return $ FA res

--------------------------------------- ExprContext Helpers -------------------------------------

allModules :: BuildContext -> [Module]
allModules = buildcModules

getTopDefCtx :: ExprContext -> Name -> FixDemandR x s e ExprContext
getTopDefCtx ctx name = do
  children <- childrenContexts ctx
  case find (\dctx -> case dctx of
      DefCNonRec{} | defName (defOfCtx dctx) == name -> True
      DefCRec{} | defName (defOfCtx dctx) == name -> True
      _ -> False
      ) children of
    Just dctx -> do
      -- lamctx <- focusChild dctx 0 -- Actually focus the lambda
      return dctx
    Nothing -> error $ "getTopDefCtx: " ++ show ctx ++ " " ++ show name

getModule :: Name -> FixDemandR x s e Module
getModule name = do
  deps <- buildcModules . buildc <$> getState
  let x = find (\m -> modName m == name) deps
  case x of
    Just mod -> return mod
    _ -> error $ "getModule: " ++ show name

addChildrenContexts :: ExprContextId -> [ExprContext] -> FixDemandR x s e ()
addChildrenContexts parentCtx contexts = do
  state <- getState
  let newIds = map contextId contexts
      newChildren = M.insert parentCtx (S.fromList newIds) (childrenIds state)
   -- trace ("Adding " ++ show childStates ++ " previously " ++ show (M.lookup parentCtx (childrenIds state))) 
  setState state{childrenIds = newChildren}

newContextId :: FixDemandR x s e ExprContextId
newContextId = do
  state <- getState
  id <- currentContext <$> getEnv
  let newCtxId = maxContextId state + 1
  updateState (\s -> s{maxContextId = newCtxId})
  return $! ExprContextId newCtxId (moduleName (contextId id))

newModContextId :: Module -> FixDemandR x s e ExprContextId
newModContextId mod = do
  state <- getState
  let newCtxId = maxContextId state + 1
  updateState (\s -> s{maxContextId = newCtxId})
  return $! ExprContextId newCtxId (modName mod)

addContextId :: (ExprContextId -> ExprContext) -> FixDemandR x s e ExprContext
addContextId f = do
  newId <- newContextId
  state <- getState
  let x = f newId
  setState state{states=M.insert newId x (states state)}
  return x

childrenOfExpr :: ExprContext -> Expr -> FixDemandR x s e [ExprContext]
childrenOfExpr ctx expr =
  case expr of
    Lam names eff e -> addContextId (\newId -> LamCBody newId ctx names e) >>= single
    App f vs -> do
      x <- addContextId (\newId -> AppCLambda newId ctx f )
      rest <- zipWithM (\i x -> addContextId (\newId -> AppCParam newId ctx i x)) [0..] vs
      return $! x : rest
    Let defs result -> do
      let defNames = map defTName (concatMap defsOf defs)
      defs <- zipWithM (\i x -> addContextId (\newId -> LetCDef newId ctx defNames i defs)) [0..] defs
      result <- addContextId (\newId -> LetCBody newId ctx defNames result)
      return $! result:defs
    Case exprs branches -> do
      match <- addContextId (\newId -> CaseCMatch newId ctx (head exprs))
      branches <- zipWithM (\i x -> addContextId (\newId -> CaseCBranch newId ctx (branchVars x) i x)) [0..] branches
      return $! match : branches
    Var name info -> addContextId (\newId -> ExprCBasic newId ctx expr ) >>= single
    TypeLam tvars expr -> childrenOfExpr ctx expr
    TypeApp expr tps -> childrenOfExpr ctx expr
    Con name repr -> addContextId (\newId -> ExprCBasic newId ctx expr) >>= single
    Lit lit -> addContextId (\newId -> ExprCBasic newId ctx expr) >>= single
  where single x = return [x]

childrenOfDef :: ExprContext -> C.DefGroup -> FixDemandR x s e [ExprContext]
childrenOfDef ctx def =
  case def of
    C.DefNonRec d -> addContextId (\newId -> DefCNonRec newId ctx [defTName d] def) >>= (\x -> return [x])
    C.DefRec ds -> zipWithM (\i d -> addContextId (\newId -> DefCRec newId ctx (map defTName ds) i def)) [0..] ds

childrenContexts :: ExprContext -> FixDemandR x s e [ExprContext]
childrenContexts ctx = do
  withEnv (\env -> env{currentContext = ctx, currentModContext = case ctx of {ModuleC{} -> ctx; _ -> currentModContext env}}) $ do
    let parentCtxId = contextId ctx
    children <- childrenIds <$> getState
    let childIds = M.lookup parentCtxId children
    case childIds of
      Nothing -> do
          -- trace ("No children for " ++ show ctx) $ return ()
          newCtxs <- case ctx of
                ModuleC _ mod _ -> do
                  res <- mapM (childrenOfDef ctx) (coreProgDefs $ fromJust $ modCoreUnopt mod)
                  return $! concat res
                DefCRec{} -> childrenOfExpr ctx (exprOfCtx ctx)
                DefCNonRec{} -> childrenOfExpr ctx (exprOfCtx ctx)
                LamCBody _ _ names body -> childrenOfExpr ctx body
                AppCLambda _ _ f -> childrenOfExpr ctx f
                AppCParam _ _ _ param -> childrenOfExpr ctx param
                LetCDef{} -> childrenOfExpr ctx (exprOfCtx ctx)
                LetCBody _ _ _ e -> childrenOfExpr ctx e
                CaseCMatch _ _ e -> childrenOfExpr ctx e
                CaseCBranch _ _ _ _ b -> do
                  x <- mapM (childrenOfExpr ctx . guardExpr) $ branchGuards b -- TODO Better context for branch guards
                  return $! concat x
                ExprCBasic{} -> return []
                ExprCTerm{} -> return []
          addChildrenContexts parentCtxId newCtxs
          -- trace ("Got children for " ++ show ctx ++ " " ++ show newCtxs) $ return newCtxs
          return newCtxs
      Just childIds -> do
        -- trace ("Got children for " ++ show ctx ++ " " ++ show childIds) $ return ()
        states <- states <$> getState
        return $! map (states M.!) (S.toList childIds)

visitChildrenCtxs :: ([a] -> a) -> ExprContext -> FixDemandR x s e a -> FixDemandR x s e a
visitChildrenCtxs combine ctx analyze = do
  children <- childrenContexts ctx
  -- trace ("Got children of ctx " ++ show ctx ++ " " ++ show children) $ return ()
  res <- mapM (\child -> withEnv (\e -> e{currentContext = child}) analyze) children
  return $! combine res

visitEachChild :: Show a => ExprContext -> FixDemandR x s e a -> FixDemandR x s e a
visitEachChild ctx analyze = do
  children <- childrenContexts ctx
  -- trace ("Got children of ctx " ++ show ctx ++ " " ++ show children) $ return ()
  each $ map (\child -> withEnv (\e -> e{currentContext = child}) analyze) children
