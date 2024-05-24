-----------------------------------------------------------------------------
-- Copyright 2024, Tim Whiting.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

module Core.Demand.DemandMonad(
  AFixChange(..), FixInput(..), FixOutput(..),
  FixDemandR, FixDemand, PostFixR, PostFix, TypeChecker,
  AnalysisKind(..),
  -- Cache / State stuff
  State(..), toAChange, toEnv, getAllRefines, getAllStates, addResult, setResults, updateAdditionalState,
  -- Context stuff
  getModule, getModuleR, getResults, getTopDefCtx, getQueryString, addContextId, addSpecialId, newContextId, newModContextId, addChildrenContexts,
  focusParam, focusBody, focusChild, focusFun, enterBod, succAEnv,
  childrenContexts, visitChildrenCtxs, visitEachChild, topBindExpr,
  -- Env stuff
  DEnv(..), getUnique, newQuery, demandLog,
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
import Core.Demand.AbstractValue
import Core.Demand.StaticContext
import Core.Demand.FixpointMonad
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

data State r e s = State{
  buildc :: BuildContext,
  states :: M.Map ExprContextId ExprContext,
  moduleContexts :: M.Map ModuleName ExprContext,
  maxContextId :: Int,
  childrenIds :: M.Map ExprContextId [ExprContextId],
  specialIds :: M.Map (ExprContextId, ExprContextId) ExprContextId,
  unique :: Int,
  finalResults :: Set r,
  -- Evaluators given an application site / environment of a primitive (what does the application evaluate to)
  primitives :: M.Map Name ((ExprContext,EnvCtx) -> FixDemandR r s e AChange),
  -- Expression relation for an application site / environment of a primitive (where does the i'th parameter flow to)
  eprimitives :: M.Map Name (Int -> (ExprContext,EnvCtx) -> FixDemandR r s e AChange),
  gas :: Int,
  outOfGas :: Bool,
  additionalState :: s
}

demandLog :: String -> FixDemandR r s e ()
demandLog s = do
  env <- getEnv
  when (loggingEnabled env) $ trace s $ return ()

setGas :: Int -> FixDemandR r s e ()
setGas g = do
  st <- getState
  setState st{gas = g, outOfGas = False}

useGas :: Int -> FixDemandR r s e Bool
useGas g = do
  st <- getState
  let newGas = gas st - g
  if newGas < 0 && (gas st /= (-1)) then
    do
      trace (show $ gas st) $ return ()
      setState st{gas = 0, outOfGas=True}
      return True
  else
    do
      setState st{gas = if gas st < 0 then gas st else newGas}
      return False

decGas :: FixDemandR r s e Bool
decGas = useGas 1

withGas :: FixDemandR r s e a -> FixDemandR r s e a
withGas f = do
  allout <- decGas
  if allout then trace "All out of gas" doBottom else f

emptyState :: BuildContext -> Int -> s -> State r e s
emptyState bc g s =
  State bc M.empty M.empty 0 M.empty M.empty 0 S.empty M.empty M.empty g False s

transformState :: (s -> x) -> (Set r -> Set b) -> Int -> State r e s -> State b e x
transformState f final gas (State bc s mc mid cid sid u fr p ep _ _ ad) =
  State bc s mc mid cid sid u (final fr) M.empty M.empty gas False (f ad)

type TypeChecker = (BuildContext -> ModuleName -> IO (Either Errors (BuildContext,Errors)))

emptyEnv :: HasCallStack => Int -> AnalysisKind -> TypeChecker -> Bool -> e -> DEnv e
emptyEnv m kind build log e =
  DEnv m build kind (error "Context used prior to loading") (error "Mod context used prior to loading") "" (-1) "" log e

updateAdditionalState :: (s -> s) -> FixDemandR r s e ()
updateAdditionalState f = do
  st <- getState
  setState st{additionalState = f (additionalState st)}

data AnalysisKind = BasicEnvs | LightweightEnvs | HybridEnvs deriving (Eq, Ord, Show)

data DEnv x = DEnv{
  contextLength :: !Int,
  builder :: BuildContext -> ModuleName -> IO (Either Errors (BuildContext,Errors)),
  analysisKind :: !AnalysisKind,
  currentContext :: ExprContext,
  currentModContext :: ExprContext,
  currentQuery :: !String,
  currentQueryId :: !Int,
  queryIndentation :: !String,
  loggingEnabled :: Bool,
  additionalEnv :: x
}
-- A query type representing the mutually recursive queries we can make that result in an abstract value
data Query =
  CallQ (ExprContext, EnvCtx) |
  ExprQ (ExprContext, EnvCtx) |
  EvalQ (ExprContext, EnvCtx) |
  EvalxQ (ExprContext, EnvCtx, Name, Type) | -- Find Applications for the type
  ExprxQ (ExprContext, EnvCtx, Type) -- Find Handler for the operation's effect type
  deriving (Eq, Ord)

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

------------------------ Navigating the syntax tree ----------------------------------
focusParam :: Int -> ExprContext -> FixDemandR x s e ExprContext
focusParam index = focusChild (index + 1)

focusBody :: ExprContext -> FixDemandR x s e ExprContext
focusBody e = do
  children <- childrenContexts e
  query <- getQueryString
  case find (\x -> case x of
              LamCBody{} -> True
              _ -> False) children of
    Just x -> return x
    Nothing -> error (query ++ "Children looking for body " ++ show children)

enterBod :: ExprContext -> EnvCtx -> ExprContext -> EnvCtx -> FixDemandR x s e (ExprContext, EnvCtx)
enterBod lam lamenv callctx callenv = do
  bd <- focusBody lam
  -- trace (query ++ "APP: Lambda body is " ++ show lamctx) $ return []
  -- In the subevaluation if a binding for the parameter is requested, we should return the parameter in this context, 
  succ <- succAEnv callctx callenv
  let newEnv = EnvCtx succ lamenv
  return (bd, newEnv)

focusFun :: ExprContext -> FixDemandR x s e ExprContext
focusFun = focusChild 0

focusChild :: Int -> ExprContext -> FixDemandR x s e ExprContext
focusChild index e = do
  children <- childrenContexts e
  -- trace ("Focused child of " ++ showSimpleContext e ++ " " ++ show (contextId e) ++ " =>\n  " ++ show children) $ return ()
  query <- getQueryString
  if index < length children then
    -- trace (query ++ "Focused child " ++ show (children !! index) ++ " " ++ show index ++ " " ++ show children) $
      return $ children !! index
    else error (query ++ "Children looking for child at " ++ show index ++ " " ++ show children)


------------------ State and Environment Helpers -----------------------------------

succAEnv :: ExprContext -> EnvCtx -> FixDemandR x s e Ctx
succAEnv newctx p' = do
  length <- contextLength <$> getEnv
  kind <- analysisKind <$> getEnv
  case kind of
    BasicEnvs -> return $ limitm (BCallCtx newctx (envhead p')) length

-- Gets a string representing the current query
getQueryString :: FixDemandR x s e String
getQueryString = do
  env <- getEnv
  return $ queryIndentation env ++ show (contextId $ currentContext env) ++ " " ++ currentQuery env ++ " "

getUnique :: FixDemandR x s e Int
getUnique = do
  st <- getState
  let u = unique st
  setState st{unique = u + 1}
  return u

addResult :: Ord x => x -> FixDemandR x s e ()
addResult x = do
  updateState (\st -> st{finalResults = S.insert x (finalResults st)})

setResults :: Set r -> FixT e1 (State r e2 s) i l d ()
setResults x = do
  updateState (\st -> st{finalResults = x})

--- Wraps a computation with a new environment that represents the query indentation and dependencies for easier following and debugging

newQuery :: Bool -> Query -> (String -> FixDemandR x s e AChange) -> FixDemandR x s e AFixChange
newQuery isRefined q d = do
  unique <- getUnique
  withEnv (\env -> env{currentContext = queryCtx q, currentQueryId = unique, currentQuery = (if isRefined then "qr" else "q") ++ queryKindCaps q ++ "(" ++ show unique ++ ")" ++ ": ", queryIndentation = queryIndentation env ++ " "}) $ do
    query <- getQueryString
    res <- d query
    return $ FA res

--------------------------------------- ExprContext Helpers -------------------------------------

getTopDefCtx :: ExprContext -> Name -> FixDemandR x s e ExprContext
getTopDefCtx ctx name = do
  -- trace ("Getting top def ctx " ++ show name ++ " " ++ show ctx) $ return ()
  children <- childrenContexts ctx
  case find (\dctx -> case dctx of
      DefCNonRec{} | defName (defOfCtx dctx) == name -> True
      DefCRec{} | defName (defOfCtx dctx) == name -> True
      _ -> False
      ) children of
    Just dctx -> do
      -- trace ("Found top def ctx " ++ showSimpleContext dctx) $ return ()
      -- lamctx <- focusChild dctx 0 -- Actually focus the lambda
      return dctx
    Nothing -> error $ "getTopDefCtx: " ++ show ctx ++ " " ++ show name

topBindExpr :: ExprContext -> C.Expr -> PostFixR x s e (Maybe C.Def, Maybe C.External)
topBindExpr ctx var@(C.Var tname _) = do
  mmod <- maybeLoadModuleR mName
  let m = do -- Maybe monad
        mod <- mmod
        core <- modCoreUnopt mod
        let defs = coreProgDefs core
        case find (\d -> defTName d == tname) (flattenDefGroups defs) of
          Just d -> return (Just d, Nothing)
          Nothing -> do
            let externs = coreProgExternals core
            case find (\e -> case e of C.External{} -> externalName e == C.getName tname; _ -> False) externs of
              Just e -> return (Nothing, Just e)
              Nothing -> return (Nothing, Nothing)
  return $ fromMaybe (Nothing, Nothing) m
  where
    mName = newModuleName (nameModule name)
    name = C.getName tname
topBindExpr ctx _ = return (Nothing, Nothing)

getModule :: Name -> FixDemandR x s e Module
getModule name = do
  deps <- buildcModules . buildc <$> getState
  let x = find (\m -> modName m == name) deps
  case x of
    Just mod -> return mod
    _ -> error $ "getModule: " ++ show name

getModuleR :: Name -> PostFixR x s e Module
getModuleR name = do
  deps <- buildcModules . buildc <$> getStateR
  let x = find (\m -> modName m == name) deps
  case x of
    Just mod -> return mod
    _ -> error $ "getModule: " ++ show name

getResults :: PostFixR x s e (Set x)
getResults = do
  st <- getStateR
  return $ finalResults st

addChildrenContexts :: ExprContextId -> [ExprContext] -> FixDemandR x s e ()
addChildrenContexts parentCtx contexts = do
  state <- getState
  let newIds = map contextId contexts
      newChildren = M.insert parentCtx newIds (childrenIds state)
   -- trace ("Adding " ++ show childStates ++ " previously " ++ show (M.lookup parentCtx (childrenIds state))) 
  setState state{childrenIds = newChildren}

newContextId :: FixDemandR x s e ExprContextId
newContextId = do
  state <- getState
  id <- currentContext <$> getEnv
  let newCtxId = maxContextId state + 1
  updateState (\s -> s{maxContextId = newCtxId})
  return $! ExprContextId newCtxId (moduleName (contextId id))

newModContextId :: ModuleName -> FixDemandR x s e ExprContextId
newModContextId mod = do
  state <- getState
  let newCtxId = maxContextId state + 1
  updateState (\s -> s{maxContextId = newCtxId})
  return $! ExprContextId newCtxId mod

addContextId :: (ExprContextId -> ExprContext) -> FixDemandR x s e ExprContext
addContextId f = do
  newId <- newContextId
  -- trace ("Adding context id " ++ show newId) $ return ()
  state <- getState
  let x = f newId
  setState state{states=M.insert newId x (states state)}
  return x

addSpecialId :: (ExprContextId, ExprContextId) -> (ExprContextId -> ExprContext) -> FixDemandR x s e ExprContext
addSpecialId ids f = do
  state <- getState
  case M.lookup ids $ specialIds state of
    Just id ->
      -- trace ("Special Id already exists " ++ show ids ++ " " ++ show id) $ do
      return $! states state M.! id
    Nothing -> do
      newId <- newContextId
      -- trace ("Adding special id " ++ show ids ++ " " ++ show newId) $ return ()
      let x = f newId
      state <- getState -- Refetch state because newContextId mutates it
      setState state{states=M.insert newId x (states state), specialIds=M.insert ids newId (specialIds state)}
      return x

childrenOfExpr :: ExprContext -> Expr -> FixDemandR x s e [ExprContext]
childrenOfExpr ctx expr =
  case expr of
    Lam names eff e -> addContextId (\newId -> LamCBody newId ctx names e) >>= single
    App f vs rng -> do
      x <- addContextId (\newId -> AppCLambda newId ctx f )
      rest <- zipWithM (\i x -> addContextId (\newId -> AppCParam newId ctx i x)) [0..] vs
      return $! x : rest
    Let defs result -> do
      let defNames = map defTName (concatMap defsOf defs)
      defs <- mapM defsFor defs
      -- trace ("Let " ++ show (map contextId defs)) $ return ()
      result <- addContextId (\newId -> LetCBody newId ctx defNames result)
      -- trace ("Let " ++ show (contextId result) ++ show result) $ return ()
      return $! result:concat defs
      where
        defsFor dg@(C.DefNonRec d) = do
          res <- addContextId (\newId -> LetCDefNonRec newId ctx [(defTName d)] dg)
          return [res]
        defsFor dg@(C.DefRec ds) = do
          mapM (\(i, _) -> addContextId (\newId -> LetCDefRec newId ctx (map defTName ds) i dg)) (zip [0..] ds)
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

initialModuleContexts :: ExprContext -> FixDemandR x s e [ExprContext]
initialModuleContexts modCtx = do
  withModuleCtx modCtx $
    case modCtx of
      ModuleC id@(ExprContextId _ n1) mod n2 -> do
        -- trace ("Getting children of module " ++ show (contextId modCtx)) $ return ()
        res <- mapM (childrenOfDef modCtx) (coreProgDefs $ fromJust $ modCoreUnopt mod)
        let newCtxs = concat res
        return newCtxs

withModuleCtx :: ExprContext -> FixDemandR x s e a -> FixDemandR x s e a
withModuleCtx ctx f = do
  case ctx of
    ModuleC (ExprContextId _ n1) _ n2 | n1 /= n2 ->
      error ("Module Context Mismatch " ++ show n1 ++ " " ++ show n2)
    ModuleC _ _ name -> do
      loadModule name
      return ()
    _ -> return ()
  withEnv (\env -> env{currentContext = ctx, currentModContext = case ctx of {ModuleC{} -> ctx; _ -> currentModContext env}}) f

childrenContexts :: ExprContext -> FixDemandR x s e [ExprContext]
childrenContexts ctx = do
  withModuleCtx ctx $ do
    let parentCtxId = contextId ctx
    children <- childrenIds <$> getState
    let childIds = M.lookup parentCtxId children
    case childIds of
      Nothing -> do
          -- trace ("No children for " ++ show ctx ++ " " ++ show (contextId ctx)) $ return ()
          newCtxs <- case ctx of
                DefCRec{} -> childrenOfExpr ctx (exprOfCtx ctx)
                DefCNonRec{} -> childrenOfExpr ctx (exprOfCtx ctx)
                LamCBody _ _ names body -> childrenOfExpr ctx body
                AppCLambda _ _ f -> childrenOfExpr ctx f
                AppCParam _ _ _ param -> childrenOfExpr ctx param
                LetCDefRec{} -> childrenOfExpr ctx (exprOfCtx ctx)
                LetCDefNonRec{} -> childrenOfExpr ctx (exprOfCtx ctx)
                LetCBody _ _ _ e -> childrenOfExpr ctx e
                CaseCMatch _ _ e -> childrenOfExpr ctx e
                CaseCBranch _ _ _ _ b -> do
                  x <- mapM (childrenOfExpr ctx . guardExpr) $ branchGuards b -- TODO Better context for branch guards
                  return $! concat x
                ExprCBasic{} -> return []
                ExprCTerm{} -> return []
                ModuleC{} -> do
                  demandLog ("initial contexts for module " ++ show (contextId ctx))
                  initialModuleContexts ctx
          addChildrenContexts parentCtxId newCtxs
          -- trace ("Got children for " ++ showCtxExpr ctx ++ " " ++ show newCtxs ++ " " ++ show (map contextId newCtxs)) $ return newCtxs
          return newCtxs
      Just childIds -> do
        -- trace ("Got children for " ++ showCtxExpr ctx ++ " " ++ show childIds) $ return ()
        states <- states <$> getState
        return $! map (states M.!) childIds

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

maybeLoadModuleR :: ModuleName -> PostFixR x s e (Maybe Module)
maybeLoadModuleR mn = do
  state <- getStateR
  case M.lookup mn (moduleContexts state) of
    Just (ModuleC _ m _) -> return $ Just m
    _ -> do
      bc <- buildc <$> getStateR
      env <- getEnvR
      let build = builder env
      let deps = buildcModules bc
      let x = find (\m -> modName m == mn) deps
      case x of
        Just mod@Module{modStatus=LoadedSource, modCoreUnopt=Just _} -> do
          trace ("Module already loaded " ++ show mn) $ return ()
          return $ Just mod
        _ -> do
          buildc' <- liftIO (build bc mn)
          case buildc' of
            Left err -> do
              trace ("Error loading module " ++ show mn ++ " " ++ show err) $ return ()
              return Nothing
            Right (bc', e) -> do
              trace ("Loaded module " ++ show mn) $ return ()
              return $ buildcLookupModule mn bc'

maybeLoadModule :: HasCallStack => ModuleName -> FixDemandR x s e (Maybe Module)
maybeLoadModule mn = do
  state <- getState
  case M.lookup mn (moduleContexts state) of
    Just (ModuleC _ m _) -> return $ Just m
    _ -> do
      bc <- buildc <$> getState
      env <- getEnv
      let deps = buildcModules bc
      let x = find (\m -> modName m == mn) deps
      ctxId <- newModContextId mn
      case x of
        Just mod@Module{modStatus=LoadedSource, modCoreUnopt=Just _} -> do
          -- trace ("Module already loaded " ++ show mn) $ return ()
          let modCtx = ModuleC ctxId mod mn
          updateState (\state ->
            state{
              moduleContexts = M.insert mn modCtx (moduleContexts state)
            })
          return $ Just mod
        _ -> do
          let build = builder env
          buildc' <- liftIO $ build bc mn
          case buildc' of
            Left err -> do
              trace ("Error loading module " ++ show mn ++ " " ++ show err) $ return ()
              return Nothing
            Right (bc', e) -> do
              -- trace ("Loaded module " ++ show mn) $ return ()
              let Just mod' = buildcLookupModule mn bc'
              let modCtx = ModuleC ctxId mod' mn
              updateState (\state ->
                state{
                  buildc = bc',
                  moduleContexts = M.insert mn (ModuleC ctxId mod' mn) (moduleContexts state)
                })
              return $ Just mod'

loadModule :: HasCallStack => ModuleName -> FixDemandR x s e (Module, ExprContext)
loadModule mn = do
  res <- maybeLoadModule mn
  case res of
    Just m -> do
      st <- getState
      return (m, moduleContexts st M.! mn)
    Nothing -> error ("Module " ++ show mn ++ " not found")