
module Core.FlowAnalysis.Monad where

import Control.Monad.State (gets, MonadState (..))
import Control.Monad.Reader
import Data.Set (Set)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Maybe (fromMaybe, fromJust, maybeToList)
import Data.List (find, intercalate)
import Control.Monad (zipWithM, when)
import Core.FlowAnalysis.AbstractValue
import Core.FlowAnalysis.StaticContext
import Core.FlowAnalysis.FixpointMonad
import Compile.Options
import Compile.BuildMonad hiding (liftIO)
import Compile.Module
import Common.Name
import Core.Core
import Common.Failure (assertion, HasCallStack)
import qualified Core.Core as C
import Compile.BuildMonad hiding (liftIO)
import Common.Error (Errors)
import Debug.Trace (trace)

type FixAR r s e i o c a = FixT (AnalysisEnv e) (BasicState r s) i o c a
type FixA r s e i o c = FixAR r s (AnalysisEnv e) i o c (o c)
type PostFixAR r s e i o c a = FixIn (AnalysisEnv e) (BasicState r s) i o c a
type PostFixA r s e i o c = PostFixAR r s (AnalysisEnv e) i o c (o c)

data BasicState r s = BasicState{
  buildc :: BuildContext,
  states :: M.Map ExprContextId ExprContext,
  moduleContexts :: M.Map ModuleName ExprContext,
  maxContextId :: Int,
  childrenIds :: M.Map ExprContextId [ExprContextId],
  specialIds :: M.Map (ExprContextId, ExprContextId) ExprContextId,
  unique :: Int,
  finalResults :: Set r,
  additionalState :: s
}
data AnalysisEnv x = AnalysisEnv{
  contextLength :: !Int,
  builder :: BuildContext -> ModuleName -> IO (Either Errors (BuildContext,Errors)),
  currentContext :: ExprContext,
  currentModContext :: ExprContext,
  loggingEnabled :: Bool,
  additionalEnv :: x
}

analysisLog :: String -> FixAR x s e i o c ()
analysisLog s = do
  env <- getEnv
  when (loggingEnabled env) $ trace s $ return ()

emptyBasicState :: BuildContext -> s -> BasicState r s
emptyBasicState bc s =
  BasicState bc M.empty M.empty 0 M.empty M.empty 0 S.empty s

transformBasicState :: (s -> x) -> (Set r -> Set b) -> BasicState r s -> BasicState b x
transformBasicState f final (BasicState bc s mc mid cid sid u fr ad) =
  BasicState bc s mc mid cid sid u (final fr) (f ad)

type TypeChecker = (BuildContext -> ModuleName -> IO (Either Errors (BuildContext,Errors)))

emptyBasicEnv :: HasCallStack => Int -> TypeChecker -> Bool -> e -> AnalysisEnv e
emptyBasicEnv m build log e =
  AnalysisEnv m build (error "Context used prior to loading") (error "Mod context used prior to loading") log e

------------------------ Navigating the syntax tree ----------------------------------
focusParam :: Int -> ExprContext -> FixAR x s e i o c ExprContext
focusParam index = focusChild (index + 1)

focusBody :: ExprContext -> FixAR x s e i o c ExprContext
focusBody e = do
  children <- childrenContexts e
  -- query <- getQueryString
  case find (\x -> case x of
              LamCBody{} -> True
              _ -> False) children of
    Just x -> return x
    Nothing -> error ("Children looking for body " ++ show children)

focusFun :: ExprContext -> FixAR x s e i o c ExprContext
focusFun = focusChild 0

focusChild :: Int -> ExprContext -> FixAR x s e i o c ExprContext
focusChild index e = do
  children <- childrenContexts e
  -- trace ("Focused child of " ++ showSimpleContext e ++ " " ++ show (contextId e) ++ " =>\n  " ++ show children) $ return ()
  -- query <- getQueryString
  if index < length children then
    -- trace (query ++ "Focused child " ++ show (children !! index) ++ " " ++ show index ++ " " ++ show children) $
      return $ children !! index
    else error ("Children looking for child at " ++ show index ++ " " ++ show children)


------------------ State Helpers -----------------------------------

getUnique :: FixAR x s e i o c Int
getUnique = do
  st <- getState
  let u = unique st
  setState st{unique = u + 1}
  return u

addResult :: Ord x => x -> FixAR x s e i o c ()
addResult x = do
  updateState (\st -> st{finalResults = S.insert x (finalResults st)})

setResults :: Set r -> FixT e1 (BasicState r s) i l d ()
setResults x = do
  updateState (\st -> st{finalResults = x})


--------------------------------------- ExprContext Helpers -------------------------------------

getTopDefCtx :: ExprContext -> Name -> FixAR x s e i o c ExprContext
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

topBindExpr :: ExprContext -> C.Expr -> PostFixAR x s e i o c (Maybe C.Def, Maybe C.External)
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

getModule :: Name -> FixAR x s e i o c Module
getModule name = do
  deps <- buildcModules . buildc <$> getState
  let x = find (\m -> modName m == name) deps
  case x of
    Just mod -> return mod
    _ -> error $ "getModule: " ++ show name

getModuleR :: Name -> PostFixAR x s e i o c Module
getModuleR name = do
  deps <- buildcModules . buildc <$> getStateR
  let x = find (\m -> modName m == name) deps
  case x of
    Just mod -> return mod
    _ -> error $ "getModule: " ++ show name

getResults :: PostFixAR x s e i o c (Set x)
getResults = do
  st <- getStateR
  return $ finalResults st

addChildrenContexts :: ExprContextId -> [ExprContext] -> FixAR x s e i o c ()
addChildrenContexts parentCtx contexts = do
  state <- getState
  let newIds = map contextId contexts
      newChildren = M.insert parentCtx newIds (childrenIds state)
   -- trace ("Adding " ++ show childStates ++ " previously " ++ show (M.lookup parentCtx (childrenIds state))) 
  setState state{childrenIds = newChildren}

newContextId :: FixAR x s e i o c ExprContextId
newContextId = do
  state <- getState
  id <- currentContext <$> getEnv
  let newCtxId = maxContextId state + 1
  updateState (\s -> s{maxContextId = newCtxId})
  return $! ExprContextId newCtxId (moduleName (contextId id))

newModContextId :: ModuleName -> FixAR x s e i o c ExprContextId
newModContextId mod = do
  state <- getState
  let newCtxId = maxContextId state + 1
  updateState (\s -> s{maxContextId = newCtxId})
  return $! ExprContextId newCtxId mod

addContextId :: (ExprContextId -> ExprContext) -> FixAR x s e i o c ExprContext
addContextId f = do
  newId <- newContextId
  -- trace ("Adding context id " ++ show newId) $ return ()
  state <- getState
  let x = f newId
  setState state{states=M.insert newId x (states state)}
  return x

addSpecialId :: (ExprContextId, ExprContextId) -> (ExprContextId -> ExprContext) -> FixAR x s e i o c ExprContext
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

childrenOfExpr :: ExprContext -> Expr -> FixAR x s e i o c [ExprContext]
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

childrenOfDef :: ExprContext -> C.DefGroup -> FixAR x s e i o c [ExprContext]
childrenOfDef ctx def =
  case def of
    C.DefNonRec d -> addContextId (\newId -> DefCNonRec newId ctx [defTName d] def) >>= (\x -> return [x])
    C.DefRec ds -> zipWithM (\i d -> addContextId (\newId -> DefCRec newId ctx (map defTName ds) i def)) [0..] ds

initialModuleContexts :: ExprContext -> FixAR x s e i o c [ExprContext]
initialModuleContexts modCtx = do
  withModuleCtx modCtx $
    case modCtx of
      ModuleC id@(ExprContextId _ n1) mod n2 -> do
        -- trace ("Getting children of module " ++ show (contextId modCtx)) $ return ()
        res <- mapM (childrenOfDef modCtx) (coreProgDefs $ fromJust $ modCoreUnopt mod)
        let newCtxs = concat res
        return newCtxs

withModuleCtx :: ExprContext -> FixAR x s e i o c a -> FixAR x s e i o c a
withModuleCtx ctx f = do
  case ctx of
    ModuleC (ExprContextId _ n1) _ n2 | n1 /= n2 ->
      error ("Module Context Mismatch " ++ show n1 ++ " " ++ show n2)
    ModuleC _ _ name -> do
      loadModule name
      return ()
    _ -> return ()
  withEnv (\env -> env{currentContext = ctx, currentModContext = case ctx of {ModuleC{} -> ctx; _ -> currentModContext env}}) f

childrenContexts :: ExprContext -> FixAR x s e i o c [ExprContext]
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
                  analysisLog ("initial contexts for module " ++ show (contextId ctx))
                  initialModuleContexts ctx
          addChildrenContexts parentCtxId newCtxs
          -- trace ("Got children for " ++ showCtxExpr ctx ++ " " ++ show newCtxs ++ " " ++ show (map contextId newCtxs)) $ return newCtxs
          return newCtxs
      Just childIds -> do
        -- trace ("Got children for " ++ showCtxExpr ctx ++ " " ++ show childIds) $ return ()
        states <- states <$> getState
        return $! map (states M.!) childIds

visitChildrenCtxs :: ([a] -> a) -> ExprContext -> FixAR x s e i o c a -> FixAR x s e i o c a
visitChildrenCtxs combine ctx analyze = do
  children <- childrenContexts ctx
  -- trace ("Got children of ctx " ++ show ctx ++ " " ++ show children) $ return ()
  res <- mapM (\child -> withEnv (\e -> e{currentContext = child}) analyze) children
  return $! combine res

visitEachChild :: (Show a, Show c, Show (o c), Lattice o c, Ord i) => ExprContext -> FixAR x s e i o c a -> FixAR x s e i o c a
visitEachChild ctx analyze = do
  children <- childrenContexts ctx
  -- trace ("Got children of ctx " ++ show ctx ++ " " ++ show children) $ return ()
  each $ map (\child -> withEnv (\e -> e{currentContext = child}) analyze) children

maybeLoadModuleR :: ModuleName -> PostFixAR x s e i o c (Maybe Module)
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

maybeLoadModule :: HasCallStack => ModuleName -> FixAR x s e i o c (Maybe Module)
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

loadModule :: HasCallStack => ModuleName -> FixAR x s e i o c (Module, ExprContext)
loadModule mn = do
  res <- maybeLoadModule mn
  case res of
    Just m -> do
      st <- getState
      return (m, moduleContexts st M.! mn)
    Nothing -> error ("Module " ++ show mn ++ " not found")