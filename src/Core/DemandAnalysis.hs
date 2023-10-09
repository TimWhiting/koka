-----------------------------------------------------------------------------
-- Copyright 2012-2023, Microsoft Research, Daan Leijen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{-
    Check if a constructor context is well formed, and create a context path
-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE InstanceSigs #-}

module Core.DemandAnalysis(
                          AbstractLattice(..),
                          ExprContext(..),
                          runEvalQueryFromRange,
                        ) where


import Control.Monad
import Common.Name
import Data.Set as S hiding (findIndex, filter, map)
import Core.Core (Expr (..), CorePhase, liftCorePhaseUniq, DefGroups, Def (..), DefGroup (..), liftCorePhaseRes, Branch (..), Guard(..), Pattern(..), TName (..), defsTNames, defGroupTNames, mapDefGroup, Core (..), VarInfo (..), liftCorePhase)
import Data.Map hiding (findIndex, filter, map)
import qualified ListT as L
-- import Debug.Trace (trace)
import Core.Pretty
import Type.Type (isTypeInt, isTypeInt32, Type (..), expandSyn, TypeCon (..), ConInfo (..))
import Data.Sequence (mapWithIndex, fromList)
import qualified Data.Sequence as Seq
import Data.Maybe (mapMaybe, isJust, fromJust, maybeToList, fromMaybe)
import Data.List (find, findIndex, elemIndex, union)
import Debug.Trace
import Compiler.Module (Loaded (..), Module (..))
import Lib.PPrint (Pretty(..))
import Type.Pretty (ppType, defaultEnv)
import Kind.Kind (Kind(..))
import Control.Monad.Trans
import ListT (ListT)
import Common.Range (Range, rangesOverlap, showFullRange)
import Syntax.RangeMap (RangeInfo)
import Common.NamePrim (nameOpen, nameEffectOpen)
import Core.CoreVar

data AbstractLattice =
  AbBottom | AbTop

-- trace:: String -> a -> a
-- trace x y = y

-- Uniquely identifies expressions despite naming
data ExprContext =
  -- Current expression context
  ModuleC ExprContextId Module Name -- Module context
  | DefCRec ExprContextId ExprContext Int Def -- A recursive definition context, working on the index'th definition
  | DefCNonRec ExprContextId ExprContext Def -- In a non recursive definition context, working on Def
  | LamCBody ExprContextId ExprContext [TName] Expr -- Inside a lambda body expression
  | AppCLambda ExprContextId ExprContext Expr -- Application context inside function context
  | AppCParam ExprContextId ExprContext Int Expr -- Application context inside param context
  | LetCDef ExprContextId ExprContext Int DefGroup -- In a let definition context working on a particular defgroup
  | LetCBody ExprContextId ExprContext Expr -- In a let body expression
  | CaseCMatch ExprContextId ExprContext Expr -- In a case match context working on the match expression (assumes only one)
  | CaseCBranch ExprContextId ExprContext Int Branch -- Which branch currently inspecting, as well as the Case context
  | ExprCBasic ExprContextId ExprContext Expr -- A basic expression context that has no sub expressions
  | ExprCTerm String -- Since analysis can fail or terminate early, keep track of the query that failed

isApp :: ExprContext -> AEnv Bool
isApp e = do
  children <- childrenContexts e
  query <- getQueryString
  return $ trace (query ++ "check App: is context " ++ show e ++ " with children ") $
   case children of
      AppCLambda{}:_ -> True
      ExprCBasic _ _ Var{}:AppCParam{}:_ -> True
      ExprCBasic _ _ Var{}:_ -> True -- Zero argument function?
      _ -> False

paramIndex e =
  case e of
    AppCParam _ _ i _ -> i

focusParam :: Maybe Int -> ExprContext -> AEnv (Maybe ExprContext)
focusParam index e = do
  children <- childrenContexts e
  query <- getQueryString
  return $ case index of
    Just x | x < length children -> Just $ children !! x
    _ -> trace (query ++ "Children looking for param " ++ show children ++ " in " ++ show e ++ " index " ++ show index) Nothing


focusBody :: ExprContext -> AEnv (Maybe ExprContext)
focusBody e = do
  children <- childrenContexts e
  query <- getQueryString
  return $ case find (\x -> case x of
              LamCBody{} -> True
              _ -> False) children of
    Just x -> Just x
    Nothing -> trace (query ++ "Children looking for body " ++ show children) Nothing

focusFun :: ExprContext -> AEnv (Maybe ExprContext)
focusFun e = do
  children <- childrenContexts e
  query <- getQueryString
  return $ case find (\x -> case x of
                AppCLambda{} -> True
                ExprCBasic _ _ Var{} -> True
                _ -> False) children of
    Just x -> Just x
    Nothing -> trace (query ++ "Children looking for lambda " ++ show children) Nothing

lamVar :: ExprContext -> Expr
lamVar ctx =
  case ctx of
    LamCBody _ _ names _ -> Var (head names) InfoNone
    _ -> trace "DemandAnalysis.lamVar: not a lambda" error "Not a lambda"

lamVarDef :: Def -> Expr
lamVarDef def = Var (TName (defName def) (defType def) Nothing) InfoNone

showExpr :: Expr -> String
showExpr e = show $ prettyExpr defaultEnv e

showDg d = show $ prettyDefGroup defaultEnv d

showDef d = show $ prettyDef defaultEnv d

instance Show ExprContext where
  show e =
    case e of
      ModuleC _ _ nm -> "Module " ++ show nm
      DefCRec _ _ i df -> "DefRec " ++ showDef df
      DefCNonRec _ _ df -> "DefNonRec " ++ showDef df
      LamCBody _ _ tn e -> "LamBody " ++ show tn ++ " " ++ showExpr e
      AppCLambda _ _ f -> "AppLambda " ++ showExpr f
      AppCParam _ _ i p -> "AppParam " ++ show i ++ " " ++ showExpr p
      LetCDef _ _ i dg -> "LetDef " ++ showDg dg
      LetCBody _ _ e -> "LetBody " ++ showExpr e
      CaseCMatch _ _ e -> "CaseMatch " ++ showExpr e
      CaseCBranch _ _ i b -> "CaseBranch " ++ show i ++ " " ++ show b
      ExprCBasic _ _ e -> "ExprBasic " ++ showExpr e
      ExprCTerm s -> "Query: " ++ s

exprOfCtx :: ExprContext -> Expr
exprOfCtx ctx =
  case ctx of
    ModuleC {} -> error "ModuleC is a multi Expression Context"
    DefCRec _ _ _ d -> defExpr d
    DefCNonRec _ _ d -> defExpr d
    LamCBody _ _ _ e -> e
    AppCLambda _ _ f -> f
    AppCParam _ _ _ param -> param
    LetCDef _ _ _ dg -> error "LetCDef has no single expr"
    LetCBody _ _ e -> e
    CaseCMatch _ _ e -> e
    CaseCBranch _ _ _ b -> guardExpr (head (branchGuards b))
    ExprCBasic _ _ e -> e
    ExprCTerm{} -> error "Query should never be queried for expression"

maybeExprOfCtx :: ExprContext -> Maybe Expr
maybeExprOfCtx ctx =
  case ctx of
    ModuleC {} -> Nothing
    DefCRec _ _ _ d -> Just $ defExpr d
    DefCNonRec _ _ d -> Just $ defExpr d
    LamCBody _ _ _ e -> Just e
    AppCLambda _ _ f -> Just f
    AppCParam _ _ _ param -> Just param
    LetCDef _ _ _ dg -> Nothing
    LetCBody _ _ e -> Just e
    CaseCMatch _ _ e -> Just e
    CaseCBranch _ _ _ b -> Just $ guardExpr (head (branchGuards b))
    ExprCBasic _ _ e -> Just e
    ExprCTerm{} -> error "Query should never be queried for expression"

contextId :: ExprContext -> ExprContextId
contextId ctx =
  case ctx of
    ModuleC c _ _ -> c
    DefCRec c _ _ _ -> c
    DefCNonRec c _ _ -> c
    LamCBody c _ _ _ -> c
    AppCLambda c _ _ -> c
    AppCParam c _ _ _ -> c
    LetCDef c _ _ _ -> c
    LetCBody c _ _ -> c
    CaseCMatch c _ _ -> c
    CaseCBranch c _ _ _ -> c
    ExprCBasic c _ _ -> c
    ExprCTerm{} -> error "Query should never be queried for context id"

contextOf :: ExprContext -> Maybe ExprContext
contextOf ctx =
  case ctx of
    ModuleC _ _ _ -> Nothing
    DefCRec _ c _ _ -> Just c
    DefCNonRec _ c _ -> Just c
    LamCBody _ c _ _ -> Just c
    AppCLambda _ c _ -> Just c
    AppCParam _ c _ _ -> Just c
    LetCDef _ c _ _ -> Just c
    LetCBody _ c _ -> Just c
    CaseCMatch _ c _ -> Just c
    CaseCBranch _ c _ _ -> Just c
    ExprCBasic _ c _ -> Just c
    ExprCTerm{} -> error "Query should never be queried for context"

branchContainsBinding :: Branch -> TName -> Bool
branchContainsBinding (Branch pat guards) name =
  name `elem` bv pat

data ExprContextId = ExprContextId{
  exprId:: Int,
  moduleName:: Name,
  topDef:: Name,
  topDefType:: Type
} deriving (Ord, Eq, Show)

instance Eq ExprContext where
  ctx1 == ctx2 = contextId ctx1 == contextId ctx2

instance Ord ExprContext where
  compare ctx1 ctx2 = compare (contextId ctx1) (contextId ctx2)

instance Ord Type where
  compare tp1 tp2 = compare (show $ ppType defaultEnv tp1) (show $ ppType defaultEnv tp2)

instance Eq Def where
  def1 == def2 = defName def1 == defName def2 && defType def1 == defType def2

type ExpressionSet = Set ExprContextId

newtype AEnv a = AEnv (Env -> State -> Result a)
data State = State{states :: Map ExprContextId ExprContext, childrenIds :: Map ExprContextId (Set ExprContextId), memoCache :: Map String (Map ExprContextId (Set ExprContext)), unique :: Int}
data Result a = Ok a State

data Env = Env{
  loaded :: Loaded,
  currentContext :: !ExprContext,
  currentContextId :: ExprContextId,
  currentQuery:: String,
  queryIndentation:: String
}

instance Functor AEnv where
  fmap f (AEnv c)  = AEnv (\env st -> case c env st of
                                        Ok x st' -> Ok (f x) st')
instance Applicative AEnv where
  pure x = AEnv (\env st -> Ok x st)
  (<*>)  = ap

instance Monad AEnv where
  -- return = pure
  (AEnv c) >>= f = AEnv (\env st -> case c env st of
                                      Ok x st' -> case f x of
                                                    AEnv d -> d env st')

instance MonadFail AEnv where
  fail _ = error "fail"

withEnv :: (Env -> Env) -> AEnv a -> AEnv a
withEnv f (AEnv c)
  = AEnv (c . f)

getEnv :: AEnv Env
getEnv = AEnv Ok

getState :: AEnv State
getState = AEnv (\env st -> Ok st st)

setState :: State -> AEnv ()
setState st = AEnv (\env _ -> Ok () st)

getQueryString :: AEnv String
getQueryString = do
  env <- getEnv
  return $ queryIndentation env ++ currentQuery env

getUnique :: AEnv Int
getUnique = do
  st <- getState
  let u = unique st
  setState st{unique = u + 1}
  return u

withQuery :: String -> AEnv a -> AEnv a
withQuery q = withEnv (\env -> env{currentQuery = q, queryIndentation = queryIndentation env ++ " "})

updateState :: (State -> State) -> AEnv ()
updateState update = do
  st <- getState
  setState $ update st

runEvalQueryFromRange :: Loaded -> (Range, RangeInfo) -> Module -> [ExprContext]
runEvalQueryFromRange loaded rng mod =
  runQueryAtRange loaded rng mod $ \exprctxs ->
    case exprctxs of
      exprctx:rst -> fixedEval exprctx
      _ -> return []

runQueryAtRange :: Loaded -> (Range, RangeInfo) -> Module -> ([ExprContext] -> AEnv a) -> a
runQueryAtRange loaded (r, ri) mod query =
  let cid = ExprContextId (-1) (modName mod) (newName "module") moduleDummyType
      modCtx = ModuleC cid mod (modName mod)
      focalContext = analyzeCtx (\a l -> a ++ concat l) (const $ findContext r ri) modCtx
      result = case focalContext >>= query of
        AEnv f -> f (Env loaded modCtx cid "" "") (State Data.Map.empty Data.Map.empty (Data.Map.fromList [("eval", Data.Map.empty), ("call", Data.Map.empty), ("expr", Data.Map.empty) ]) 0)
  in case result of
    Ok a st -> a

findContext :: Range -> RangeInfo -> AEnv [ExprContext]
findContext r ri = do
  ctx <- currentContext <$> getEnv
  case ctx of
    ExprCBasic _ _ (Var (TName _ _ (Just rng)) _) | r `rangesOverlap` rng -> trace ("found overlapping range " ++ showFullRange rng ++ " " ++ show ctx) $ return [ctx]
    ExprCBasic _ _ (Var (TName _ _ (Just rng)) _) -> trace ("var range doesn't overlap "++ show ctx ++ " " ++ showFullRange rng) $
      return []
    _ -> return []

analyzeCtx :: (a -> [a] -> a) -> (ExprContext -> AEnv a) -> ExprContext  -> AEnv a
analyzeCtx combine analyze ctx = do
  id <- currentContextId <$> getEnv
  -- trace ("Analyzing ctx " ++ show ctx ++ " with id " ++ show (exprId id)) $ return ()
  res <- analyze ctx
  visitChildrenCtxs (combine res) ctx $ do
    childCtx <- currentContext <$> getEnv
    analyzeCtx combine analyze childCtx

moduleDummyType :: Type
moduleDummyType = TCon $ TypeCon (newName "dummy") (KCon (newName "dummy"))

bind :: ExprContext -> Expr -> Maybe (ExprContext, Maybe Int)
bind ctx var@(Var tname vInfo) =
  case ctx of
    ModuleC _ mod _ -> if lookupDefGroups (coreProgDefs $ modCoreNoOpt mod) tname then Just (ctx, Nothing) else trace ("External variable binding " ++ show tname ++ ": " ++ show vInfo) Nothing
    DefCRec _ ctx i d -> if lookupDef d tname then Just (ctx, Just i) else bind ctx var -- TODO Consider other definitions in the recursive defs
    DefCNonRec _ ctx d -> if lookupDef d tname then Just (ctx, Nothing) else bind ctx var
    LamCBody _ ctx names _  -> case elemIndex tname names of
      Just x ->  Just (ctx, Just $ x + 1) -- function is first index in contexts when we lookup the parameter
      _ -> bind ctx var
    AppCLambda _ ctx _ -> bind ctx var
    AppCParam _ ctx _ _ -> bind ctx var
    LetCDef _ ctx i defg -> if lookupDefGroup defg tname then Just (ctx, Just i) else bind ctx var
    LetCBody _ ctx _ -> bind ctx var
    CaseCMatch _ ctx _ -> bind ctx var
    CaseCBranch _ ctx _ b -> if branchContainsBinding b tname then Just (ctx, Nothing) else bind ctx var
    ExprCBasic _ ctx _ -> bind ctx var
    ExprCTerm{} -> Nothing

findUsage :: Expr -> ExprContext -> AEnv (Set ExprContext)
findUsage  expr@Var{varName=tname@TName{getName = name}} ctx =
  let nameEq = (== name)
      empty = return S.empty
      childrenUsages =
        visitChildrenCtxs S.unions ctx $ do
          childCtx <- currentContext <$> getEnv
          -- trace ("Looking for usages of " ++ show name ++ " in " ++ show ctx) $ return empty
          findUsage expr childCtx in
  case ctx of -- shadowing
    DefCRec _ _ _ d -> if nameEq $ defName d then empty else childrenUsages -- TODO: Consider index
    DefCNonRec _ _ d -> if nameEq $ defName d then empty else childrenUsages
    LamCBody _ _ names _ -> if any (nameEq . getName) names then empty else childrenUsages
    LetCDef _ _ _ d -> if any (nameEq . defName) (defsOf d) then empty else childrenUsages
    CaseCBranch _ _ _ b -> if branchContainsBinding b tname then empty else childrenUsages
    ExprCBasic id _ Var{varName=TName{getName=name2}} ->
      if nameEq name2 then do
        query <- getQueryString
        return $ trace (query ++ "Found usage in " ++ show ctx ) $ S.singleton ctx
      else
        -- trace ("Not found usage in " ++ show ctx ++ " had name " ++ show name2 ++ " expected " ++ show name) $ empty
        empty
    _ -> childrenUsages

findUsage2 :: String -> Expr -> ExprContext -> AEnv [ExprContext]
findUsage2 query e ctx = do
  usage <- withQuery query $ findUsage e ctx
  return $ -- trace ("Looking for usages of " ++ show e ++ " in " ++ show ctx ++ " got " ++ show usage) 
    S.toList usage

doAEnv :: String -> AEnv [a] -> ListT AEnv a
doAEnv query f = do
  xs <- liftWithQuery query f
  L.fromFoldable xs

doAEnvMaybe :: String -> AEnv (Maybe a) -> ListT AEnv a
doAEnvMaybe query f = do
  xs <- liftWithQuery query f
  L.fromFoldable xs

liftWithQuery :: MonadTrans t => String -> AEnv a -> t AEnv a
liftWithQuery query f = lift $ withQuery query f

queryId :: AEnv String
queryId = do
  unique <- getUnique
  return $ "Q " ++ show unique ++ ": "

wrapMemo :: String -> ExprContext -> ListT AEnv ExprContext -> ListT AEnv ExprContext
wrapMemo name ctx f = do
  state <- lift getState
  let cache = (Data.Map.!) (memoCache state) name
  case Data.Map.lookup (contextId ctx) cache of
    Just x -> L.fromFoldable x
    _ -> do
      res <- f
      state <- lift getState
      let cache = (Data.Map.!) (memoCache state) name
      let newCache = Data.Map.insertWith S.union (contextId ctx) (S.singleton res) cache
      lift $ setState state{memoCache = Data.Map.insert name newCache (memoCache state)}
      return res

doEval :: (ExprContext -> ListT AEnv ExprContext) -> (ExprContext -> ListT AEnv ExprContext) -> (ExprContext -> ListT AEnv ExprContext) -> ExprContext -> ListT AEnv ExprContext
doEval eval expr call ctx = do
  query <- lift queryId
  trace (query ++ "Eval " ++ show ctx) $
    wrapMemo "eval" ctx $
    case ctx of
      LamCBody{} -> return ctx
      AppCLambda _ (ExprCBasic _ _ (Var n i)) _ | getName n == nameEffectOpen -> do
        trace (query ++ "Open ") $ return []
        bd <- doAEnvMaybe query (focusParam (Just 1) ctx) 
        eval bd
      ExprCBasic _ _ v@(Var _ _) -> do
        trace (query ++ "Eval var " ++ show ctx) $ return []
        case bind ctx v of
          Just (lambodyctx, index) -> do
            appctx <- trace (query ++ "Found binding for " ++ show v ++ " " ++ show lambodyctx) $ call lambodyctx
            param <- doAEnvMaybe query $ focusParam index appctx
            eval param
          Nothing -> return ctx
      AppCParam{} -> return ctx
      ExprCTerm{} -> return ctx
      _ -> do
        app <- liftWithQuery query $ isApp ctx
        if app then do
          trace (query ++ "Eval app " ++ show ctx) $ return []
          fn <- doAEnvMaybe query $ focusFun ctx
          case fn of
            (ExprCBasic _ _ (Var n i)) | getName n == nameEffectOpen -> do
              trace (query ++ "Is open") $ return []
              arg <- doAEnvMaybe query $ focusParam (Just 1) (fromJust $ contextOf ctx)
              eval arg
            _ -> do
              trace (query ++ "Is app not open") $ return []
              lamctx <- eval fn
              bd <- doAEnvMaybe query $ focusBody lamctx
              eval bd
        else do
          trace (query ++ "unhandled eval type " ++ show ctx) $ return ctx

doExpr :: (ExprContext -> ListT AEnv ExprContext) -> (ExprContext -> ListT AEnv ExprContext) -> (ExprContext -> ListT AEnv ExprContext) -> ExprContext -> ListT AEnv ExprContext
doExpr eval expr call ctx = do
  query <- lift queryId
  trace (query ++ "Expr " ++ show ctx)
    wrapMemo "expr" ctx $
    case ctx of
      AppCLambda _ c e -> 
        trace (query ++ "Evaluates to " ++ show e) $
        return c
      AppCParam _ c _ _ -> do
        fn <- doAEnvMaybe query $ focusFun c
        ctxlam <- eval fn
        bd <- doAEnvMaybe query $ focusBody ctxlam
        ctx' <- lift $ findUsage2 query (lamVar ctxlam) bd
        L.fromFoldable ctx' >>= expr
      LamCBody{} -> do
        ctxlambody <- call ctx
        expr ctxlambody
      ExprCBasic _ c _ -> expr c
      LetCBody{} -> do
        return $ ExprCTerm $ "expressions where let body " ++ show ctx ++ " is called"
      LetCDef{} -> do
        return $ ExprCTerm $ "expressions where let def " ++ show ctx ++ " is called"
      CaseCMatch{} -> do
        return $ ExprCTerm $ "expressions where case match " ++ show ctx ++ " is called"
      CaseCBranch{} -> do
        return $ ExprCTerm $ "expressions where case branch " ++ show ctx ++ " is called"
      DefCRec{} -> do
        return $ ExprCTerm $ "expressions where recursive def " ++ show ctx ++ " is called"
      DefCNonRec _ c d -> do
        ctx' <- lift $ findUsage2 query (lamVarDef d) c
        L.fromFoldable ctx' >>= expr
        -- trace ("Expr def non rec results " ++ show ctx') $ 
      ModuleC _ _ nm -> return $ ExprCTerm $ "expressions where module " ++ show nm ++ " is called (should never happen)"

doCall :: (ExprContext -> ListT AEnv ExprContext) -> (ExprContext -> ListT AEnv ExprContext) -> (ExprContext -> ListT AEnv ExprContext) -> ExprContext -> ListT AEnv ExprContext
doCall eval expr call ctx = 
  wrapMemo "call" ctx $ do
  query <- lift queryId
  trace (query ++ "Call " ++ show ctx) $
   case ctx of
      LamCBody _ c _ _-> expr c
      DefCNonRec _ c d -> do
        ctx' <- lift $ findUsage2 query (lamVarDef d) c
        L.fromFoldable ctx' >>= expr
      _ -> return $ ExprCTerm $ "call not implemented for " ++ show ctx

fix3_eval :: (t1 -> t2 -> t -> t1) -> (t1 -> t2 -> t -> t2) -> (t1 -> t2 -> t -> t) -> t1
fix3_eval eval expr call =
  eval (fix3_eval eval expr call) (fix3_expr eval expr call) (fix3_call eval expr call)

fix3_expr :: (t1 -> t2 -> t -> t1) -> (t1 -> t2 -> t -> t2) -> (t1 -> t2 -> t -> t) -> t2
fix3_expr eval expr call =
  expr (fix3_eval eval expr call) (fix3_expr eval expr call) (fix3_call eval expr call)

fix3_call :: (t1 -> t2 -> t3 -> t1) -> (t1 -> t2 -> t3 -> t2) -> (t1 -> t2 -> t3 -> t3) -> t3
fix3_call eval expr call =
  call (fix3_eval eval expr call) (fix3_expr eval expr call) (fix3_call eval expr call)

fixedEval e = L.toList $ fix3_eval doEval doExpr doCall e
fixedExpr e = L.toList $ fix3_expr doEval doExpr doCall e
fixedCall e = L.toList $ fix3_call doEval doExpr doCall e

allModules :: Loaded -> [Module]
allModules loaded = loadedModule loaded : loadedModules loaded

getModule :: String -> AEnv Module
getModule name = do
  modules <- allModules . loaded <$> getEnv
  return $ head $ filter (\mod -> (nameModule . modName) mod == name) modules

getDefAndGroup :: Module -> TName -> DefGroups -> Maybe (Module, Def, Int, DefGroup)
getDefAndGroup mod tname defGs =
  let def = find (\def -> defName def == getName tname && defType def == tnameType tname) (concatMap defsOf defGs)
  in case def of
    Just d -> let group = head $ filter (\dg -> tname `elem` defGroupTNames dg) defGs in
                Just (mod, d, fromJust (elemIndex d (defsOf group)), group)
    Nothing -> Nothing

findTopDefRef :: TName -> AEnv (Maybe (Module, Def, Int, DefGroup))
findTopDefRef tname = do
  loaded <- loaded <$> getEnv
  mod <- getModule (nameModule (getName tname))
  let defs = coreProgDefs . modCoreNoOpt $ mod
  return $ getDefAndGroup mod tname defs

basicExprOf :: ExprContext -> Maybe Expr
basicExprOf ctx =
  case ctx of
    ExprCBasic _ ctx e -> Just e
    _ -> Nothing

defsOf :: DefGroup -> [Def]
defsOf (DefNonRec d) = [d]
defsOf (DefRec ds) = ds

lookupDefGroup :: DefGroup -> TName -> Bool
lookupDefGroup dg tname = tname `elem` defGroupTNames dg

lookupDefGroups :: DefGroups -> TName -> Bool
lookupDefGroups defGs tname = any (flip lookupDefGroup tname) defGs

lookupDef :: Def -> TName -> Bool
lookupDef def tname = defName def == getName tname && tnameType tname == defType def

addChildrenContexts :: ExprContextId -> [ExprContext] -> AEnv ()
addChildrenContexts parentCtx contexts = do
  state <- getState
  let newIds = map contextId contexts
      newChildren = Data.Map.insert parentCtx (S.fromList newIds) (childrenIds state)
   -- trace ("Adding " ++ show childStates ++ " previously " ++ show (Data.Map.lookup parentCtx (childrenIds state))) 
  setState state{childrenIds = newChildren}

newContextId :: AEnv ExprContextId
newContextId = do
  state <- getState
  id <- currentContextId <$> getEnv
  return $ ExprContextId (Data.Map.size $ states state) (moduleName id) (topDef id) (topDefType id)

addContextId :: (ExprContextId -> ExprContext) -> AEnv ExprContext
addContextId f = do
  newId <- newContextId
  state <- getState
  let x = f newId
  setState state{states=Data.Map.insert newId x (states state)}
  return x

childrenOfExpr :: ExprContext -> Expr -> AEnv [ExprContext]
childrenOfExpr ctx expr =
  case expr of
    Lam names eff e -> addContextId (\newId -> LamCBody newId ctx names e) >>= single
    App f vs -> do
      x <- addContextId (\newId -> AppCLambda newId ctx f )
      rest <- zipWithM (\i x -> addContextId (\newId -> AppCParam newId ctx i x)) [0..] vs
      return $! x : rest
    Let defs result -> do
      defs <- zipWithM (\i x -> addContextId (\newId -> LetCDef newId ctx i x)) [0..] defs
      result <- addContextId (\newId -> LetCBody newId ctx result)
      return $! result:defs
    Case exprs branches -> do
      match <- addContextId (\newId -> CaseCMatch newId ctx (head exprs))
      branches <- zipWithM (\i x -> addContextId (\newId -> CaseCBranch newId ctx i x)) [0..] branches
      return $! match : branches
    Var name info -> addContextId (\newId -> ExprCBasic newId ctx expr ) >>= single
    TypeLam tvars expr -> childrenOfExpr ctx expr
    TypeApp expr tps -> childrenOfExpr ctx expr
    Con name repr -> addContextId (\newId -> ExprCBasic newId ctx expr) >>= single
    Lit lit -> addContextId (\newId -> ExprCBasic newId ctx expr) >>= single
  where single x = return [x]

childrenOfDef :: ExprContext -> DefGroup -> AEnv [ExprContext]
childrenOfDef ctx def =
  case def of
    DefNonRec d -> addContextId (\newId -> DefCNonRec newId ctx d) >>= (\x -> return [x])
    DefRec ds -> zipWithM (\i d -> addContextId (\newId -> DefCRec newId ctx i d)) [0..] ds

childrenContexts :: ExprContext -> AEnv [ExprContext]
childrenContexts ctx = do
  let parentCtxId = contextId ctx
  children <- childrenIds <$> getState
  let childIds = Data.Map.lookup parentCtxId children
  case childIds of
    Nothing -> do
        -- trace ("No children for " ++ show ctx) $ return ()
        newCtxs <- case ctx of
              ModuleC _ mod _ -> do
                res <- mapM (childrenOfDef ctx) (coreProgDefs $ modCoreNoOpt mod)
                return $ concat res
              DefCRec _ _ _ d -> childrenOfExpr ctx (defExpr d)
              DefCNonRec _ _ d -> childrenOfExpr ctx (defExpr d)
              LamCBody _ _ names body -> childrenOfExpr ctx body
              AppCLambda _ _ f -> childrenOfExpr ctx f
              AppCParam _ _ _ param -> childrenOfExpr ctx param
              LetCDef _ _ _ defg -> childrenOfDef ctx defg
              LetCBody _ _ e -> childrenOfExpr ctx e
              CaseCMatch _ _ e -> childrenOfExpr ctx e
              CaseCBranch _ _ _ b -> do
                x <- mapM (childrenOfExpr ctx . guardExpr) $ branchGuards b -- TODO Better context for branch guards
                return $ concat x
              ExprCBasic{} -> return []
        addChildrenContexts parentCtxId newCtxs
        return $ newCtxs
    Just childIds -> do
      -- trace ("Got children for " ++ show ctx ++ " " ++ show childIds) $ return ()
      states <- states <$> getState
      return $ map (states Data.Map.!) (S.toList childIds)

visitChildrenCtxs :: ([a] -> a) -> ExprContext -> AEnv a -> AEnv a
visitChildrenCtxs combine ctx analyze = do
  children <- childrenContexts ctx
  -- trace ("Got children of ctx " ++ show ctx ++ " " ++ show children) $ return ()
  res <- mapM (\child -> withEnv (\e -> e{currentContext = child, currentContextId =contextId child}) analyze) children
  return $ combine res