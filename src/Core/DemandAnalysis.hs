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
import Core.Core (Expr (..), DefGroups, Def (..), DefGroup (..), Branch (..), Guard(..), Pattern(..), TName (..), defsTNames, defGroupTNames, mapDefGroup, Core (..), VarInfo (..), defTName, makeDef, Lit (..))
import Data.Map hiding (findIndex, filter, map)
import qualified ListT as L
-- import Debug.Trace (trace)
import Core.Pretty
import Type.Type (isTypeInt, isTypeInt32, Type (..), expandSyn, TypeCon (..), ConInfo (..), Flavour (Bound), TypeVar (TypeVar), effectEmpty)
import Data.Sequence (mapWithIndex, fromList)
import qualified Data.Sequence as Seq
import Data.Maybe (mapMaybe, isJust, fromJust, maybeToList, fromMaybe)
import Data.List (find, findIndex, elemIndex, union)
import Debug.Trace
import Compiler.Module (Loaded (..), Module (..), ModStatus (LoadedIface), addOrReplaceModule)
import Lib.PPrint (Pretty(..))
import Type.Pretty (ppType, defaultEnv, Env (..))
import Kind.Kind (Kind(..), kindFun, kindStar)
import Control.Monad.Trans
import ListT (ListT)
import Common.Range (Range, rangesOverlap, showFullRange)
import Syntax.RangeMap (RangeInfo)
import Common.NamePrim (nameOpen, nameEffectOpen)
import Core.CoreVar
import GHC.IO (unsafePerformIO)

data AbstractLattice =
  AbBottom | AbTop

-- trace:: String -> a -> a
-- trace x y = y

-- Uniquely identifies expressions despite naming
data ExprContext =
  -- Current expression context
  ModuleC ExprContextId Module Name -- Module context
  | DefCRec ExprContextId ExprContext [TName] Int Def -- A recursive definition context, working on the index'th definition
  | DefCNonRec ExprContextId ExprContext [TName] Def -- In a non recursive definition context, working on Def
  | LamCBody ExprContextId ExprContext [TName] Expr -- Inside a lambda body expression
  | AppCLambda ExprContextId ExprContext Expr -- Application context inside function context
  | AppCParam ExprContextId ExprContext Int Expr -- Application context inside param context
  -- TODO: This needs adjustment, currently it flatmaps over the defgroup and indexes over that
  | LetCDef ExprContextId ExprContext [TName] Int DefGroup -- In a let definition context working on a particular defgroup
  | LetCBody ExprContextId ExprContext [TName] Expr -- In a let body expression
  | CaseCMatch ExprContextId ExprContext Expr -- In a case match context working on the match expression (assumes only one)
  | CaseCBranch ExprContextId ExprContext [TName] Int Branch -- Which branch currently inspecting, as well as the Case context
  | ExprCBasic ExprContextId ExprContext Expr -- A basic expression context that has no sub expressions
  | ExprCTerm ExprContextId String -- Since analysis can fail or terminate early, keep track of the query that failed

-- newtype EnvCtx = EnvCtx [[Ctx]] deriving (Eq, Ord, Show)
newtype EnvCtx = EnvCtx [Ctx] deriving (Eq, Ord)

instance Show EnvCtx where
  show (EnvCtx ctxs) = show ctxs

data Ctx =
  IndetCtx
  | DegenCtx
  | CallCtx ExprContext EnvCtx
  | TopCtx
  deriving (Eq, Ord)

instance Show Ctx where
  show ctx =
    case ctx of
      IndetCtx -> "?"
      DegenCtx -> "[]"
      CallCtx id env -> "call(" ++ show id ++ "," ++ show env ++ ")"
      TopCtx -> "()"

-- data Ctx =
--   DegenCtx -- Degenerate bottom of Ctx sequence (means we were limited by m)
--   | TopCtx -- Empty top context (called from top level)
--   | IndetCtx ExprContextId -- Indeterminate context for a particular set of bindings
--   | CallCtx ExprContextId -- Call context for a particular call
--   deriving (Eq, Ord, Show)

data ConstrContext =
  ConstrContext{
    constrName:: Name,
    constrType:: Type,
    constrParams:: AbValue
  } deriving (Eq, Ord, Show)

data SimpleLattice x =
  SimpleAbBottom
  | Simple x
  | SimpleAbTop
  deriving (Eq, Ord, Show)

joinL :: Eq x => SimpleLattice x -> SimpleLattice x -> SimpleLattice x
joinL SimpleAbBottom x = x
joinL x SimpleAbBottom = x
joinL SimpleAbTop _ = SimpleAbTop
joinL _ SimpleAbTop = SimpleAbTop
joinL (Simple x) (Simple y) = if x == y then Simple x else SimpleAbTop

joinML :: Eq x => Map EnvCtx (SimpleLattice x) -> Map EnvCtx (SimpleLattice x) -> Map EnvCtx (SimpleLattice x)
joinML = unionWith joinL

data AbValue =
  AbValue{
    closures:: Set (ExprContext, EnvCtx),
    constrs:: Set ConstrContext,
    intV:: Map EnvCtx (SimpleLattice Integer),
    floatV:: SimpleLattice Double,
    charV:: SimpleLattice Char,
    stringV:: SimpleLattice String,
    err:: Maybe String
  } deriving (Eq, Ord)

instance Show AbValue where
  show (AbValue cls cntrs i f c s e) =
    (if S.null cls then "" else "closures: " ++ show (S.toList cls)) ++
    (if S.null cntrs then "" else " constrs: " ++ show (S.toList cntrs)) ++
    (if Data.Map.null i then "" else " ints: " ++ show (Data.Map.toList i)) ++
    (if f == SimpleAbBottom then "" else " float: " ++ show f) ++
    (if c == SimpleAbBottom then "" else " char: " ++ show c) ++
    (if s == SimpleAbBottom then "" else " string: " ++ show s) ++
    maybe "" (" err: " ++) e

emptyAbValue :: AbValue
emptyAbValue = AbValue S.empty S.empty Data.Map.empty SimpleAbBottom SimpleAbBottom SimpleAbBottom Nothing
injClosure ctx env = emptyAbValue{closures= S.singleton (ctx, env)}
injErr err = emptyAbValue{err= Just err}

injLit :: Lit -> EnvCtx -> AbValue
injLit x env =
  case x of
    LitInt i -> emptyAbValue{intV= Data.Map.singleton env $ Simple i}
    LitFloat f -> emptyAbValue{floatV= Simple f}
    LitChar c -> emptyAbValue{charV= Simple c}
    LitString s -> emptyAbValue{stringV= Simple s}

joinAbValue :: AbValue -> AbValue -> AbValue
joinAbValue (AbValue cls0 cs0 i0 f0 c0 s0 e0) (AbValue cls1 cs1 i1 f1 c1 s1 e1) = AbValue (S.union cls0 cls1) (S.union cs0 cs1) (i0 `joinML` i1) (f0 `joinL` f1) (c0 `joinL` c1) (s0 `joinL` s1) (e0 `mplus` e1)

paramIndex e =
  case e of
    AppCParam _ _ i _ -> i

enclosingLambda :: ExprContext -> Maybe ExprContext
enclosingLambda ctx =
  case ctx of
    LamCBody{} -> Just ctx
    AppCLambda _ c _ -> enclosingLambda c
    AppCParam _ c _ _ -> enclosingLambda c
    DefCRec _ c _ _ _ -> enclosingLambda c
    DefCNonRec _ c _ _ -> enclosingLambda c
    LetCDef _ c _ _ _ -> enclosingLambda c
    LetCBody _ c _ _ -> enclosingLambda c
    CaseCMatch _ c _ -> enclosingLambda c
    CaseCBranch _ c _ _ _ -> enclosingLambda c
    ExprCBasic _ c _ -> enclosingLambda c
    ExprCTerm{} -> Nothing
    ModuleC{} -> Nothing

focusParam :: Maybe Int -> ExprContext -> AEnv (Maybe ExprContext)
focusParam index e = do
  children <- childrenContexts e
  query <- getQueryString
  return $ case index of
    Just x | x + 1 < length children -> Just $ children !! (x + 1) -- Parameters are the not the first child of an application (that is the function)
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


focusChild :: ExprContext -> Int -> AEnv (Maybe ExprContext)
focusChild e index = do
  children <- childrenContexts e
  query <- getQueryString
  return $ if index < length children then
    trace (query ++ "Focused child " ++ show (children !! index) ++ " " ++ show index ++ " " ++ show children) $
      Just (children !! index)
    else trace (query ++ "Children looking for child at " ++ show index ++ " " ++ show children) Nothing

focusLetBinding :: Maybe Int -> ExprContext -> AEnv (Maybe ExprContext)
focusLetBinding index e = do
  children <- childrenContexts e
  query <- getQueryString
  return $ case index of
    Just x | x < length children -> Just $ children !! x
    _ -> trace (query ++ "Children looking for let binding " ++ show children) Nothing

lamVar :: Int -> ExprContext -> Expr
lamVar index ctx =
  case maybeExprOfCtx ctx of
    Just (Lam names _ _) -> Var (names !! index) InfoNone
    Just (TypeLam e (Lam names _ _)) -> Var (names !! index) InfoNone
    _ -> trace ("DemandAnalysis.lamVar: not a lambda " ++ show ctx) error "Not a lambda"

lamVarDef :: Def -> Expr
lamVarDef def = Var (TName (defName def) (defType def) Nothing) InfoNone

showExpr :: Expr -> String
showExpr e = show $ prettyExpr defaultEnv{showRanges=True} e

showDg d = show $ prettyDefGroup defaultEnv d

showDef d = show $ prettyDef defaultEnv d

instance Show ExprContext where
  show e =
    case e of
      ModuleC _ _ nm -> "Module " ++ show nm
      DefCRec _ _ _ i df -> "DefRec " ++ showDef df
      DefCNonRec _ _ _ df -> "DefNonRec " ++ showDef df
      LamCBody _ _ tn e -> "LamBody " ++ show tn ++ " " ++ showExpr e
      AppCLambda _ _ f -> "AppLambda " ++ showExpr f
      AppCParam _ _ i p -> "AppParam " ++ show i ++ " " ++ showExpr p
      LetCDef _ _ _ i dg -> "LetDef " ++ showDg dg
      LetCBody _ _ _ e -> "LetBody " ++ showExpr e
      CaseCMatch _ _ e -> "CaseMatch " ++ showExpr e
      CaseCBranch _ _ _ i b -> "CaseBranch " ++ show i ++ " " ++ show b
      ExprCBasic _ _ e -> "ExprBasic " ++ showExpr e
      ExprCTerm _ s -> "Query: " ++ s

exprOfCtx :: ExprContext -> Expr
exprOfCtx ctx =
  case ctx of
    ModuleC {} -> error "ModuleC is a multi Expression Context"
    DefCRec _ _ _ _ d -> defExpr d
    DefCNonRec _ _ _ d -> defExpr d
    LamCBody _ _ _ e -> e
    AppCLambda _ _ f -> f
    AppCParam _ _ _ param -> param
    LetCDef _ _ _ i dg -> defExpr (defsOf dg !! i)
    LetCBody _ _ _ e -> e
    CaseCMatch _ _ e -> e
    CaseCBranch _ _ _ _ b -> guardExpr (head (branchGuards b))
    ExprCBasic _ _ e -> e
    ExprCTerm{} -> error "Query should never be queried for expression"

maybeExprOfCtx :: ExprContext -> Maybe Expr
maybeExprOfCtx ctx =
  case ctx of
    ModuleC {} -> Nothing
    DefCRec _ _ _ _ d -> Just $ defExpr d
    DefCNonRec _ _ _ d -> Just $ defExpr d
    LamCBody _ _ _ e -> Just e
    AppCLambda _ _ f -> Just f
    AppCParam _ _ _ param -> Just param
    LetCDef _ _ _ _ dg -> Nothing
    LetCBody _ _ _ e -> Just e
    CaseCMatch _ _ e -> Just e
    CaseCBranch _ _ _ _ b -> Just $ guardExpr (head (branchGuards b))
    ExprCBasic _ _ e -> Just e
    ExprCTerm{} -> error "Query should never be queried for expression"

contextId :: ExprContext -> ExprContextId
contextId ctx =
  case ctx of
    ModuleC c _ _ -> c
    DefCRec c _ _ _ _ -> c
    DefCNonRec c _ _ _ -> c
    LamCBody c _ _ _ -> c
    AppCLambda c _ _ -> c
    AppCParam c _ _ _ -> c
    LetCDef c _ _ _ _ -> c
    LetCBody c _ _ _ -> c
    CaseCMatch c _ _ -> c
    CaseCBranch c _ _ _ _ -> c
    ExprCBasic c _ _ -> c
    ExprCTerm c _ -> c

contextOf :: ExprContext -> Maybe ExprContext
contextOf ctx =
  case ctx of
    ModuleC _ _ _ -> Nothing
    DefCRec _ c _ _ _ -> Just c
    DefCNonRec _ c _ _ -> Just c
    LamCBody _ c _ _ -> Just c
    AppCLambda _ c _ -> Just c
    AppCParam _ c _ _ -> Just c
    LetCDef _ c _ _ _ -> Just c
    LetCBody _ c _ _ -> Just c
    CaseCMatch _ c _ -> Just c
    CaseCBranch _ c _ _ _ -> Just c
    ExprCBasic _ c _ -> Just c
    ExprCTerm{} -> error "Query should never be queried for context"

branchContainsBinding :: Branch -> TName -> Bool
branchContainsBinding (Branch pat guards) name =
  name `elem` bv pat

data ExprContextId = ExprContextId{
  exprId:: Int,
  moduleName:: Name
} deriving (Ord, Eq)

instance Show ExprContextId where
  show id =
    nameId (moduleName id) ++ ":" ++ show (exprId id)

instance Eq ExprContext where
  ctx1 == ctx2 = contextId ctx1 == contextId ctx2

instance Ord ExprContext where
  compare ctx1 ctx2 = compare (contextId ctx1) (contextId ctx2)

instance Ord Type where
  compare tp1 tp2 = compare (show $ ppType defaultEnv tp1) (show $ ppType defaultEnv tp2)

instance Eq Def where
  def1 == def2 = defName def1 == defName def2 && defType def1 == defType def2

type ExpressionSet = Set ExprContextId

newtype AEnv a = AEnv (DEnv -> State -> Result a)
data State = State{
  loaded :: Loaded,
  states :: Map ExprContextId ExprContext,
  childrenIds :: Map ExprContextId (Set ExprContextId),
  evalCacheGeneration :: Int,
  evalCache :: Map ExprContextId (Map EnvCtx (Int, AbValue)),
  memoCache :: Map String (Map (ExprContextId, EnvCtx) (Set (ExprContext, EnvCtx))),
  unique :: Int
}
data Result a = Ok a State

data DEnv = DEnv{
  contextLength :: Int,
  currentContext :: !ExprContext,
  currentEnv:: EnvCtx,
  currentQuery:: String,
  queryIndentation:: String,
  loadModuleFromSource :: (Module -> IO Module)
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

withEnv :: (DEnv -> DEnv) -> AEnv a -> AEnv a
withEnv f (AEnv c)
  = AEnv (c . f)

getEnv :: AEnv DEnv
getEnv = AEnv Ok

getState :: AEnv State
getState = AEnv (\env st -> Ok st st)

setState :: State -> AEnv ()
setState st = AEnv (\env _ -> Ok () st)

getQueryString :: AEnv String
getQueryString = do
  env <- getEnv
  return $ queryIndentation env ++ currentQuery env ++ show (contextId $ currentContext env) ++ " "

getContext :: ExprContextId -> AEnv ExprContext
getContext id = do
  st <- getState
  case Data.Map.lookup id (states st) of
    Just x -> return x
    _ -> error $ "Context not found " ++ show id

getUnique :: AEnv Int
getUnique = do
  st <- getState
  let u = unique st
  setState st{unique = u + 1}
  return u


updateState :: (State -> State) -> AEnv ()
updateState update = do
  st <- getState
  setState $ update st

runEvalQueryFromRange :: Loaded -> (Module -> IO Module) -> (Range, RangeInfo) -> Module -> [(EnvCtx, AbValue)]
runEvalQueryFromRange loaded loadModuleFromSource rng mod =
  runQueryAtRange loaded loadModuleFromSource rng mod $ \exprctxs ->
    case exprctxs of
      exprctx:rst -> do
        res <- fixedEval exprctx (indeterminateStaticCtx exprctx)
        trace ("eval result " ++ show res) $ return res
      _ -> return []

runQueryAtRange :: Loaded -> (Module -> IO Module) -> (Range, RangeInfo) -> Module -> ([ExprContext] -> AEnv a) -> a
runQueryAtRange loaded loadModuleFromSource (r, ri) mod query =
  let cid = ExprContextId (-1) (modName mod)
      modCtx = ModuleC cid mod (modName mod)
      focalContext = analyzeCtx (\a l -> a ++ concat l) (const $ findContext r ri) modCtx
      result = case focalContext >>= query of
        AEnv f -> f (DEnv 2 modCtx (EnvCtx []) "" "" loadModuleFromSource) (State loaded Data.Map.empty Data.Map.empty 0 (Data.Map.empty) (Data.Map.fromList [("eval", Data.Map.empty), ("call", Data.Map.empty), ("expr", Data.Map.empty) ]) 0)
  in case result of
    Ok a st -> a

findContext :: Range -> RangeInfo -> AEnv [ExprContext]
findContext r ri = do
  ctx <- currentContext <$> getEnv
  case ctx of
    ExprCBasic _ _ (Var (TName _ _ (Just rng)) _) | r `rangesOverlap` rng -> trace ("found overlapping range " ++ showFullRange rng ++ " " ++ show ctx) $ return [ctx]
    ExprCBasic _ _ (Var (TName _ _ (Just rng)) _) -> -- trace ("var range doesn't overlap "++ show ctx ++ " " ++ showFullRange rng) $
      return []
    _ -> return []

analyzeCtx :: (a -> [a] -> a) -> (ExprContext -> AEnv a) -> ExprContext  -> AEnv a
analyzeCtx combine analyze ctx = do
  -- id <- currentContext <$> getEnv
  -- trace ("Analyzing ctx " ++ show ctx ++ " with id " ++ show (exprId id)) $ return ()
  res <- analyze ctx
  visitChildrenCtxs (combine res) ctx $ do
    childCtx <- currentContext <$> getEnv
    analyzeCtx combine analyze childCtx

moduleDummyType :: Type
moduleDummyType = TCon $ TypeCon (newName "dummy") (KCon (newName "dummy"))

-- BIND: The resulting context is not only a nested context focused on a lambda body It is also
-- can be focused on a Let Body or Recursive Let binding It can also be focused on a Recursive Top
-- Level Definition Body It can be bound to a different top level definition It can also be focused on a
-- branch of a match statement BIND requires searching the imported modules for both the name
-- and definition. As such a module import graph should be used. The value of the parameter in the
-- case of unknown definitions is simply the top of the type lattice for the type of the parameter in
-- question. - Additional note: Since Koka uses interface modules to avoid re-parsing user code, we
-- need to determine an appropriate tradeoff in precision and compilation. In particular, a full core
-- file might be an appropriate file to output in addition to the core interface. We only load the core
-- file with the full definitions on demand when we detect that it would increase precision?
bind :: ExprContext -> Expr -> EnvCtx -> Maybe ((ExprContext, EnvCtx), Maybe Int)
bind ctx var@(Var tname vInfo) env =
  case ctx of
    ModuleC _ mod _ -> if lookupDefGroups (coreProgDefs $ modCoreNoOpt mod) tname then Just ((ctx, env), Nothing) else trace ("External variable binding " ++ show tname ++ ": " ++ show vInfo) Nothing
    DefCRec _ ctx' names i d -> lookupName names ctx'
    DefCNonRec _ ctx' names d -> lookupName names ctx'
    LamCBody _ ctx' names _  -> lookupNameNewCtx names ctx'
    AppCLambda _ ctx _ -> bind ctx var env
    AppCParam _ ctx _ _ -> bind ctx var env
    LetCDef _ ctx' names i _ -> lookupName names ctx'
    LetCBody _ ctx' names _ -> lookupName names ctx'
    CaseCMatch _ ctx _ -> bind ctx var env
    CaseCBranch _ ctx' names _ b -> lookupName names ctx'
    ExprCBasic _ ctx _ -> bind ctx var env
    ExprCTerm{} -> Nothing
  where
    lookupNameNewCtx names ctx' =
      case elemIndex tname names
        of Just x -> Just ((ctx, env), Just x)
           _ -> bind ctx' var (envtail env) -- lambdas introduce a new binding context that relates to calls. Other binding expressions do not
    lookupName names ctx' =
      case elemIndex tname names
        of Just x -> Just ((ctx, env), Just x)
           _ -> bind ctx' var env

indeterminateStaticCtx :: ExprContext -> EnvCtx
indeterminateStaticCtx ctx =
  case ctx of
    ModuleC _ mod _ -> EnvCtx [TopCtx]
    DefCRec _ ctx' _ _ _ -> indeterminateStaticCtx ctx'
    DefCNonRec _ ctx' _ _ -> indeterminateStaticCtx ctx'
    LamCBody _ ctx' _ _ ->
      let (EnvCtx parent) = indeterminateStaticCtx ctx'
      in EnvCtx (IndetCtx:parent)
    AppCLambda _ ctx _ -> indeterminateStaticCtx ctx
    AppCParam _ ctx _ _ -> indeterminateStaticCtx ctx
    LetCDef _ ctx' _ _ _ -> indeterminateStaticCtx ctx'
    LetCBody _ ctx' _ _ -> indeterminateStaticCtx ctx'
    CaseCMatch _ ctx _ -> indeterminateStaticCtx ctx
    CaseCBranch _ ctx' _ _ _ -> indeterminateStaticCtx ctx'
    ExprCBasic _ ctx _ -> indeterminateStaticCtx ctx
    ExprCTerm{} -> error "Never should occur"

bindExternal :: Expr -> AEnv (Maybe (ExprContext, Maybe Int))
bindExternal var@(Var tn@(TName name tp _) vInfo) = do
  deps <- loadedModules . loaded <$> getState
  let x = find (\m -> modName m == newName (nameModule name)) deps
  case x of
    Just mod -> do
      ctxId <- newContextId
      mod' <- if modStatus mod == LoadedIface then do
        -- TODO: set some level of effort / time required for loading externals, but potentially load all core modules on startup
                load <- loadModuleFromSource <$> getEnv
                let mod' = unsafePerformIO $ load mod
                updateState (\state ->
                  let ld = loaded state
                  in state{loaded = ld{loadedModules = addOrReplaceModule mod' (loadedModules ld) }})
                return mod'
              else return mod
      return $ if lookupDefGroups (coreProgDefs $ modCoreNoOpt mod') tn then Just (ModuleC ctxId mod' (modName mod'), Nothing) else trace ("External variable binding " ++ show tn ++ ": " ++ show vInfo) Nothing
    _ -> return Nothing

findUsage :: Expr -> ExprContext -> EnvCtx -> AEnv (Set (ExprContext, EnvCtx))
findUsage expr@Var{varName=tname@TName{getName = name}} ctx env@(EnvCtx cc) =
  let nameEq = (== name)
      empty = return S.empty
      childrenUsages =
        visitChildrenCtxs S.unions ctx $ do -- visitChildrenCtxs sets the currentContext
          childCtx <- currentContext <$> getEnv
          -- trace ("Looking for usages of " ++ show name ++ " in " ++ show ctx) $ return empty
          findUsage expr childCtx env in
  case maybeExprOfCtx ctx of
    Just (Lam params _ _) ->
      let paramNames = map getName params in
      if name `elem` paramNames then -- shadowing
        empty
      else
        visitChildrenCtxs S.unions ctx $ do
          childCtx <- currentContext <$> getEnv
          findUsage expr childCtx (EnvCtx (IndetCtx:cc))
    Just (Var{varName=TName{getName=name2}}) ->
      if nameEq name2 then do
        query <- getQueryString
        return $ trace (query ++ "Found usage in " ++ show ctx) $ S.singleton (ctx, env)
      else
        -- trace ("Not found usage in " ++ show ctx ++ " had name " ++ show name2 ++ " expected " ++ show name) $ empty
        empty
    _ -> childrenUsages -- TODO Avoid shadowing let bindings

newQuery :: String -> ExprContext -> EnvCtx -> (String -> AEnv a) -> AEnv a
newQuery kind exprctx envctx d = do
  unique <- getUnique
  withEnv (\env -> env{currentContext = exprctx, currentEnv = envctx, currentQuery = "q" ++ show unique ++ "(" ++ kind ++ ")" ++ ": ", queryIndentation = queryIndentation env ++ " "}) $ do
    query <- getQueryString
    d query

wrapMemo :: String -> ExprContext -> EnvCtx -> AEnv [(ExprContext, EnvCtx)] -> AEnv [(ExprContext, EnvCtx)]
wrapMemo name ctx env f = do
  state <- getState
  let cache = (Data.Map.!) (memoCache state) name
  case Data.Map.lookup (contextId ctx, env) cache of
    Just x -> return $ S.toAscList x
    _ -> do
      res <- f
      state <- getState
      let cache = (Data.Map.!) (memoCache state) name
      let newCache = Data.Map.insertWith S.union (contextId ctx, env) (S.fromList res) cache
      setState state{memoCache = Data.Map.insert name newCache (memoCache state)}
      return res

wrapMemoEval :: ExprContext -> EnvCtx -> AEnv AbValue -> AEnv AbValue
wrapMemoEval ctx env f = do
  state <- getState
  case Data.Map.lookup (contextId ctx) (evalCache state) of
    Just ctxmap ->
      case Data.Map.lookup env ctxmap of
        Just (gen, oldAbValue) ->
          -- TODO: Don't recompute if the cache has not changed
          if evalCacheGeneration state == gen then
            return oldAbValue
          else do
            ress <- f
            let newAbValue = joinAbValue oldAbValue ress
            if oldAbValue == newAbValue then return oldAbValue -- dont' change the cache generation if this hasn't added anything new
            else do
              state <- getState
              let newCacheGen = evalCacheGeneration state + 1
              let newCtxMap = Data.Map.insert env (newCacheGen, newAbValue) ctxmap
              let newCache = Data.Map.insert (contextId ctx) newCtxMap (evalCache state)
              setState state{evalCache = newCache, evalCacheGeneration = newCacheGen}
              return newAbValue
        _ -> do
          newAbValue <- f
          state <- getState
          let newCacheGen = evalCacheGeneration state + 1
          let newCtxMap = Data.Map.insert env (newCacheGen, newAbValue) ctxmap
          let newCache = Data.Map.insert (contextId ctx) newCtxMap (evalCache state)
          setState state{evalCache = newCache, evalCacheGeneration = newCacheGen}
          return newAbValue
    _ -> do
      newAbValue <- f
      state <- getState
      let newCacheGen = evalCacheGeneration state + 1
      let newCtxMap = Data.Map.insert env (newCacheGen, newAbValue) Data.Map.empty
      let newCache = Data.Map.insert (contextId ctx) newCtxMap (evalCache state)
      setState state{evalCache = newCache, evalCacheGeneration = newCacheGen}
      return newAbValue

succAEnv :: Ctx -> AEnv Ctx
succAEnv newctx = do
  length <- contextLength <$> getEnv
  return $ succm newctx length

succm :: Ctx -> Int -> Ctx
succm envctx m =
  if m == 0 then if envctx == TopCtx then TopCtx else DegenCtx
  else
    case envctx of
      CallCtx c e -> CallCtx c (succmenv e (m - 1))
      _ -> envctx

succmenv :: EnvCtx -> Int -> EnvCtx
succmenv (EnvCtx e) m =
  EnvCtx (map (\x -> succm x m) e)

doForAbValue :: AbValue -> [a] -> (a -> AEnv AbValue) -> AEnv AbValue
doForAbValue init l doA = do
  foldM (\res x -> do
    res' <- doA x
    return $ joinAbValue res res') init l

doMaybeAbValue :: AbValue -> Maybe a -> (a -> AEnv AbValue) -> AEnv AbValue
doMaybeAbValue init l doA = do
  case l of
    Just x -> doA x
    Nothing -> return init

doForContexts :: [(ExprContext, EnvCtx)] -> [a] -> (a -> AEnv [(ExprContext, EnvCtx)]) -> AEnv [(ExprContext, EnvCtx)]
doForContexts init l doA = do
  foldM (\res x -> do
    res' <- doA x
    return $ res ++ res') init l

doEval :: ((ExprContext, EnvCtx) -> AEnv AbValue) -> ((ExprContext, EnvCtx) -> AEnv [(ExprContext, EnvCtx)]) -> ((ExprContext, EnvCtx) -> AEnv [(ExprContext, EnvCtx)]) -> (ExprContext, EnvCtx) -> AEnv AbValue
doEval eval expr call (ctx, env) = newQuery "EVAL" ctx env (\query -> do
  trace (query ++ "EVAL: " ++ show env ++ " " ++ show (exprOfCtx ctx)) $
    wrapMemoEval ctx env $
    case exprOfCtx ctx of
      Lam{} -> -- LAM CLAUSE
        trace (query ++ "LAM: " ++ show ctx) $
        return $ injClosure ctx env
      v@(Var n _) | getName n == nameEffectOpen -> do -- TODO: Reevaluate eventually
        trace (query ++ "OPEN: " ++ show ctx) $ return []
        newId <- newContextId
        let tvar = TypeVar 0 (kindFun kindStar kindStar) Bound
            x = TName (newName "x") (TVar tvar) Nothing
            def = makeDef nameEffectOpen (TypeLam [tvar] (Lam [x] effectEmpty (Var x InfoNone)))
            newCtx = DefCNonRec newId ctx [defTName def] def
        return $ injClosure newCtx (EnvCtx [TopCtx])
      v@(Var tn _) -> do -- REF CLAUSE
-- REF: 
--  - When the binding is focused on a lambda body, we need to find the callers of the lambda, and proceed as original formulation. 
--  - When the binding is in the context of a Let Body we can directly evaluate the let binding as the value of the variable being bound (indexed to match the binding).
--  - When the binding is in the context of a Let binding, it evaluates to that binding or the indexed binding in a mutually recursive group 
--  - When the binding is a top level definition - it evaluates to that definition 
--  - When the binding is focused on a match body then we need to issue a subquery for the evaluation of the match expression that contributes to the binding, 
--         and then consider the abstract value and find all abstract values that match the pattern of the branch in question 
--         and only consider the binding we care about. 
--         This demonstrates one point where a context sensitive shape analysis could propagate more interesting information along with the subquery to disregard traces that don’t contribute
        -- trace (query ++ "REF: " ++ show ctx) $ return []
        let binded = bind ctx v env
        trace (query ++ "REF: bound to " ++ show binded) $ return []
        case binded of
          Just ((lambodyctx@LamCBody{}, bindedenv), Just index) -> do
            calls <- call (lambodyctx, bindedenv)
            doForAbValue emptyAbValue calls (\(appctx, appenv) -> do
              trace (query ++ "REF: found application " ++ show appctx ++ " " ++ show appenv ++ " param index " ++ show index) $ return []
              param <- focusParam (Just index) appctx
              doMaybeAbValue emptyAbValue param (\param -> eval (param, appenv)))
          -- Just ((letbodyctx@LetCBody{}, bindedenv), index) ->
          --   eval =<< withQuery query (focusChild (fromJust $ contextOf letbodyctx) (fromJust index))
          -- Just ((letdefctx@LetCDef{}, bindedenv), index) ->
          --   eval =<< withQuery query (focusChild (fromJust $ contextOf letdefctx) (fromJust index))
          Just ((matchbodyctx@CaseCBranch{}, bindedenv), index) -> do
            -- TODO:
            let msg = query ++ "REF: TODO: Match body context " ++ show v ++ " " ++ show matchbodyctx
            trace msg $ return $ injErr msg
          Just ((modulectx@ModuleC{}, bindedenv), index) -> do
            lamctx <- getDefCtx modulectx (getName tn)
            -- Evaluates just to the lambda
            eval (lamctx, EnvCtx [TopCtx])
          Just ((ctxctx, bindedenv), index) -> do
            children <- childrenContexts ctxctx
            let msg = query ++ "REF: unexpected context in result of bind: " ++ show v ++ " " ++ show ctxctx ++ " children: " ++ show children
            trace msg $ return $ injErr msg
          Nothing -> do
            ext <- bindExternal v
            case ext of
              Just (modulectx@ModuleC{}, index) -> do
                lamctx <- getDefCtx modulectx (getName tn)
                -- Evaluates just to the lambda
                eval (lamctx, EnvCtx [TopCtx])
              _ -> return $ injErr $ "REF: can't find what the following refers to " ++ show ctx
      App f tms -> do
        fun <- focusChild ctx 0
        doMaybeAbValue emptyAbValue fun (\fun -> do
            trace (query ++ "APP: Lambda Fun " ++ show fun) $ return []
            lamctx <- eval (fun, env)
            let clss = closures lamctx
            doForAbValue emptyAbValue (S.toList clss) (\(lam, EnvCtx lamenv) -> do
              trace (query ++ "APP: Lambda is " ++ show lamctx) $ return []
              bd <- focusBody lam
              doMaybeAbValue emptyAbValue bd (\bd -> do
                trace (query ++ "APP: Lambda body is " ++ show lamctx) $ return []
                childs <- childrenContexts ctx
                -- In the subevaluation if a binding for the parameter is requested, we should return the parameter in this context, 
                -- TODO: How does this affect any recursive contexts? (a local find from the body of the lambda)
                succ <- succAEnv (CallCtx ctx env)
                eval (bd, EnvCtx (succ:lamenv))
                )
              )
          )
      TypeApp{} ->
        case ctx of
          DefCNonRec{} -> return $ injClosure ctx env
          DefCRec{} -> return $ injClosure ctx env
          _ -> do
            ctx' <- focusChild ctx 0
            doMaybeAbValue emptyAbValue ctx' (\ctx -> eval (ctx,env))
      TypeLam{} ->
        case ctx of
          DefCNonRec{} -> return $ injClosure ctx env-- Don't further evaluate if it is just the definition / lambda
          DefCRec{} -> return $ injClosure ctx env-- Don't further evaluate if it is just the definition / lambda
          _ -> do
            ctx' <- focusChild ctx 0
            doMaybeAbValue emptyAbValue ctx' (\ctx -> eval (ctx,env))
      Lit l -> return $ injLit l env
      Case e branches -> do
        trace (query ++ "CASE: " ++ show ctx) $ return []
        -- discrim <- eval =<< withQuery query (focusChild ctx 0)
        -- let msg = query ++ "CASE: discrim is " ++ show discrim
        let msg = "Case not implemented"
        return $ trace msg $ injErr msg
      Con nm repr -> return $ injErr ("Constructor: " ++ show nm ++ " " ++ show ctx)
      _ ->
        let msg =  (query ++ "TODO: Not Handled Eval: " ++ show ctx ++ " expr: " ++ show (exprOfCtx ctx)) in
        trace msg $ return $ injErr msg
  )

newErrTerm :: String -> AEnv [(ExprContext, EnvCtx)]
newErrTerm s = do
  newId <- newContextId
  return [(ExprCTerm newId ("Error: " ++ s), EnvCtx [DegenCtx])]

doExpr :: ((ExprContext, EnvCtx) -> AEnv AbValue) -> ((ExprContext, EnvCtx) -> AEnv [(ExprContext, EnvCtx)]) -> ((ExprContext, EnvCtx) -> AEnv [(ExprContext, EnvCtx)]) -> (ExprContext, EnvCtx) -> AEnv [(ExprContext, EnvCtx)]
doExpr eval expr call (ctx, env) = newQuery "EXPR" ctx env (\query -> do
  trace (query ++ "EXPR " ++ show env ++ " "  ++ show (maybeExprOfCtx ctx)) $
    wrapMemo "expr" ctx env $
    case ctx of
      AppCLambda _ c e -> -- RATOR Clause
        trace (query ++ "RATOR: Expr is " ++ show ctx) $
        return [(c, env)]
      AppCParam _ c index e -> do -- RAND Clause 
        trace (query ++ "RAND: Expr is " ++ show ctx) $ return []
        fn <- focusFun c
        case fn of
          Just fn -> do
            -- trace (query ++ "RAND: Fn is " ++ show fn) $ return []
            ctxlam <- eval (fn, env)
            let clss = closures ctxlam
            doForContexts [] (S.toList clss) (\(lam, EnvCtx lamenv) -> do
              -- trace (query ++ "RAND: Lam is " ++ show lam) $ return []
              bd <- focusBody lam
              case bd of
                Nothing -> return []
                Just bd -> do
                  -- trace (query ++ "RAND: Lam body is " ++ show bd ++ " looking for usages of " ++ show (lamVar index lam)) $ return []
                  succ <- succAEnv (CallCtx ctx env)
                  ctxs <- findUsage (lamVar index lam) bd (EnvCtx $ succ:lamenv)
                  -- trace (query ++ "RAND: Usages are " ++ show ctxs) $ return []
                  ress <- mapM expr (S.toList ctxs)
                  return $ concat ress
              )
          Nothing -> return []
      LamCBody _ _ _ e -> do -- BODY Clause
        trace (query ++ "BODY: Expr is " ++ show ctx) $ return []
        res <- call (ctx, env)
        ress <- mapM expr res
        return $ concat ress
      ExprCTerm{} ->
        trace (query ++ "ends in error " ++ show ctx)
        return [(ctx, env)]
      DefCNonRec _ c index df -> do
        trace (query ++ "DEF: Expr is " ++ show ctx) $ return []
        ctxs <- findUsage (lamVarDef df) c (EnvCtx [TopCtx])
        trace (query ++ "Def: Usages are " ++ show ctxs) $ return []
        ress <- mapM expr (S.toList ctxs)
        return $ concat ress
      ExprCBasic _ c _ -> expr (c, env)
      _ ->
        case contextOf ctx of
          Just c ->
            case enclosingLambda c of
              Just c' -> expr (c', env)
              _ -> newErrTerm $ "Exprs has no enclosing lambda, so is always demanded (top level?) " ++ show ctx
          Nothing -> newErrTerm $ "expressions where " ++ show ctx ++ " is demanded (should never happen)"
  )

doCall :: ((ExprContext, EnvCtx) -> AEnv AbValue) -> ((ExprContext, EnvCtx) -> AEnv [(ExprContext, EnvCtx)]) -> ((ExprContext, EnvCtx) -> AEnv [(ExprContext, EnvCtx)]) -> (ExprContext, EnvCtx) -> AEnv [(ExprContext, EnvCtx)]
doCall eval expr call (ctx, env@(EnvCtx cc)) =
  wrapMemo "call" ctx env $ newQuery "CALL" ctx env (\query -> do
   trace (query ++ "CALL " ++ show env ++ " " ++ show (exprOfCtx ctx)) $
    case ctx of
        LamCBody _ c _ _->
          case cc of
            (CallCtx callctx p'):p -> do
              trace (query ++ "Known: " ++ show callctx) $ return ()
              pnew <- calibratem p'
              return [(callctx, pnew)]
            _ -> do
              trace (query ++ "Unknown") $ return ()
              expr (c, envtail env)
        ExprCTerm{} ->
          trace (query ++ "ends in error " ++ show ctx)
          return [(ctx, env)]
        -- DefCNonRec _ c _ d -> do
        --   ctx' <- findUsage2 query (lamVarDef d) c
        --   L.fromFoldable ctx' >>= expr
        _ -> newErrTerm $ "CALL not implemented for " ++ show ctx
  )

envtail :: EnvCtx -> EnvCtx
envtail (EnvCtx (c:p)) = EnvCtx p
envtail (EnvCtx []) = EnvCtx []

calibratem :: EnvCtx -> AEnv EnvCtx
calibratem ctx = do
  mlimit <- contextLength <$> getEnv
  return $ calibratemenv mlimit ctx

calibratemenv :: Int -> EnvCtx -> EnvCtx
calibratemenv mlimit (EnvCtx ps) = do
  EnvCtx $ map (calibratemctx mlimit) ps

calibratemctx :: Int -> Ctx -> Ctx
calibratemctx mlimit p =
  if mlimit == 0 then DegenCtx
  else case p of
    IndetCtx -> IndetCtx
    DegenCtx -> IndetCtx
    CallCtx c p' -> CallCtx c (calibratemenv (mlimit - 1) p')
    TopCtx -> TopCtx


fix3_eval :: (t1 -> t2 -> t3 -> t1) -> (t1 -> t2 -> t3 -> t2) -> (t1 -> t2 -> t3 -> t3) -> t1
fix3_eval eval expr call =
  eval (fix3_eval eval expr call) (fix3_expr eval expr call) (fix3_call eval expr call)

fix3_expr :: (t -> t2 -> t3 -> t) -> (t -> t2 -> t3 -> t2) -> (t -> t2 -> t3 -> t3) -> t2
fix3_expr eval expr call =
  expr (fix3_eval eval expr call) (fix3_expr eval expr call) (fix3_call eval expr call)

fix3_call :: (t -> t2 -> t3 -> t) -> (t -> t2 -> t3 -> t2) -> (t -> t2 -> t3 -> t3) -> t3
fix3_call eval expr call =
  call (fix3_eval eval expr call) (fix3_expr eval expr call) (fix3_call eval expr call)

fixedEval :: ExprContext -> EnvCtx -> AEnv [(EnvCtx, AbValue)]
fixedEval e env = do
  fix3_eval doEval doExpr doCall (e, env)
  state <- getState
  let cache = evalCache state
  case Data.Map.lookup (contextId e) cache of
    Just res -> return (map (\(k, (_, v)) -> (k, v)) (Data.Map.assocs res))
    Nothing -> do
      let msg = "fixedEval: " ++ show e ++ " not in cache " ++ show (Data.Map.keys cache)
      trace msg $ return [(EnvCtx [IndetCtx], injErr msg)]

fixedExpr :: ExprContext -> AEnv [(ExprContext, EnvCtx)]
fixedExpr e = fix3_expr doEval doExpr doCall (e, EnvCtx [])
fixedCall :: ExprContext -> AEnv [(ExprContext, EnvCtx)]
fixedCall e = fix3_call doEval doExpr doCall (e, EnvCtx [])

allModules :: Loaded -> [Module]
allModules loaded = loadedModule loaded : loadedModules loaded

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
lookupDefGroups defGs tname = any (`lookupDefGroup` tname) defGs

lookupDef :: Def -> TName -> Bool
lookupDef def tname = defName def == getName tname && tnameType tname == defType def

getDefCtx :: ExprContext -> Name -> AEnv ExprContext
getDefCtx ctx name = do
  children <- childrenContexts ctx
  case find (\dctx -> case dctx of
      DefCNonRec _ _ _ d | defName d == name -> True
      DefCRec _ _ _ _ d | defName d == name -> True
      _ -> False
      ) children of
    Just dctx -> do
      -- lamctx <- focusChild dctx 0 -- Actually focus the lambda
      return dctx
    Nothing -> error $ "getDefCtx: " ++ show ctx ++ " " ++ show name

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
  id <- currentContext <$> getEnv
  return $ ExprContextId (Data.Map.size $ states state) (moduleName (contextId id))

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
      let defNames = map defTName (concatMap defsOf defs)
      defs <- zipWithM (\i x -> addContextId (\newId -> LetCDef newId ctx defNames i x)) [0..] defs
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

branchVars :: Branch -> [TName]
branchVars (Branch pat guards) = S.toList $ bv pat -- TODO: Is this deterministic? Assuming so since it is ordered

childrenOfDef :: ExprContext -> DefGroup -> AEnv [ExprContext]
childrenOfDef ctx def =
  case def of
    DefNonRec d -> addContextId (\newId -> DefCNonRec newId ctx [defTName d] d) >>= (\x -> return [x])
    DefRec ds -> zipWithM (\i d -> addContextId (\newId -> DefCRec newId ctx (map defTName ds) i d)) [0..] ds

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
              DefCRec _ _ _ _ d -> childrenOfExpr ctx (defExpr d)
              DefCNonRec _ _ _ d -> childrenOfExpr ctx (defExpr d)
              LamCBody _ _ names body -> childrenOfExpr ctx body
              AppCLambda _ _ f -> childrenOfExpr ctx f
              AppCParam _ _ _ param -> childrenOfExpr ctx param
              LetCDef _ _ _ _ defg -> childrenOfDef ctx defg
              LetCBody _ _ _ e -> childrenOfExpr ctx e
              CaseCMatch _ _ e -> childrenOfExpr ctx e
              CaseCBranch _ _ _ _ b -> do
                x <- mapM (childrenOfExpr ctx . guardExpr) $ branchGuards b -- TODO Better context for branch guards
                return $ concat x
              ExprCBasic{} -> return []
              ExprCTerm{} -> return []
        addChildrenContexts parentCtxId newCtxs
        return newCtxs
    Just childIds -> do
      -- trace ("Got children for " ++ show ctx ++ " " ++ show childIds) $ return ()
      states <- states <$> getState
      return $ map (states Data.Map.!) (S.toList childIds)

visitChildrenCtxs :: ([a] -> a) -> ExprContext -> AEnv a -> AEnv a
visitChildrenCtxs combine ctx analyze = do
  children <- childrenContexts ctx
  -- trace ("Got children of ctx " ++ show ctx ++ " " ++ show children) $ return ()
  res <- mapM (\child -> withEnv (\e -> e{currentContext = child}) analyze) children
  return $ combine res