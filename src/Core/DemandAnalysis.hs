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
import Core.Core (Expr (..), CorePhase, liftCorePhaseUniq, DefGroups, Def (..), DefGroup (..), liftCorePhaseRes, Branch (..), Guard(..), Pattern(..), TName (..), defsTNames, defGroupTNames, mapDefGroup, Core (..), VarInfo (..), liftCorePhase, defTName, makeDef)
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
import Compiler.Module (Loaded (..), Module (..))
import Lib.PPrint (Pretty(..))
import Type.Pretty (ppType, defaultEnv, Env (..))
import Kind.Kind (Kind(..), kindFun, kindStar)
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
  | DefCRec ExprContextId ExprContext [TName] Int Def -- A recursive definition context, working on the index'th definition
  | DefCNonRec ExprContextId ExprContext [TName] Def -- In a non recursive definition context, working on Def
  | LamCBody ExprContextId ExprContext [TName] Expr -- Inside a lambda body expression
  | AppCLambda ExprContextId ExprContext Expr -- Application context inside function context
  | AppCParam ExprContextId ExprContext Int Expr -- Application context inside param context
  | LetCDef ExprContextId ExprContext [TName] Int DefGroup -- In a let definition context working on a particular defgroup
  | LetCBody ExprContextId ExprContext [TName] Expr -- In a let body expression
  | CaseCMatch ExprContextId ExprContext Expr -- In a case match context working on the match expression (assumes only one)
  | CaseCBranch ExprContextId ExprContext [TName] Int Branch -- Which branch currently inspecting, as well as the Case context
  | ExprCBasic ExprContextId ExprContext Expr -- A basic expression context that has no sub expressions
  | ExprCTerm ExprContextId String -- Since analysis can fail or terminate early, keep track of the query that failed


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

lamVar :: ExprContext -> Expr
lamVar ctx =
  case maybeExprOfCtx ctx of
    Just (Lam names _ _) -> Var (head names) InfoNone
    _ -> trace ("DemandAnalysis.lamVar: not a lambda" ++ show ctx) error "Not a lambda"

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
    LetCDef _ _ _ _ dg -> error "LetCDef has no single expr"
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

newtype AEnv a = AEnv (DEnv -> State -> Result a)
data State = State{states :: Map ExprContextId ExprContext, childrenIds :: Map ExprContextId (Set ExprContextId), memoCache :: Map String (Map ExprContextId (Set ExprContext)), unique :: Int}
data Result a = Ok a State

data DEnv = DEnv{
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
        AEnv f -> f (DEnv loaded modCtx cid "" "") (State Data.Map.empty Data.Map.empty (Data.Map.fromList [("eval", Data.Map.empty), ("call", Data.Map.empty), ("expr", Data.Map.empty) ]) 0)
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
bind :: ExprContext -> Expr -> Maybe (ExprContext, Maybe Int)
bind ctx var@(Var tname vInfo) =
  case ctx of
    ModuleC _ mod _ -> if lookupDefGroups (coreProgDefs $ modCoreNoOpt mod) tname then Just (ctx, Nothing) else trace ("External variable binding " ++ show tname ++ ": " ++ show vInfo) Nothing
    DefCRec _ ctx' names i d -> lookupName names ctx'
    DefCNonRec _ ctx' names d -> lookupName names ctx'
    LamCBody _ ctx' names _  -> lookupName names ctx'
    AppCLambda _ ctx _ -> bind ctx var
    AppCParam _ ctx _ _ -> bind ctx var
    LetCDef _ ctx' names i _ -> lookupName names ctx'
    LetCBody _ ctx' names _ -> lookupName names ctx'
    CaseCMatch _ ctx _ -> bind ctx var
    CaseCBranch _ ctx' names _ b -> lookupName names ctx'
    ExprCBasic _ ctx _ -> bind ctx var
    ExprCTerm{} -> Nothing
  where
    lookupName names ctx' =
      case elemIndex tname names
    -- special case this instead of using lookup name since the function is the first index in contexts when we lookup the parameter
    -- TODO: Figure out a better way of doing this
        of Just x -> Just (ctx, Just x)
           _ -> bind ctx' var


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
    DefCRec _ _ _ _ d -> if nameEq $ defName d then empty else childrenUsages -- TODO: Consider index
    DefCNonRec _ _ _ d -> if nameEq $ defName d then empty else childrenUsages
    LamCBody _ _ names _ -> if any (nameEq . getName) names then empty else childrenUsages
    LetCDef _ _ _ _ d -> if any (nameEq . defName) (defsOf d) then empty else childrenUsages
    CaseCBranch _ _ _ _ b -> if branchContainsBinding b tname then empty else childrenUsages
    ExprCBasic id _ Var{varName=TName{getName=name2}} ->
      if nameEq name2 then do
        query <- getQueryString
        return $ trace (query ++ "Found usage in " ++ show (fromJust $ contextOf ctx)) $ S.singleton (fromJust $ contextOf ctx)
      else
        -- trace ("Not found usage in " ++ show ctx ++ " had name " ++ show name2 ++ " expected " ++ show name) $ empty
        empty
    _ -> childrenUsages

findUsage2 :: String -> Expr -> ExprContext -> AEnv [ExprContext]
findUsage2 query e ctx = do
  usage <- withQuery query $ findUsage e ctx
  return $ -- trace ("Looking for usages of " ++ show e ++ " in " ++ show ctx ++ " got " ++ show usage) 
    S.toList usage

doAEnvList :: String -> AEnv [a] -> ListT AEnv a
doAEnvList query f = do
  xs <- liftWithQuery query f
  L.fromFoldable xs

doAEnv :: String -> AEnv a -> ListT AEnv a
doAEnv query f = do
  liftWithQuery query f

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
  trace (query ++ "Eval " ++ show ctx ++ " expr: " ++ show (exprOfCtx ctx)) $
    wrapMemo "eval" ctx $
    case exprOfCtx ctx of
      Lam{} -> -- LAM CLAUSE
        trace (query ++ "LAM: " ++ show ctx) $
        return ctx 
      v@(Var n _) | getName n == nameEffectOpen -> do -- TODO: Reevaluate eventually
        trace (query ++ "OPEN: " ++ show ctx) $ return []
        newId <- lift newContextId
        let tvar = TypeVar 0 (kindFun kindStar kindStar) Bound 
            x = TName (newName "x") (TVar tvar) Nothing
            def = makeDef nameEffectOpen (TypeLam [tvar] (Lam [x] effectEmpty (Var x InfoNone)))
            newCtx = DefCNonRec newId ctx [defTName def] def
        -- _ <- doAEnv query $ childrenContexts newCtx
        return newCtx
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
        trace (query ++ "REF: " ++ show ctx) $ return []
        let binded = bind ctx v
        trace (query ++ "REF: bound to " ++ show binded) $ return []
        case binded of
          Just (lambodyctx@LamCBody{}, index) -> do
            appctx <- call lambodyctx
            param <- doAEnvMaybe query $ focusParam index appctx
            eval param
          Just (letbodyctx@LetCBody{}, index) ->
            eval =<< doAEnvMaybe query (focusChild (fromJust $ contextOf letbodyctx) (fromJust index))
          Just (letdefctx@LetCDef{}, index) -> 
            eval =<< doAEnvMaybe query (focusChild (fromJust $ contextOf letdefctx) (fromJust index))
          Just (matchbodyctx@CaseCBranch{}, index) -> do
            -- TODO:
            let msg = query ++ "REF: TODO: Match body context " ++ show v ++ " " ++ show matchbodyctx
            trace msg $ newErrTerm msg
          Just (modulectx@ModuleC{}, index) -> do
            lamctx <- doAEnv query $ getDefCtx modulectx (getName tn)
            -- Evaluates just to the lambda
            eval lamctx
          Just (ctxctx, index) -> do
            children <- lift (childrenContexts ctxctx)
            let msg = query ++ "REF: unexpected context in result of bind: " ++ show v ++ " " ++ show ctxctx ++ " children: " ++ show children
            trace msg $ newErrTerm msg
          Nothing ->
            newErrTerm $ "REF: currently doesn't support external variables such as " ++ show ctx
      App f tms -> do
        fun <- doAEnvMaybe query $ focusChild ctx 0
        trace (query ++ "APP: Lambda Fun " ++ show fun) $ return []
        -- case fun of
          -- ExprCBasic _ _ (Var n i) | getName n == nameEffectOpen ->
          --   doAEnvMaybe query (focusChild (fromJust $ contextOf $ fromJust $ contextOf ctx) 1) >>= eval
          -- _ -> do
        lamctx <- eval fun
        trace (query ++ "APP: Lambda is " ++ show lamctx) $ return []
        bd <- doAEnvMaybe query $ focusBody lamctx
        trace (query ++ "APP: Lambda body is " ++ show lamctx) $ return []
        eval bd 
        -- TODO: In the subevaluation if a binding for the parameter is requested, we should return the parameter in this context, 
        -- additionally, in any recursive contexts (a local find from the body of the lambda)
      TypeApp{} -> 
        case ctx of
          DefCNonRec{} -> return ctx 
          DefCRec{} -> return ctx 
          _ -> do
            ctx' <- doAEnvMaybe query $ focusChild ctx 0
            eval ctx'
      TypeLam{} -> 
        case ctx of
          DefCNonRec{} -> return ctx -- Don't further evaluate if it is just the definition / lambda
          DefCRec{} -> return ctx -- Don't further evaluate if it is just the definition / lambda
          _ -> do
            ctx' <- doAEnvMaybe query $ focusChild ctx 0
            eval ctx'
      _ -> 
        let msg =  (query ++ "TODO: Not Handled Eval: " ++ show ctx ++ " expr: " ++ show (exprOfCtx ctx)) in
        trace msg $ newErrTerm msg
        -- case ctx of -- APP CLAUSE
        --   ExprCTerm{} ->
        --     trace (query ++ "Eval ends in error " ++ show ctx)
        --     return ctx
          -- AppCLambda{} -> do
            
          -- _ -> do
          --   app <- liftWithQuery query $ isApp ctx
          --   if app then do
          --     trace (query ++ "Eval app " ++ show ctx) $ return []
          --     fn <- doAEnvMaybe query $ focusFun ctx
          --     case fn of
          --       (ExprCBasic _ _ (Var n i)) | getName n == nameEffectOpen -> do
          --         trace (query ++ "Is open") $ return []
          --         arg <- doAEnvMaybe query $ focusParam (Just 1) (fromJust $ contextOf ctx)
          --         eval arg
          --       _ -> do
          --         trace (query ++ "Is app not open") $ return []
          --         lamctx <- eval fn
          --         bd <- doAEnvMaybe query $ focusBody lamctx
          --         eval bd
          --   else do
          -- _ ->
          --   trace (query ++ "unhandled eval type " ++ show ctx) $ return ctx

newErrTerm :: String -> ListT AEnv ExprContext
newErrTerm s = lift $ do
  newId <- newContextId
  return $ ExprCTerm newId ("Error: " ++ s)

-- CALL / EXPR: CALL as mentioned in the Context Sensitivity paper just relates a LAMBDA body
-- context to and expression that relates the enclosing context to applications that bind the lambda’s
-- variables. This can be trivially included without a separate call relation by in BIND focusing on the
-- lambda body’s parent context.
-- EXPR’s purpose is to relate a context which has as it’s expression a lambda, to the places where
-- that lambda’s is called (and thus it’s variables bound).
-- The above rules for ref make it impossible for eval to ask for a call / expr relation for Lets /
-- Matches and Top Level Defs. i.e. the expression demanded always is a context whose expression is
-- a lambda or var
-- Top level definitions should never require expr, since their bindings are resolved already during
-- the REF. However, an initial query of the CALLs / EXPRs of a top level definition could be made. As
-- such an call on a TLD delegates immediately to expr, which then just issues a find query over the
-- program. To prevent this from becoming too expensive, a module import graph should be used to
-- work our way to only those modules that demand the current module and the symbol in question
-- is in the import scope. This is the same rule that should happen for FIND in general
doExpr :: (ExprContext -> ListT AEnv ExprContext) -> (ExprContext -> ListT AEnv ExprContext) -> (ExprContext -> ListT AEnv ExprContext) -> ExprContext -> ListT AEnv ExprContext
doExpr eval expr call ctx = do
  query <- lift queryId
  trace (query ++ "Expr " ++ show ctx ++ " parent " ++ show (contextOf ctx))
    wrapMemo "expr" ctx $
    case ctx of
      AppCLambda _ c e -> -- RATOR Clause
        trace (query ++ "RATOR: Expr is " ++ show ctx) $
        return c
      AppCParam _ c _ e -> do -- RAND Clause 
        trace (query ++ "RAND: Expr is " ++ show ctx) $ return []
        fn <- doAEnvMaybe query $ focusFun c 
        trace (query ++ "RAND: Fn is " ++ show fn) $ return []
        ctxlam <- eval fn
        trace (query ++ "RAND: Lam is " ++ show ctxlam) $ return []
        bd <- doAEnvMaybe query $ focusBody ctxlam
        trace (query ++ "RAND: Lam body is " ++ show bd) $ return []
        ctx' <- lift $ findUsage2 query (lamVar ctxlam) bd
        L.fromFoldable ctx' >>= expr
      LamCBody _ _ _ e -> do -- BODY Clause
-- The expr rule creates new expr relations in a nonspecific context during the second half
-- of the BOD rule. This happens when the lambda is returned from the body of an expression. The
-- initial context for BOD is not necessarily an immediate lambda body context as expected by the
-- call relation, due to intermediate contexts including local let bindings. As such we need to take
-- the context and work outwards on the contexts until we find the nearest lambda body context
-- (returning immediately if it is already the case). Then we use this context to demand expressions.
-- The body’s precondition then is either being a Basic Expression, or already a Lambda Body Context.
-- The Basic Expressions we work outwards, prior to the call. (Note this doesn't change the body rule at all just changes the ExprCBasic case)
        trace (query ++ "BODY: Expr is " ++ show ctx) $ return []
        ctxlambody <- call ctx
        expr ctxlambody
      ExprCBasic _ c _ -> 
        trace (query ++ "EXPR: basic " ++ show ctx) $
        case enclosingLambda c of
          Just c' -> expr c'  --
          _ -> newErrTerm "Exprs has no enclosing lambda, so is always demanded (top level?)"
      LetCBody{} -> do
        newErrTerm $ "Exprs where let body " ++ show ctx ++ " is demanded"
      LetCDef{} -> do
        newErrTerm $ "Exprs where let def " ++ show ctx ++ " is demanded"
      CaseCMatch{} -> do
        newErrTerm $ "Exprs where case match " ++ show ctx ++ " is demanded"
      CaseCBranch{} -> do
        newErrTerm $ "Exprs where case branch " ++ show ctx ++ " is demanded"
      DefCRec{} -> do
        newErrTerm $ "Exprs where recursive def " ++ show ctx ++ " is demanded"
      DefCNonRec _ c _ d -> do
        trace (query ++ "EXPR: DefNonRec " ++ show ctx) $ return []
        ctx' <- lift $ findUsage2 query (lamVarDef d) c
        L.fromFoldable ctx' >>= expr
        -- trace ("Expr def non rec results " ++ show ctx') $ 
      ModuleC _ _ nm -> newErrTerm $ "expressions where module " ++ show nm ++ " is demanded (should never happen - Module is not an expression)"
      ExprCTerm{} ->
        trace (query ++ "Expr ends in error " ++ show ctx)
        return ctx

doCall :: (ExprContext -> ListT AEnv ExprContext) -> (ExprContext -> ListT AEnv ExprContext) -> (ExprContext -> ListT AEnv ExprContext) -> ExprContext -> ListT AEnv ExprContext
doCall eval expr call ctx =
  wrapMemo "call" ctx $ do
  query <- lift queryId
  trace (query ++ "Call " ++ show ctx) $ 
    -- case contextOf ctx of 
    --   Just x -> expr x
    --   Nothing -> newErrTerm $ "call not implemented for " ++ show ctx 
   case ctx of
      LamCBody _ c _ _-> expr c
      ExprCTerm{} ->
        trace (query ++ "Call ends in error " ++ show ctx)
        return ctx
      DefCNonRec _ c _ d -> do
        ctx' <- lift $ findUsage2 query (lamVarDef d) c
        L.fromFoldable ctx' >>= expr
      _ -> newErrTerm $ "call not implemented for " ++ show ctx

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
              _ -> error $ "childrenContexts: " ++ show ctx
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