-----------------------------------------------------------------------------
-- Copyright 2024, Tim Whiting.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{-
    Check if a constructor context is well formed, and create a context path
-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Demand.DemandAnalysis(
  fixedEval,fixedExpr,fixedCall,loop,qcall,qexpr,qeval,
  FixDemandR,FixDemand,State(..),DEnv(..),FixInput(..),FixOutput(..),Query(..),AnalysisKind(..),
  refineQuery,getEnv,withEnv,
  getQueryString,getState,updateState,setResult,getUnique,
  childrenContexts,analyzeCtx,findContext,visitChildrenCtxs,
  createPrimitives,
  runEvalQueryFromRangeSource,
                        ) where
import GHC.IO (unsafePerformIO)
import Control.Monad hiding (join)
import Control.Monad.Reader (lift, ReaderT (runReaderT), local, ask)
import Control.Monad.Trans.Cont (ContT(runContT), resetT, shiftT, mapContT, evalContT, callCC, liftLocal)
import Control.Monad.State (StateT (..), MonadState (..), gets)
import Control.Monad.Identity (IdentityT, Identity (..))
import Control.Monad.Trans
import Common.Error
import Data.Set as S hiding (findIndex, filter, map)
import qualified Data.Sequence as Seq
import qualified Data.Map.Strict as M
import Data.Maybe (mapMaybe, isJust, fromJust, maybeToList, fromMaybe, catMaybes)
import Data.List (find, findIndex, elemIndex, union, intercalate)
import Common.Name
import Common.Range (Range, showFullRange, rangeNull)
import Common.NamePrim (nameOpen, nameEffectOpen)
import Compile.Module (Module(..), ModStatus (..), moduleNull)
import Compile.BuildContext (BuildContext(..), buildcLookupModule, buildcTypeCheck)
import Syntax.RangeMap
import Lib.PPrint (Pretty(..))
import Debug.Trace
import Demand.StaticContext
import Demand.AbstractValue
import Demand.DemandMonad
import Demand.FixpointMonad
import Demand.Syntax
import Syntax.Syntax (UserExpr, UserDef)
import qualified Syntax.Syntax as Syn
import Compile.Options (Flags (..), Terminal(..))
import Core.Core
import Core.Core as C
import Type.Type
import Compile.Build (runBuild)
import Kind.Kind

-- Refines a query given a more specific environment
refineQuery :: Query -> EnvCtx -> Query
refineQuery (CallQ (ctx, env0)) env = CallQ (ctx, env)
refineQuery (ExprQ (ctx, env0)) env = ExprQ (ctx, env)
refineQuery (EvalQ (ctx, env0)) env = EvalQ (ctx, env)

------------------------------ Environment FIXPOINT -----------------------------------

calibratem :: ExprContext -> EnvCtx -> FixDemandR x s e EnvCtx
calibratem call env = do
  length <- contextLength <$> getEnv
  return $ calibratemenv length (indeterminateStaticCtx call) env

tryCalibratem :: ExprContext -> EnvCtx -> FixDemandR x s e (Maybe EnvCtx)
tryCalibratem call env = do
  length <- contextLength <$> getEnv
  return $ tryCalibratemenv length (indeterminateStaticCtx call) env

succAEnv :: ExprContext -> EnvCtx -> FixDemandR x s e Ctx
succAEnv newctx p' = do
  length <- contextLength <$> getEnv
  kind <- analysisKind <$> getEnv
  case kind of
    BasicEnvs -> return $ limitm (BCallCtx newctx (envhead p')) length
    _ -> return $ CallCtx newctx (limitmenv p' (length - 1))

getRefine :: EnvCtx -> FixDemandR x s e (Maybe EnvCtx)
getRefine env =
  case env of
    EnvCtx cc tail -> do
      let f = if ccDetermined cc then return Nothing else
              do
                res <- loop (EnvInput env)
                return $ toEnv res
          t = do
                tailRefine <- getRefine tail
                case tailRefine of
                  Just tailRefine -> return $ Just (EnvCtx cc tailRefine)
                  Nothing -> return Nothing
      each [f,t]
    EnvTail cc ->
      do
        res <- loop (EnvInput env)
        return $ toEnv res

----------------- Unwrap/iterate over values within an abstract value and join results of subqueries ----------------------
doMaybe :: Maybe a -> (a -> FixDemandR x s e AChange) -> FixDemandR x s e AChange
doMaybe l doA = do
  case l of
    Just x -> doA x
    Nothing -> doBottom

-- Convenience functions to set up the mutual recursion between the queries and unwrap the result
qcall :: (ExprContext, EnvCtx) -> FixDemandR x s e AChange
qcall c = do
  res <- loop $ QueryInput (CallQ c)
  return $ toAbValue res
qexpr :: (ExprContext, EnvCtx) -> FixDemandR x s e AChange
qexpr c = do
  res <- loop $ QueryInput (ExprQ c)
  return $ toAbValue res
qeval :: (ExprContext, EnvCtx) -> FixDemandR x s e AChange
qeval c = do
  res <- loop $ QueryInput (EvalQ c)
  return $ toAbValue res

-- The main fixpoint loop
loop :: FixInput -> FixDemandR x s e AFixChange
loop fixinput = do
  memo fixinput $ \i ->
    case i of
      QueryInput cq ->
        case cq of
          EvalQ{} -> do
            newQuery cq (\queryStr -> do
                refine <- getRefine (queryEnv cq)
                doMaybe refine (\refine -> doEval (EvalQ (queryCtx cq, refine)) queryStr)
              )
          CallQ{} -> do
            newQuery cq (\queryStr -> do
                refine <- getRefine (queryEnv cq)
                doMaybe refine (\refine -> doCall (CallQ (queryCtx cq, refine)) queryStr)
              )
          ExprQ{} -> do
            newQuery cq (\queryStr -> do
                refine <- getRefine (queryEnv cq)
                doMaybe refine (\refine -> doExpr (ExprQ (queryCtx cq, refine)) queryStr)
              )
      EnvInput env -> return (FE env) -- TODO: Will this cause an infinite loop?

bindExternal :: Expr -> FixDemandR x s e (Maybe (ExprContext, Maybe Int))
bindExternal var@(Var tn@(TName name tp _) vInfo) = do
  bc <- buildc <$> getState
  env <- getEnv
  let deps = buildcModules bc
  let x = find (\m -> modName m == newName (nameModule name)) deps
  case x of
    Just mod -> do
      ctxId <- newModContextId mod
      mod' <- if modStatus mod == LoadedIface then do
        -- TODO: set some level of effort / time required for loading externals, but potentially load all core modules on startup
                buildc' <- liftIO (runBuild (term env) (flags env) (buildcTypeCheck [(modName mod)] bc))
                case buildc' of
                  Left err -> do
                    trace ("Error loading module " ++ show (modName mod) ++ " " ++ show err) $ return ()
                    return mod
                  Right (bc', e) -> do
                    let mod' = fromJust $ buildcLookupModule (modName mod) bc'
                    updateState (\state -> state{buildc = bc'})
                    return mod'
              else return mod
      return $ if lookupDefGroups (coreProgDefs $ fromJust $ modCore mod') tn then Just (ModuleC ctxId mod' (modName mod'), Nothing) else trace ("External variable binding " ++ show tn ++ ": " ++ show vInfo) Nothing
    _ -> return Nothing


findAllUsage :: Bool -> Expr -> ExprContext -> EnvCtx -> FixDemandR x s e (Maybe (ExprContext, EnvCtx))
findAllUsage first expr@Var{varName=tname@TName{getName = name}} ctx env = do
  case ctx of
    ModuleC{} -> do
      if nameStem name == "main" then return $ Just (ctx, env) else do
        mods <- buildcModules . buildc <$> getState
        let lds = mapMaybe (\m -> if modStatus m == LoadedSource then Just m else Nothing) mods
        each $ map (\m -> do
            let mdctx = modCtxOf m
            withEnv (\e -> e{currentModContext=mdctx, currentContext=mdctx}) $ findUsage first expr mdctx env
          ) lds
    _ -> findUsage first expr ctx env

-- TODO: Fix map example, not working for recursive call? 
-- finds usages of a variable expression within a (context,env) and returns the set of (context,env) pairs that reference it
findUsage :: Bool -> Expr -> ExprContext -> EnvCtx -> FixDemandR x s e (Maybe (ExprContext, EnvCtx))
findUsage first expr@Var{varName=tname@TName{getName = name}} ctx env = do
  trace ("Looking for usages of " ++ show name ++ " in " ++ show ctx ++ " in env " ++ show env ++ " first " ++ show first) $ return ()
  let nameEq = (== name)
      empty = return Nothing
      childrenNoShadow tn =
        if first || tname `notElem` tn then childrenUsages else return Nothing
      childrenUsages = do
        trace ("Looking for " ++ show name ++ " in " ++ show ctx ++ " in env " ++ show env) $ return ()
        visitEachChild ctx $ do
          -- visitChildrenCtxs sets the currentContext
          childCtx <- currentContext <$> getEnv
          findUsage False expr childCtx env in
    case ctx of
      LetCDef _ _ _ i d -> childrenNoShadow [defTName $ defOfCtx ctx]
      LetCBody _ _ tn _ -> childrenNoShadow tn
      DefCNonRec _ _ _ d -> childrenNoShadow [defTName $ defOfCtx ctx]
      DefCRec _ _ tn _ _ -> childrenNoShadow tn
      LamCBody _ _ tn _ ->
        -- No adding an IndetCtx because we are starting our search in the body itself
        if first then childrenUsages
        -- No usages if the name is shadowed
        else if tname `elem` tn then
          empty
        else
          visitEachChild ctx $ do
            childCtx <- currentContext <$> getEnv
            m <- contextLength <$> getEnv
            findUsage False expr childCtx (limitmenv (EnvCtx (IndetCtx tn ctx) env) m)
      ExprCBasic _ c (Var{varName=TName{getName=name2}}) ->
        if nameEq name2 then do
          query <- getQueryString
          return $! trace (query ++ "Found usage in " ++ showContextPath ctx) $
            return (c, env)
        else
          -- trace ("Not found usage in " ++ show ctx ++ " had name " ++ show name2 ++ " expected " ++ show name) $ empty
          empty
      ModuleC{} -> do
        visitEachChild ctx $ do
          -- visitChildrenCtxs sets the currentContext
          childCtx <- currentContext <$> getEnv
          findUsage first expr childCtx env
      _ -> childrenUsages

createPrimitives :: FixDemandR x s e ()
createPrimitives = do
  newModId <- newContextId
  let modName = newName "primitives"
      modCtx = ModuleC newModId (moduleNull modName) modName
  do
    let tvar = TypeVar 0 (kindFun kindStar kindStar) Bound
        x = TName (newName "x") (TVar tvar) Nothing
        lamExpr = Lam [x] effectEmpty (Var x InfoNone)
        def = makeDef nameEffectOpen (TypeLam [tvar] lamExpr)
        newCtx newId = DefCNonRec newId modCtx [defTName def] (C.DefNonRec def)
    ctx <- addContextId (\id -> newCtx id)
    addPrimitive nameEffectOpen ctx
  return ()

addPrimitive :: Name -> ExprContext -> FixDemandR x s e ()
addPrimitive name ctx = do
  updateState (\state -> state{primitives = M.insert name ctx (primitives state)})

getPrimitive :: TName -> FixDemandR x s e AChange
getPrimitive name = do
  prims <- primitives <$> getState
  case M.lookup (getName name) prims of
    Just ctx -> qeval (ctx, EnvTail TopCtx)
    Nothing -> error ("getPrimitive: " ++ show name)

doEval :: Query -> String -> FixDemandR x s e AChange
doEval cq@(EvalQ (ctx, env)) query = do
   trace (query ++ show cq) $ do
    case maybeExprOfCtx ctx of
      Nothing -> error $ "doEval: can't find expression"
      Just expr ->
        case expr of
          Lam{} -> -- LAM CLAUSE
            -- trace (query ++ "LAM: " ++ show ctx) $
            return $! AChangeClos ctx env
          v@(Var n _) | getName n == nameEffectOpen -> do
            getPrimitive n
          v@(Var tn _) -> do -- REF CLAUSE
          -- TODO: Consider static overloading
            -- trace (query ++ "REF: " ++ show ctx) $ return []
    -- REF: 
    --  - When the binding is focused on a lambda body, we need to find the callers of the lambda, and proceed as original formulation. 
    --  - When the binding is in the context of a Let Body we can directly evaluate the let binding as the value of the variable being bound (indexed to match the binding).
    --  - When the binding is in the context of a Let binding, it evaluates to that binding or the indexed binding in a mutually recursive group 
    --  - When the binding is a top level definition - it evaluates to that definition 
    --  - When the binding is focused on a match body then we need to issue a sub-query for the evaluation of the match expression that contributes to the binding, 
    --         and then consider the abstract value and find all abstract values that match the pattern of the branch in question 
    --         and only consider the binding we care about. 
    --         This demonstrates one point where a context sensitive shape analysis could propagate more interesting information along with the sub-query to disregard traces that don’t contribute
            -- trace (query ++ "REF: " ++ show ctx) $ return []
            let binded = bind ctx v env
            -- trace (query ++ "REF: " ++ show tn ++ " bound to " ++ show binded) $ return []
            case binded of
              BoundLam lamctx lamenv index -> do
                AChangeClos appctx appenv <- qcall (lamctx, lamenv)
                trace (query ++ "REF: found application " ++ showSimpleContext appctx ++ " " ++ showSimpleEnv appenv ++ " param index " ++ show index) $ return []
                param <- focusParam (Just index) appctx
                doMaybe param (\param -> qeval (param, appenv))
              BoundDef parentCtx ctx boundEnv index -> do
                param <- focusChild parentCtx index
                doMaybe param (\ctx -> qeval (ctx, boundEnv))
              BoundDefRec parentCtx ctx boundEnv index -> do
                param <- focusChild parentCtx index
                doMaybe param (\ctx -> qeval (ctx, boundEnv))
              BoundCase parentCtx caseCtx caseEnv branchIndex patBinding -> do
                mscrutinee <- focusChild parentCtx 0
                case mscrutinee of
                  Nothing -> error $ "REF: can't find scrutinee of case " ++ show ctx
                  Just scrutinee -> do
                    -- trace (query ++ "REF: scrutinee of case " ++ show scrutinee) $ return []
                    evalPatternRef scrutinee caseEnv patBinding
              BoundModule modulectx modenv -> do
                lamctx <- getTopDefCtx modulectx (getName tn)
                -- Evaluates just to the lambda
                qeval (lamctx, EnvTail TopCtx)
              BoundError e -> error $ "Binding Error"
              BoundGlobal _ _ -> do
                ext <- bindExternal v
                case ext of
                  Just (modulectx@ModuleC{}, index) -> do
                    lamctx <- getTopDefCtx modulectx (getName tn)
                    -- Evaluates just to the lambda
                    qeval (lamctx, EnvTail TopCtx)
                  _ -> error $ "REF: can't find what the following refers to " ++ show ctx
          App (TypeApp (Con nm repr) _) args -> do
            trace (query ++ "APPCon: " ++ show ctx) $ return []
            children <- childrenContexts ctx
            return $ AChangeConstr ctx env
          App (Con nm repr) args -> do
            trace (query ++ "APPCon: " ++ show ctx) $ return []
            children <- childrenContexts ctx
            return $ AChangeConstr ctx env
          App f tms -> do
            trace (query ++ "APP: " ++ show ctx) $ return []
            fun <- focusChild ctx 0
            case fun of
              Just fun -> do
                -- trace (query ++ "APP: Lambda Fun " ++ show fun) $ return []
                AChangeClos lam lamenv <- qeval (fun, env)
                -- trace (query ++ "APP: Lambda is " ++ show lamctx) $ return []
                bd <- focusBody lam
                case bd of
                  Just bd -> do
                    -- trace (query ++ "APP: Lambda body is " ++ show lamctx) $ return []
                    childs <- childrenContexts ctx
                    -- In the subevaluation if a binding for the parameter is requested, we should return the parameter in this context, 
                    succ <- succAEnv ctx env
                    let newEnv = EnvCtx succ lamenv
                    result <- qeval (bd, newEnv)
                    qeval (bd, newEnv)
          TypeApp{} ->
            trace (query ++ "TYPEAPP: " ++ show ctx) $
            case ctx of
              DefCNonRec{} -> return $! AChangeClos ctx env
              DefCRec{} -> return $! AChangeClos ctx env
              _ -> do
                ctx' <- focusChild ctx 0
                doMaybe ctx' (\ctx -> qeval (ctx,env))
          TypeLam{} ->
            trace (query ++ "TYPE LAM: " ++ show ctx) $
            case ctx of
              DefCNonRec{} -> return $! AChangeClos ctx env-- Don't further evaluate if it is just the definition / lambda
              DefCRec{} -> return $! AChangeClos ctx env-- Don't further evaluate if it is just the definition / lambda
              _ -> do
                ctx' <- focusChild ctx 0
                doMaybe ctx' (\ctx -> qeval (ctx,env))
          Lit l -> return $! injLit l env
          Let defs e -> do
            trace (query ++ "LET: " ++ show ctx) $ return []
            ex <- focusChild ctx 0 -- Lets have their return expression as first child
            doMaybe ex (\ex -> qeval (ex, env))
          Case expr branches -> do
            trace (query ++ "CASE: " ++ show ctx) $ return []
            e <- focusChild ctx 0
            doMaybe e (\e -> do
                res <- qeval (e, env)
                evalBranches res ctx env (zip branches ([0..]))
                -- case res of
                --   AChangeConstr con cenv -> do
                --     trace (query ++ "CASE: scrutinee is " ++ showCtxExpr con) $ return []
                --     -- return emptyAbValue
                --     trace (query ++ "CASE: Looking for branch matching " ++ show con) $ return ()
                --     branches <- findBranch con ctx cenv
                --     -- trace (query ++ "CASE: branches are " ++ show branches) $ return []
                --     -- TODO: Consider just the first branch that matches? Need to make sure that works with approximation
                --     each $ map (\branch -> qeval (branch, cenv)) branches
                --   AChangeLit lit cenv -> do
                --     -- trace (query ++ "CASE: result is " ++ show res) $ return []
                --     branches <- findBranchLit lit ctx
                --     trace (query ++ "CASE: branches' are " ++ show branches) $ return []
                --     each $ map (\branch -> qeval (branch, cenv)) branches
              )
          Con nm repr -> return $! AChangeConstr ctx env -- TODO: Check that the constructor is a singleton

--------------------------------- PATTERN EVALUATION HELPERS -----------------------------------------------
evalPatternRef :: ExprContext -> EnvCtx -> PatBinding -> FixDemandR x s e AChange
evalPatternRef expr env pat = do
  case pat of
    BoundPatVar _ -> qeval (expr, env)
    BoundPatIndex 0 b -> evalPatternRef expr env b -- Only support singleton patterns for now
    BoundConIndex con i b -> do
      AChangeConstr conApp cenv <- qeval (expr, env)
      let App (Con nm _) tms = exprOfCtx expr -- TODO: We should eval the f of the App to get to the actual constructor (past the type applications)
      if con /= nm then
        doBottom
      else do
        x <- focusChild conApp i
        case x of
          Nothing -> doBottom
          Just expr -> evalPatternRef expr cenv pat

evalBranches :: AChange -> ExprContext -> EnvCtx -> [(Branch, Int)] -> FixDemandR x s e AChange
evalBranches ch ctx env branches =
  case branches of
    [] -> doBottom
    (Branch [p] _, i):xs -> do
      matches <- matchesPattern ch p
      if matches then do
        -- trace ("Found matching branch " ++ show p) $ return ()
        e <- focusChild ctx (i + 1) -- +1 to skip the scrutinee
        doMaybe e (\e -> qeval (e, env))
      else evalBranches ch ctx env xs

matchesPattern :: AChange -> Pattern -> FixDemandR x s e Bool
matchesPattern ch pat =
  case ch of
    AChangeConstr conApp env -> matchesPatternConstr conApp env pat
    AChangeLit lit env -> return $ matchesPatternLit lit env pat

matchesPatternConstr :: ExprContext -> EnvCtx -> Pattern -> FixDemandR x s e Bool
matchesPatternConstr conApp env pat = do
  case pat of
    PatCon{patConName} ->
      case exprOfCtx conApp of
        App (Con nm _) _ | nm == patConName ->
          do
            childs <- childrenContexts conApp
            matchesPatternsCtx
              (Prelude.drop 1 childs) -- Drop the constructor
              (patConPatterns pat) env
        _ -> return False
    PatVar _ p -> matchesPatternConstr conApp env p
    PatWild -> return True
    _ -> return False

matchesPatternsCtx :: [ExprContext] -> [Pattern] -> EnvCtx -> FixDemandR x s e Bool
matchesPatternsCtx childrenCC pats env = do
  childrenEval <- mapM (\cc -> qeval (cc, env)) childrenCC
  res <- zipWithM (\ch subPat ->
    case ch of
      AChangeLit l env -> return $ matchesPatternLit l env subPat
      AChangeConstr con env -> matchesPatternConstr con env subPat
    ) childrenEval pats
  return $ and res

matchesPatternLit :: LiteralChange -> EnvCtx -> Pattern -> Bool
matchesPatternLit litc env pat =
  case pat of
    PatLit{} | pat `patSubsumed` litc -> True
    PatVar _ p -> matchesPatternLit litc env p
    PatWild -> True
    _ -> False


patSubsumed :: Pattern -> LiteralChange -> Bool
patSubsumed (PatLit (LitInt i)) (LiteralChangeInt (LChangeSingle x)) = i == x
patSubsumed (PatLit (LitFloat i)) (LiteralChangeFloat (LChangeSingle x)) = i == x
patSubsumed (PatLit (LitChar i)) (LiteralChangeChar (LChangeSingle x)) = i == x
patSubsumed (PatLit (LitString i)) (LiteralChangeString (LChangeSingle x)) = i == x
patSubsumed (PatLit (LitInt i)) (LiteralChangeInt LChangeTop) = True
patSubsumed (PatLit (LitFloat i)) (LiteralChangeFloat LChangeTop) = True
patSubsumed (PatLit (LitChar i)) (LiteralChangeChar LChangeTop) = True
patSubsumed (PatLit (LitString i)) (LiteralChangeString LChangeTop) = True
patSubsumed _ _ = False

-- TODO: This still sometimes returns emptyAbValue
doExpr :: Query -> String -> FixDemandR x s e AChange
doExpr cq@(ExprQ (ctx,env)) query = do
  trace (query ++ show cq) $ do
    case ctx of
      AppCLambda _ c e -> -- RATOR Clause
        -- trace (query ++ "OPERATOR: Application is " ++ showCtxExpr c) $
        return $ AChangeClos c env
      AppCParam _ c index e -> do -- RAND Clause 
        -- trace (query ++ "OPERAND: Expr is " ++ showCtxExpr ctx) $ return []
        fn <- focusChild c 0
        case fn of
          Just fn -> do
            -- trace (query ++ "OPERAND: Evaluating To Closure " ++ showCtxExpr fn) $ return []
            AChangeClos lam lamenv <- qeval (fn, env)
            -- trace (query ++ "OPERAND: Closure is: " ++ showCtxExpr lam) $ return []
            bd <- focusBody lam
            case bd of
              Nothing -> doBottom
              Just bd -> do
                -- trace (query ++ "OPERAND: Closure's body is " ++ showCtxExpr bd) $ return ()
                -- trace (query ++ "OPERAND: Looking for usages of operand bound to " ++ show (lamVar index lam)) $ return []
                succ <- succAEnv c env
                m <- contextLength <$> getEnv
                call <- findAllUsage True (lamVar index lam) bd (EnvCtx succ lamenv)
                -- trace (query ++ "RAND: Usages are " ++ show ctxs) $ return []
                doMaybe call qexpr
          Nothing -> doBottom
      LamCBody _ _ _ e -> do -- BODY Clause
        -- trace (query ++ "BODY: Looking for locations the returned closure is called " ++ show ctx) $ return []
        AChangeClos lamctx lamenv <- qcall (ctx, env)
        qexpr (lamctx, lamenv)
      ExprCTerm{} ->
        -- trace (query ++ "ends in error " ++ show ctx)
        -- return [(ctx, env)]
        error $ "Exprs led to ExprCTerm" ++ show ctx
      DefCNonRec _ c index _ -> do
        trace (query ++ "DEF NonRec: Env is " ++ show env) $ return []
        let df = defOfCtx ctx
        call <- case c of
          ModuleC{} -> do
            trace (query ++ "DEF NonRec: In module binding " ++ show c ++ " looking for usages of " ++ show (lamVarDef df)) $ return ()
            findAllUsage True (lamVarDef df) c env
          _ -> do
            trace (query ++ "DEF NonRec: In other binding " ++ show c ++ " looking for usages of " ++ show (lamVarDef df)) $ return ()
            findAllUsage True (lamVarDef df) (fromJust $ contextOf c) env
        -- trace (query ++ "DEF: Usages are " ++ show ctxs) $ return []
        if isMain ctx then return $ AChangeClos c env else doMaybe call qexpr
        -- doMaybe call qexpr
      DefCRec _ c _ _ _ -> do
        trace (query ++ "DEF Rec: Env is " ++ show env) $ return []
        let df = defOfCtx ctx
        call <- case c of
          ModuleC{} -> do
            trace (query ++ "DEF Rec: In module binding " ++ show c ++ " looking for usages of " ++ show (lamVarDef df)) $ return ()
            findAllUsage True (lamVarDef df) c env
          _ -> do
            trace (query ++ "DEF Rec: In other binding " ++ show c ++ " looking for usages of " ++ show (lamVarDef df)) $ return ()
            findAllUsage True (lamVarDef df) (fromJust $ contextOf c) env
        -- trace (query ++ "DEF: Usages are " ++ show ctxs) $ return []
        doMaybe call qexpr
      ExprCBasic _ c _ -> error "Should never get here" -- qexpr (c, env)
      _ ->
        case contextOf ctx of
          Just c ->
            case enclosingLambda c of
              Just c' -> qexpr (c', env)
              _ -> error $ "Exprs has no enclosing lambda, so is always demanded (top level?) " ++ show ctx
          Nothing -> error $ "expressions where " ++ show ctx ++ " is demanded (should never happen)"

doCall :: Query -> String -> FixDemandR x s e AChange
doCall cq@(CallQ(ctx, env)) query =
  trace (query ++ show cq) $ do
    -- TODO: Treat top level functions specially in call, not in expr
      case ctx of
          LamCBody _ c _ _-> do
            kind <- analysisKind <$> getEnv
            case kind of
              BasicEnvs -> do
                let cc0 = envhead env
                    p = envtail env
                AChangeClos callctx callenv <- qexpr (c, p)
                m <- contextLength <$> getEnv
                cc1 <- succAEnv callctx callenv
                if cc1 == cc0 then
                  trace (query ++ "KNOWN CALL: " ++ showSimpleCtx cc1 ++ " " ++ showSimpleCtx cc0)
                  return $! AChangeClos callctx callenv
                else if cc0 `subsumesCtx` cc1 then do
                  trace (query ++ "UNKNOWN CALL: " ++ showSimpleCtx cc1 ++ " " ++ showSimpleCtx cc0) $ return ()
                  instantiate query (EnvCtx cc1 p) env
                  doBottom
                else do
                  -- trace (query ++ "CALL IS NOT SUBSUMED:\n\nFIRST:" ++ show cc1 ++ "\n\nSECOND:" ++ show cc0) $ return ()
                  doBottom
              LightweightEnvs -> do
                -- Lightweight Version
                case envhead env of
                  (CallCtx callctx p') -> do
                    trace (query ++ "Known: " ++ show callctx) $ return ()
                    pnew <- calibratem callctx p'
                    return $ AChangeClos callctx pnew
                  _ -> do
                    trace (query ++ "Unknown") $ return ()
                    qexpr (c, envtail env)
              HybridEnvs -> do
                -- Hybrid Version
                let fallback = do
                      let cc0 = envhead env
                          p = envtail env
                      AChangeClos callctx callenv <- qexpr (c, p)
                      m <- contextLength <$> getEnv
                      cc1 <- succAEnv callctx callenv
                      if cc1 == cc0 then
                        trace (query ++ "KNOWN CALL: " ++ showSimpleCtx cc1 ++ " " ++ showSimpleCtx cc0)
                        return $! AChangeClos callctx callenv
                      else if cc0 `subsumesCtx` cc1 then do
                        trace (query ++ "UNKNOWN CALL: " ++ showSimpleCtx cc1 ++ " " ++ showSimpleCtx cc0) $ return ()
                        instantiate query (EnvCtx cc1 p) env
                        doBottom
                      else do
                        trace (query ++ "CALL IS NOT SUBSUMED:") $ return () -- \n\nFIRST:" ++ show cc1 ++ "\n\nSECOND:" ++ show cc0) $ return ()
                        doBottom
                case envhead env of
                  (CallCtx callctx p') -> do
                    pnew <- tryCalibratem callctx p'
                    case pnew of
                      Just pnew -> do
                        trace (query ++ "Known: " ++ show callctx) $ return ()
                        return $ AChangeClos callctx pnew
                      Nothing -> fallback
                  _ -> fallback
          _ -> error $ "CALL not implemented for " ++ show ctx

instantiate :: String -> EnvCtx -> EnvCtx -> FixDemandR x s e ()
instantiate query c1 c0 = if c1 == c0 then return () else do
  trace (query ++ "INST: " ++ showSimpleEnv c0 ++ " to " ++ showSimpleEnv c1) $ return ()
  loop (EnvInput c0)
  push (EnvInput c0) (FE c1)
  return ()

--------------------------- TOP LEVEL QUERIES: RUNNING THE FIXPOINT ------------------------------
fixedEval :: ExprContext -> EnvCtx -> FixDemandR x s e [(EnvCtx, AbValue)]
fixedEval e env = do
  let q = EvalQ (e, env)
  loop (QueryInput q)
  refines <- getAllRefines env
  res <- mapM (\env ->
    do
      st <- getAllStates (EvalQ (e, env))
      return (env, st)
    ) (S.toList refines)
  trace "Finished eval" $ return ()
  return res

fixedExpr :: ExprContext -> EnvCtx -> FixDemandR x s e [(ExprContext, EnvCtx)]
fixedExpr e env = do
  let q = ExprQ (e, env)
  loop (QueryInput q)
  refines <- getAllRefines env
  res <- mapM (\env ->
    do
      st <- getAllStates (ExprQ (e, env))
      return (e, env)
    ) (S.toList refines)
  trace "Finished expr" $ return ()
  return res

fixedCall :: ExprContext -> EnvCtx -> FixDemandR x s e [(ExprContext, EnvCtx)]
fixedCall e env = do
  let q = CallQ (e, env)
  loop (QueryInput q)
  refines <- getAllRefines env
  res <- mapM (\env ->
    do
      st <- getAllStates (CallQ (e, env))
      return (e, env)
    ) (S.toList refines)
  trace "Finished call" $ return ()
  return res

getAbResult :: (EnvCtx, AbValue) -> FixDemandR x s e (EnvCtx, ([UserExpr], [UserDef], [Syn.Lit], [String], Set Type))
getAbResult (envctx, res) = do
  let vals = [res]
      lams = map fst $ concatMap (S.toList . aclos) vals
      i = concatMap ((mapMaybe toSynLit . M.elems) . intV) vals
      f = concatMap ((mapMaybe toSynLitD . M.elems) . floatV) vals
      c = concatMap ((mapMaybe toSynLitC . M.elems) . charV) vals
      s = concatMap ((mapMaybe toSynLitS . M.elems) . stringV) vals
      topTypes = unions $ map topTypesOf vals
      vs = i ++ f ++ c ++ s
      cs = map fst $ concatMap (S.toList . acons) vals
  consts <- mapM toSynConstr cs
  sourceLams <- mapM findSourceExpr lams
  let (sourceLambdas, sourceDefs) = unzip sourceLams
  return $ trace ("eval result:\n----------------------\n" ++ showSimpleAbValue res ++ "\n----------------------\n") (envctx, (catMaybes sourceLambdas, catMaybes sourceDefs, vs, catMaybes consts, topTypes))

runEvalQueryFromRangeSource :: BuildContext
  -> Terminal -> Flags -> (Range, RangeInfo) -> Module -> AnalysisKind -> Int
  -> IO (Maybe ([(EnvCtx, ([UserExpr], [UserDef], [Syn.Lit], [String], Set Type))], BuildContext))
runEvalQueryFromRangeSource bc term flags rng mod kind m = do
  (r, lattice, x) <- runQueryAtRange bc term flags rng mod kind m $ \exprctxs ->
        case exprctxs of
          exprctx:rst -> do
            trace ("evaluating " ++ show exprctx) $ return ()
            createPrimitives
            ress <- fixedEval exprctx (indeterminateStaticCtx exprctx)
            res' <- mapM getAbResult ress
            buildc' <- buildc <$> getState
            setResult (res', buildc')
          _ ->
            setResult ([(EnvTail CutUnknown, ([],[],[],[],S.empty))], bc)
  return $ trace (show lattice) x

runQueryAtRange :: BuildContext
  -> Terminal -> Flags -> (Range, RangeInfo)
  -> Module -> AnalysisKind -> Int
  -> ([ExprContext] -> FixDemand x () ())
  -> IO ((FixOutput AFixChange), M.Map FixInput (FixOutput AFixChange), Maybe x)
runQueryAtRange buildc term flags (r, ri) mod kind m query = do
  let cid = ExprContextId (-1) (modName mod)
      modCtx = ModuleC cid mod (modName mod)
      focalContext = analyzeCtx (\parentRes childRes -> case concat childRes of {x:_ -> [x]; _ -> parentRes}) (const $ findContext r ri) modCtx
  result <- runFix (focalContext >>= query) (DEnv m term flags kind modCtx modCtx (EnvTail TopCtx) "" "" ()) (State buildc M.empty 0 M.empty 0 Nothing M.empty ())
  return $ case result of
    (a, b, s) -> (a, b, finalResult s)

findContext :: Range -> RangeInfo -> FixDemandR x s e [ExprContext]
findContext r ri = do
  ctx <- currentContext <$> getEnv
  case ctx of
    ExprCBasic _ _ (Var (TName _ _ (Just rng)) _) | r `rangesOverlap` rng -> trace ("found overlapping range " ++ showFullRange "" rng ++ " " ++ show ctx) $ return [ctx]
    ExprCBasic _ _ (Var (TName _ _ (Just rng)) _) -> -- trace ("var range doesn't overlap "++ show ctx ++ " " ++ showFullRange rng) $
      return []
    LetCDef{} -> fromNames ctx [defTName (defOfCtx ctx)]
    -- Hovering over a lambda parameter should query what values that parameter can evaluate to -- need to create an artificial Var expression
    LamCBody _ _ tnames _ -> fromNames ctx tnames
    CaseCBranch _ _ tnames _ _ -> fromNames ctx tnames
    _ -> return []
  where fromNames ctx tnames =
          case mapMaybe (\tn -> (case fmap (rangesOverlap r) (originalRange tn) of {Just True -> Just tn; _ -> Nothing})) tnames of
              [tn] -> do
                id <- newContextId
                return [ExprCBasic id ctx (Var tn InfoNone)]
              _ -> return []

analyzeCtx :: (a -> [a] -> a) -> (ExprContext -> FixDemandR x s e a) -> ExprContext -> FixDemandR x s e a
analyzeCtx combine analyze ctx = do
  -- id <- currentContext <$> getEnv
  -- trace ("Analyzing ctx " ++ show ctx ++ " with id " ++ show (exprId id)) $ return ()
  res <- analyze ctx
  visitChildrenCtxs (combine res) ctx $ do
    childCtx <- currentContext <$> getEnv
    analyzeCtx combine analyze childCtx