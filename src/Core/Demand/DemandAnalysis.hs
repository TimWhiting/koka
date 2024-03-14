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

module Core.Demand.DemandAnalysis(
  query,refine,qcall,qexpr,qeval,
  FixDemandR,FixDemand,State(..),DEnv(..),FixInput(..),FixOutput(..),Query(..),AnalysisKind(..),
  refineQuery,getEnv,withEnv,
  getQueryString,getState,updateState,getUnique,getAbValueResults,
  childrenContexts,analyzeEachChild,visitChildrenCtxs,
  createPrimitives,
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
import Core.Demand.StaticContext
import Core.Demand.AbstractValue
import Core.Demand.DemandMonad
import Core.Demand.FixpointMonad
import Syntax.Syntax (UserExpr, UserDef)
import qualified Syntax.Syntax as Syn
import Compile.Options (Flags (..), Terminal(..))
import Core.Core as C
import Type.Type
import Compile.Build (runBuild)
import Kind.Kind
import Data.Functor ((<&>))
import Common.Failure (assertion)

-- Refines a query given a more specific environment
refineQuery :: Query -> EnvCtx -> Query
refineQuery (CallQ (ctx, env0)) env = CallQ (ctx, env)
refineQuery (ExprQ (ctx, env0)) env = ExprQ (ctx, env)
refineQuery (EvalQ (ctx, env0)) env = EvalQ (ctx, env)

------------------------------ Environment FIXPOINT -----------------------------------

succAEnv :: ExprContext -> EnvCtx -> FixDemandR x s e Ctx
succAEnv newctx p' = do
  length <- contextLength <$> getEnv
  kind <- analysisKind <$> getEnv
  case kind of
    BasicEnvs -> return $ limitm (BCallCtx newctx (envhead p')) length

----------------- Unwrap/iterate over values within an abstract value and join results of subqueries ----------------------
doMaybe :: Maybe a -> (a -> FixDemandR x s e AChange) -> FixDemandR x s e AChange
doMaybe l doA = do
  maybe doBottom doA l

-- Convenience functions to set up the mutual recursion between the queries and unwrap the result
qcall :: (ExprContext, EnvCtx) -> FixDemandR x s e AChange
qcall c = query (CallQ c)
qexpr :: (ExprContext, EnvCtx) -> FixDemandR x s e AChange
qexpr c = query (ExprQ c)
qeval :: (ExprContext, EnvCtx) -> FixDemandR x s e AChange
qeval c = query (EvalQ c)

-- The main fixpoint loop
query :: Query -> FixDemandR x s e AChange
query q = do
  trace (show q) $ return ()
  res <- memo (QueryInput q) $ do
    let cq = newQuery q (\queryStr -> do
                trace (queryStr ++ show q) $ return ()
                x <- case q of
                        CallQ _ -> doCall q queryStr
                        ExprQ _ -> doExpr q queryStr
                        EvalQ _ -> doEval q queryStr  
                trace (queryStr ++ "==> " ++ show x) $ return x
                )
    let refined = do
          refine <- getRefine (queryEnv q)
          res <- query (refineQuery q refine)
          return $ FA res
    each [cq, refined]
  return $ toAChange res

refine :: EnvCtx -> FixDemandR x s e EnvCtx
refine env = do
  e <- memo (EnvInput env) doBottom
  return $ toEnv e

getRefine :: EnvCtx -> FixDemandR x s e EnvCtx
getRefine env =
  if isFullyDetermined env then doBottom else
  case env of
    EnvCtx cc tail -> 
        each [
          refine env,
          do
            tailRefine <- getRefine tail
            return (EnvCtx cc tailRefine)]
    EnvTail cc -> refine env

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
                buildc' <- liftIO (runBuild (term env) (flags env) (buildcTypeCheck [modName mod] bc))
                case buildc' of
                  Left err -> do
                    trace ("Error loading module " ++ show (modName mod) ++ " " ++ show err) $ return ()
                    return mod
                  Right (bc', e) -> do
                    let mod' = fromJust $ buildcLookupModule (modName mod) bc'
                    updateState (\state -> state{buildc = bc'})
                    return mod'
              else return mod
      return $ if lookupDefGroups (coreProgDefs $ fromJust $ modCoreUnopt mod') tn then Just (ModuleC ctxId mod' (modName mod'), Nothing) else trace ("External variable binding " ++ show tn ++ ": " ++ show vInfo) Nothing
    _ -> return Nothing


findAllUsage :: Bool -> Expr -> ExprContext -> EnvCtx -> FixDemandR x s e (ExprContext, EnvCtx)
findAllUsage first expr@Var{varName=tname@TName{getName = name}} ctx env = do
  case ctx of
    ModuleC{} -> do
      if nameStem name == "main" then return (ctx, env) else do
        mods <- buildcModules . buildc <$> getState
        let lds = mapMaybe (\m -> if modStatus m == LoadedSource then Just m else Nothing) mods
        each $ map (\m -> do
            let mdctx = modCtxOf m
            withEnv (\e -> e{currentModContext=mdctx, currentContext=mdctx}) $ findUsage first expr mdctx env
          ) lds
    _ -> findUsage first expr ctx env

-- TODO: Fix map example, not working for recursive call? 
-- finds usages of a variable expression within a (context,env) and returns the set of (context,env) pairs that reference it
findUsage :: Bool -> Expr -> ExprContext -> EnvCtx -> FixDemandR x s e (ExprContext, EnvCtx)
findUsage first expr@Var{varName=tname@TName{getName = name}} ctx env = do
  -- trace ("Looking for usages of " ++ show name ++ " in " ++ show ctx ++ " in env " ++ show env ++ " first " ++ show first) $ return ()
  let nameEq = (== name)
      childrenNoShadow tn =
        if first || tname `notElem` tn then childrenUsages else doBottom
      childrenUsages = do
        -- trace ("Looking for " ++ show name ++ " in " ++ show ctx ++ " in env " ++ show env) $ return ()
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
          doBottom
        else
          visitEachChild ctx $ do
            childCtx <- currentContext <$> getEnv
            m <- contextLength <$> getEnv
            findUsage False expr childCtx (limitmenv (EnvCtx (IndetCtx tn ctx) env) m)
      ExprCBasic _ c (Var{varName=TName{getName=name2}}) ->
        if nameEq name2 then do
          query <- getQueryString
          return $! trace (query ++ "Found usage in " ++ showContextPath ctx) (c, env)
        else
          -- trace ("Not found usage in " ++ show ctx ++ " had name " ++ show name2 ++ " expected " ++ show name) $ empty
          doBottom
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
    addPrimitive nameEffectOpen (\(ctx, env) -> do
            -- Open applied to some function results in that function
            trace ("OPEN Primitive: " ++ show ctx) $ return ()
            ctx' <- focusParam 0 ctx
            qeval (ctx', env)
          )
    addPrimitiveExpr nameEffectOpen (\i (ctx, env) -> do
        assertion ("EffectOpen: " ++ show i ++ " " ++ show ctx ++ " " ++ show env) (i == 0) $ return ()
        trace ("OPEN Primitive: " ++ show ctx) $ return ()
        -- Open's first parameter is a function and flows anywhere that the application flows to
        qexpr (fromJust $ contextOf ctx, env)
      )
  return ()

addPrimitive :: Name -> ((ExprContext,EnvCtx) -> FixDemandR x s e AChange) -> FixDemandR x s e ()
addPrimitive name m = do
  updateState (\state -> state{primitives = M.insert name m (primitives state)})

addPrimitiveExpr :: Name -> (Int -> (ExprContext,EnvCtx) -> FixDemandR x s e AChange) -> FixDemandR x s e ()
addPrimitiveExpr name m = do
  updateState (\state -> state{eprimitives = M.insert name m (eprimitives state)})

isPrimitive :: ExprContext -> FixDemandR x s e Bool
isPrimitive ctx = do
  prims <- primitives <$> getState
  case maybeExprOfCtx ctx of
    Just (Var tn _)  ->
      return $ M.member (getName tn) prims
    _ -> return False

evalPrimitive :: ExprContext -> ExprContext -> EnvCtx -> FixDemandR x s e AChange
evalPrimitive (ExprCBasic _ _ (Var tn _)) ctx env = do
  prims <- primitives <$> getState
  case M.lookup (getName tn) prims of
    Just m -> m (ctx, env)
    Nothing -> error ("evalPrimitive: Primitive not found! " ++ show tn)

exprPrimitive :: ExprContext -> Int -> ExprContext -> EnvCtx -> FixDemandR x s e AChange
exprPrimitive (ExprCBasic _ _ (Var tn _)) index ctx env = do
  prims <- eprimitives <$> getState
  case M.lookup (getName tn) prims of
    Just m -> m index (ctx, env)
    Nothing -> error ("exprPrimitive: Primitive not found! " ++ show tn)

doEval :: Query -> String -> FixDemandR x s e AChange
doEval cq@(EvalQ (ctx, env)) query = do
  case maybeExprOfCtx ctx of
    Nothing -> error "doEval: can't find expression"
    Just expr ->
      case expr of
        Lam{} -> -- LAM CLAUSE
          -- trace (query ++ "LAM: " ++ show ctx) $
          return $! AChangeClos ctx env
        v@(Var tn _) -> do -- REF CLAUSE
          prim <- isPrimitive ctx
          if prim then do
            trace (query ++ "REF: Primitive " ++ show tn) $ return ()
            return (AChangeClos ctx env)
          else do
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
                param <- focusParam index appctx
                qeval (param, appenv)
              BoundDef parentCtx ctx boundEnv index -> do
                param <- focusChild parentCtx index
                qeval (ctx, boundEnv)
              BoundDefRec parentCtx ctx boundEnv index -> do
                param <- focusChild parentCtx index
                qeval (ctx, boundEnv)
              BoundCase parentCtx caseCtx caseEnv branchIndex patBinding -> do
                mscrutinee <- focusChild parentCtx 0
                -- trace (query ++ "REF: scrutinee of case " ++ show scrutinee) $ return []
                evalPatternRef mscrutinee caseEnv patBinding
              BoundModule modulectx modenv -> do
                lamctx <- getTopDefCtx modulectx (getName tn)
                -- Evaluates just to the lambda
                qeval (lamctx, EnvTail TopCtx)
              BoundError e -> error "Binding Error"
              BoundGlobal _ _ -> do
                ext <- bindExternal v
                case ext of
                  Just (modulectx@ModuleC{}, index) -> do
                    lamctx <- getTopDefCtx modulectx (getName tn)
                    -- Evaluates just to the lambda
                    qeval (lamctx, EnvTail TopCtx)
                  _ -> error $ "REF: can't find what the following refers to " ++ show ctx
        App (TypeApp (Con nm repr) _) args rng -> do
          trace (query ++ "APPCon: " ++ show ctx) $ return []
          children <- childrenContexts ctx
          return $ AChangeConstr ctx env
        App (Con nm repr) args rng -> do
          trace (query ++ "APPCon: " ++ show ctx) $ return []
          children <- childrenContexts ctx
          return $ AChangeConstr ctx env
        App f tms rng -> do
          trace (query ++ "APP: " ++ show ctx) $ return []
          fun <- focusChild ctx 0
          -- trace (query ++ "APP: Lambda Fun " ++ show fun) $ return []
          AChangeClos lam lamenv <- qeval (fun, env)
          prim <- isPrimitive lam
          if prim then do
            trace (query ++ "APP: Primitive " ++ show lam) $ return ()
            evalPrimitive lam ctx env
          else do
            -- trace (query ++ "APP: Lambda is " ++ show lamctx) $ return []
            bd <- focusBody lam
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
              qeval (ctx',env)
        TypeLam{} ->
          trace (query ++ "TYPE LAM: " ++ show ctx) $
          case ctx of
            DefCNonRec{} -> return $! AChangeClos ctx env-- Don't further evaluate if it is just the definition / lambda
            DefCRec{} -> return $! AChangeClos ctx env-- Don't further evaluate if it is just the definition / lambda
            _ -> do
              ctx' <- focusChild ctx 0
              qeval (ctx',env)
        Lit l -> return $! injLit l env
        Let defs e -> do
          trace (query ++ "LET: " ++ show ctx) $ return []
          ex <- focusChild ctx 0 -- Lets have their return expression as first child
          qeval (ex, env)
        Case expr branches -> do
          trace (query ++ "CASE: " ++ show ctx) $ return []
          e <- focusChild ctx 0
          res <- qeval (e, env)
          evalBranches res ctx env (zip branches [0..])
        Con nm repr -> return $! AChangeConstr ctx env -- TODO: Check that the constructor is a singleton

--------------------------------- PATTERN EVALUATION HELPERS -----------------------------------------------
evalPatternRef :: ExprContext -> EnvCtx -> PatBinding -> FixDemandR x s e AChange
evalPatternRef expr env pat = do
  case pat of
    BoundPatVar _ -> qeval (expr, env)
    BoundPatIndex 0 b -> evalPatternRef expr env b -- Only support singleton patterns for now
    BoundConIndex con i b -> do
      AChangeConstr conApp cenv <- qeval (expr, env)
      let App (Con nm _) tms rng = exprOfCtx expr -- TODO: We should eval the f of the App to get to the actual constructor (past the type applications)
      if con /= nm then
        doBottom
      else do
        x <- focusChild conApp i
        evalPatternRef expr cenv pat

evalBranches :: AChange -> ExprContext -> EnvCtx -> [(Branch, Int)] -> FixDemandR x s e AChange
evalBranches ch ctx env branches =
  case branches of
    [] -> doBottom
    (Branch [p] _, i):xs -> do
      matches <- matchesPattern ch p
      if matches then do
        -- trace ("Found matching branch " ++ show p) $ return ()
        e <- focusChild ctx (i + 1) -- +1 to skip the scrutinee
        qeval (e, env)
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
        App (Con nm _) _ rng | nm == patConName ->
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
  case ctx of
    AppCLambda _ c e -> -- RATOR Clause
      -- trace (query ++ "OPERATOR: Application is " ++ showCtxExpr c) $
      return $ AChangeClos c env
    AppCParam _ c index e -> do -- RAND Clause 
      -- trace (query ++ "OPERAND: Expr is " ++ showCtxExpr ctx) $ return []
      fn <- focusChild c 0
      -- trace (query ++ "OPERAND: Evaluating To Closure " ++ showCtxExpr fn) $ return []
      AChangeClos lam lamenv <- qeval (fn, env)
      prim <- isPrimitive lam
      if prim then do
        trace (query ++ "OPERAND: Primitive " ++ show lam) $ return ()
        exprPrimitive lam index ctx env
      else do
        trace (query ++ "OPERAND: Closure is: " ++ showCtxExpr lam) $ return []
        bd <- focusBody lam
        -- trace (query ++ "OPERAND: Closure's body is " ++ showCtxExpr bd) $ return ()
        -- trace (query ++ "OPERAND: Looking for usages of operand bound to " ++ show (lamVar index lam)) $ return []
        succ <- succAEnv c env
        m <- contextLength <$> getEnv
        call <- findAllUsage True (lamVar index lam) bd (EnvCtx succ lamenv)
        -- trace (query ++ "RAND: Usages are " ++ show ctxs) $ return []
        qexpr call
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
      if isMain ctx then return $ AChangeClos c (EnvTail TopCtx) else qexpr call
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
      qexpr call
    ExprCBasic _ c _ -> error "Should never get here" -- qexpr (c, env)
    ModuleC{} -> do -- This is for calls to main
      trace (query ++ "Module: " ++ show ctx) $ return []
      return $ AChangeClos ctx env
    _ ->
      case contextOf ctx of
        Just c ->
          case enclosingLambda c of
            Just c' -> qexpr (c', env)
            _ -> error $ "Exprs has no enclosing lambda, so is always demanded (top level?) " ++ show ctx
        Nothing -> error $ "expressions where " ++ show ctx ++ " is demanded (should never happen)"

doCall :: Query -> String -> FixDemandR x s e AChange
doCall cq@(CallQ(ctx, env)) query =
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
            if cc1 `subsumesCtx` cc0 then
              trace (query ++ "KNOWN CALL: " ++ showSimpleCtx cc1 ++ " " ++ showSimpleCtx cc0)
              return $! AChangeClos callctx callenv
            else if cc0 `subsumesCtx` cc1 then do
              trace (query ++ "UNKNOWN CALL: " ++ showSimpleCtx cc1 ++ " " ++ showSimpleCtx cc0) $ return ()
              instantiate query (EnvCtx cc1 p) env
              doBottom
            else doBottom
              -- trace (query ++ "CALL IS NOT SUBSUMED:\n\nFIRST:" ++ show cc1 ++ "\n\nSECOND:" ++ show cc0) $ return ()
      _ -> error $ "CALL not implemented for " ++ show ctx

instantiate :: String -> EnvCtx -> EnvCtx -> FixDemandR x s e ()
instantiate query c1 c0 = if c1 == c0 then return () else do
  trace (query ++ "INST: " ++ showSimpleEnv c0 ++ " to " ++ showSimpleEnv c1) $ return ()
  lift $ push (EnvInput c0) (FE c1)
  return ()

--------------------------- TOP LEVEL QUERIES: RUNNING THE FIXPOINT ------------------------------

getAbValueResults :: Query -> PostFixR x s e [(EnvCtx, AbValue)]
getAbValueResults q = do
  refines <- getAllRefines (queryEnv q)
  mapM (\env ->
    do
      st <- getAllStates (refineQuery q env)
      return (env, st)
    ) (S.toList refines)

analyzeEachChild :: Show a => (ExprContext -> FixDemandR x s e a) -> ExprContext -> FixDemandR x s e a
analyzeEachChild analyze ctx = do
  let self = analyze ctx
      children = do
        visitEachChild ctx $ do
          childCtx <- currentContext <$> getEnv
          analyzeEachChild analyze childCtx
  each [self, children]

instance Label (FixOutput m) where
  label (A a) = ""
  label (E e) = ""
  label N = "⊥"

instance Label FixInput where
  label (QueryInput q) = show q
  label (EnvInput e) = "Env Refinements: " ++ show e