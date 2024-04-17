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
  refineQuery,getEnv,withEnv,succAEnv,
  getQueryString,getState,updateState,getUnique,getAbValueResults,
  childrenContexts,analyzeEachChild,visitChildrenCtxs,addPrimitive,addPrimitiveExpr,evalParam,
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
import Common.NamePrim (nameOpen, nameEffectOpen, nameIntAdd, nameCoreHnd)
import Compile.Module (Module(..), ModStatus (..), moduleNull, modImportNames)
import Compile.BuildContext (BuildContext(..), buildcLookupModule, buildcTypeCheck)
import Syntax.RangeMap
import Lib.PPrint (Pretty(..))
import qualified Lib.PPrint as P
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

evalParam :: Int -> ExprContext -> EnvCtx -> FixDemandR x s e AChange
evalParam i ctx env = do
  param <- focusParam i ctx
  qeval (param, env)

-- The main fixpoint loop
query :: Query -> FixDemandR x s e AChange
query q = do
  res <- memo (QueryInput q) $ do
    let cq = newQuery q (\queryStr -> do
                trace (queryStr ++ show q) $ return ()
                x <- withGas $ case q of
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

bindExternal :: Expr -> FixDemandR x s e (Maybe ExprContext)
bindExternal var@(Var tn@(TName name tp _) vInfo) = do
  let modName = newModuleName (nameModule name)
  (mod', ctx) <- loadModule modName
  if lookupDefGroups (coreProgDefs $ fromJust $ modCoreUnopt mod') tn then return (Just ctx)
  else trace ("External variable binding not found " ++ show tn ++ ": " ++ show vInfo) (return Nothing)

findAllUsage :: Bool -> Expr -> ExprContext -> EnvCtx -> FixDemandR x s e (ExprContext, EnvCtx)
findAllUsage first expr@Var{varName=tname@TName{getName = name}} ctx env = do
  case ctx of
    ModuleC{} -> do
      if nameStem name == "main" then return (ctx, env) else do
        mods <- importedBy (newModuleName (nameModule name))
        each $ map (\m -> do
            withEnv (\e -> e{currentModContext=m, currentContext= m}) $ findUsage first expr m env
          ) mods
    _ -> findUsage first expr ctx env

-- Which modules import the given module
importedBy :: ModuleName -> FixDemandR x s e [ExprContext]
importedBy modN = do
  mods <- buildcModules . buildc <$> getState
  let mods' = filter (\m -> elem modN $ modImportNames m) mods
  mdctxs <- moduleContexts <$> getState
  let ctx = mdctxs M.! modN
  ctxs <- mapM (\m -> do
      (mod, ctx) <- loadModule (modName m)
      return ctx
    ) mods'
  return (ctx:ctxs)

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
            findUsage False expr childCtx (limitmenv (EnvCtx (IndetCtx tn) env) m)
      ExprCBasic _ c (Var{varName=TName{getName=name2}}) ->
        if nameEq name2 then do
          query <- getQueryString
          return $! trace (query ++ "Found usage in " ++ show (ppContextPath ctx)) (c, env)
        else
          -- trace ("Not found usage in " ++ show ctx ++ " had name " ++ show name2 ++ " expected " ++ show name) $ empty
          doBottom
      ModuleC{} -> do
        visitEachChild ctx $ do
          -- visitChildrenCtxs sets the currentContext
          childCtx <- currentContext <$> getEnv
          findUsage first expr childCtx env
      _ -> childrenUsages

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
evalPrimitive var ctx env = do
  case maybeExprOfCtx var of
    Just (Var tn _) -> do
      prims <- primitives <$> getState
      case M.lookup (getName tn) prims of
        Just m -> m (ctx, env)
        Nothing -> error ("evalPrimitive: Primitive not found! " ++ show tn)
    _ -> error ("evalPrimitive: Not a primitive! " ++ show var)

exprPrimitive :: ExprContext -> Int -> ExprContext -> EnvCtx -> FixDemandR x s e AChange
exprPrimitive var index ctx env = do
  case maybeExprOfCtx var of
    Just (Var tn _) -> do
      prims <- eprimitives <$> getState
      case M.lookup (getName tn) prims of
        Just m -> m index (ctx, env)
        Nothing -> error ("exprPrimitive: Primitive not found! " ++ show tn)
    _ -> error ("exprPrimitive: Not a primitive! " ++ show var)

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
            -- trace (query ++ "REF: Primitive " ++ show tn) $ return ()
            return (AChangeClos ctx env)
          else do
            let binded = bind ctx v env
            -- trace (query ++ "REF: " ++ show tn ++ " bound to " ++ show binded) $ return []
            case binded of
              BoundError e -> error "Binding Error"
              BoundLam lamctx lamenv index -> do
                -- For a lambda bound name, we find the callers, and then evaluate the corresponding parameter of the applications found
                AChangeClos appctx appenv <- qcall (lamctx, lamenv)
                -- trace (query ++ "REF: found application " ++ showSimpleContext appctx ++ " " ++ showSimpleEnv appenv ++ " param index " ++ show index) $ return []
                evalParam index appctx appenv
              BoundDef parentCtx ctx boundEnv index -> do
                -- trace (query ++ "REF-def: " ++ show parentCtx ++ " " ++ show index) $ return []
                -- For a top level definition, it evaluates to itself
                qeval (ctx, boundEnv)
              BoundDefRec parentCtx ctx boundEnv index -> do
                -- trace (query ++ "REF-defrec: " ++ show parentCtx ++ " " ++ show index) $ return []
                -- For a top level definition, it evaluates to itself
                qeval (ctx, boundEnv)
              BoundLetDef parentCtx ctx boundEnv index -> do
                -- trace (query ++ "REF-let: " ++ show parentCtx ++ " " ++ show index) $ return []
                -- For a top level definition, it evaluates to itself
                qeval (ctx, boundEnv)
              BoundLetBod parentCtx ctx boundEnv index -> do
                -- For a top level definition, it evaluates to itself
                ctx' <- focusChild index parentCtx
                -- trace (query ++ "REF-letbod: " ++ show ctx' ++ " " ++ show index) $ return []
                qeval (ctx', boundEnv)
              BoundCase parentCtx caseCtx caseEnv branchIndex patBinding -> do
                -- For a case bound name, we focus the scruitinee and delegate to a special function to handle this recursively for nested patterns
                mscrutinee <- focusChild 0 parentCtx
                -- trace (query ++ "REF: scrutinee of case " ++ show scrutinee) $ return []
                evalPatternRef mscrutinee caseEnv patBinding
              BoundModule modulectx modenv -> do
                -- For a name bound in the top level of the current module we evaluate to the lambda of the definition
                lamctx <- getTopDefCtx modulectx (getName tn)
                -- Evaluates just to the lambda
                qeval (lamctx, EnvTail TopCtx)
              BoundGlobal nm _ -> do
                if newModuleName (nameModule (getName nm)) == nameCoreHnd then
                  error ("Hnd: missing primitive " ++ showSimpleContext ctx)
                else do
                  -- For other names we evaluate to the lambda of the definition, and load the module's source on demand if needed
                  ext <- bindExternal v
                  case ext of
                    Just modulectx@ModuleC{} -> do
                      -- trace (query ++ "REF: External module " ++ showSimpleContext modulectx) $ return ()
                      withModuleCtx modulectx $ do
                        lamctx <- getTopDefCtx modulectx (getName tn)
                        -- trace (query ++ "REF: External module " ++ showSimpleContext lamctx) $ return ()
                        qeval (lamctx, EnvTail TopCtx) -- Evaluates just to the lambda
                    _ -> error $ "REF: can't find what the following refers to " ++ showSimpleContext ctx
        App (TypeApp (Con nm repr) _) args rng -> do
          -- trace (query ++ "APPCon: " ++ show ctx) $ return []
          return $ AChangeConstr ctx env
        App (Con nm repr) args rng -> do
          -- trace (query ++ "APPCon: " ++ show ctx) $ return []
          return $ AChangeConstr ctx env
        App f tms rng -> do
          -- trace (query ++ "APP: " ++ show ctx) $ return []
          fun <- focusFun ctx
          -- trace (query ++ "APP: Lambda Fun " ++ show fun) $ return []
          AChangeClos lam lamenv <- qeval (fun, env)
          prim <- isPrimitive lam
          if prim then do
            -- trace (query ++ "APP: Primitive " ++ show lam) $ return ()
            evalPrimitive lam ctx env
          else do
            -- trace (query ++ "APP: Lambda is " ++ show lamctx) $ return []
            (bd, bdenv) <- enterBod lam lamenv ctx env
            qeval (bd, bdenv)
        TypeApp{} ->
          -- trace (query ++ "TYPEAPP: " ++ show ctx) $
          case ctx of
            DefCNonRec{} -> return $! AChangeClos ctx env
            DefCRec{} -> return $! AChangeClos ctx env
            _ -> do
              ctx' <- focusChild 0 ctx
              qeval (ctx',env)
        TypeLam{} ->
          -- trace (query ++ "TYPE LAM: " ++ show ctx) $
          case ctx of
            DefCNonRec{} -> return $! AChangeClos ctx env-- Don't further evaluate if it is just the definition / lambda
            DefCRec{} -> return $! AChangeClos ctx env-- Don't further evaluate if it is just the definition / lambda
            _ -> do
              ctx' <- focusChild 0 ctx
              qeval (ctx',env)
        Lit l -> return $! injLit l env
        Let defs e -> do
          -- trace (query ++ "LET: " ++ show ctx) $ return []
          ex <- focusChild 0 ctx -- Lets have their return expression as first child
          qeval (ex, env)
        Case expr branches -> do
          -- trace (query ++ "CASE: " ++ show ctx) $ return []
          e <- focusChild 0 ctx
          res <- qeval (e, env)
          evalBranches res ctx env (zip branches [0..])
        Con nm repr -> return $! AChangeConstr ctx env -- TODO: Check that the constructor is a singleton

--------------------------------- PATTERN EVALUATION HELPERS -----------------------------------------------
evalPatternRef :: ExprContext -> EnvCtx -> PatBinding -> FixDemandR x s e AChange
evalPatternRef expr env pat = do
  case pat of
    BoundPatVar _ -> qeval (expr, env)
    BoundPatIndex 0 b -> evalPatternRef expr env b -- Only support singleton patterns for now
    BoundConIndex con i subBinding -> do
      -- trace ("EVALPatRef: " ++ show expr ++ " " ++ show pat) $ return ()
      res <- qeval (expr, env)
      case res of
        AChangeConstr conApp cenv -> do
          -- trace ("EVALPatRef2: " ++ show conApp ++ " " ++ show cenv) $ return ()
          case exprOfCtx conApp of
            App c tms rng -> do
              f <- focusChild 0 conApp -- Evaluate the head of the application to get the constructor (could be polymorphic)
              AChangeConstr cexpr _ <- qeval (f, cenv)
              case exprOfCtx cexpr of
                Con nm _ ->
                  if con /= nm then
                    doBottom
                  else do
                    x <- focusParam i conApp
                    evalPatternRef x cenv subBinding
            Con nm _ -> doBottom -- Could also be a singleton constructor, but there are no bound variables there
        e -> error ("EVALPatRef: Not a constructor " ++ show e)

evalBranches :: AChange -> ExprContext -> EnvCtx -> [(Branch, Int)] -> FixDemandR x s e AChange
evalBranches ch ctx env branches =
  case branches of
    [] -> doBottom
    b@(Branch [p] _, i):xs -> do
      -- trace ("Looking for matching branch " ++ show b ++ " " ++ show ch) $ return ()
      matches <- matchesPattern ch p
      if matches then do
        -- trace ("Found matching branch " ++ show p) $ return ()
        e <- focusChild (i + 1) ctx -- +1 to skip the scrutinee
        qeval (e, env)
      else evalBranches ch ctx env xs

matchesPattern :: AChange -> Pattern -> FixDemandR x s e Bool
matchesPattern ch pat =
  case ch of
    AChangeConstr conApp env -> matchesPatternConstr conApp env pat
    AChangeLit lit env -> return $ matchesPatternLit lit env pat
    AChangeClos lam env -> case pat of
      PatVar _ p -> matchesPattern ch p
      PatWild -> return True
      _ -> return False

matchesPatternConstr :: ExprContext -> EnvCtx -> Pattern -> FixDemandR x s e Bool
matchesPatternConstr conApp env pat = do
  case pat of
    PatCon{patConName, patConInfo=ci} -> do
      case exprOfCtx conApp of
        Con nm _ | nm == patConName -> return True
        Con nm _ | nm /= patConName -> return False
        _ -> do
          -- trace ("Looking for matching constructor " ++ show patConName ++ " in " ++ show (exprOfCtx conApp)) $ return ()
          conE <- focusChild 0 conApp
          con <- qeval (conE, env)
          case con of
            AChangeConstr c _ -> do
              case exprOfCtx c of
                Con nm _ | nm == patConName ->
                  if Prelude.null (patConPatterns pat) then return True
                  else do
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

doExpr :: Query -> String -> FixDemandR x s e AChange
doExpr cq@(ExprQ (ctx,env)) query = do
  case ctx of
    AppCLambda _ c e -> -- RATOR Clause
      -- trace (query ++ "OPERATOR: Application is " ++ showCtxExpr c) $
      return $ AChangeClos c env
    AppCParam _ c index e -> do -- RAND Clause 
      -- trace (query ++ "OPERAND: Expr is " ++ showCtxExpr ctx) $ return []
      fn <- focusChild 0 c
      -- trace (query ++ "OPERAND: Evaluating To Closure " ++ showCtxExpr fn) $ return []
      AChangeClos lam lamenv <- qeval (fn, env)
      prim <- isPrimitive lam
      if prim then do
        -- trace (query ++ "OPERAND: Primitive " ++ show lam) $ return ()
        exprPrimitive lam index ctx env
      else do
        -- trace (query ++ "OPERAND: Closure is: " ++ showCtxExpr lam) $ return []
        (bd, bdenv) <- enterBod lam lamenv c env
        m <- contextLength <$> getEnv
        call <- findAllUsage True (lamVar index lam) bd bdenv
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
      -- trace (query ++ "DEF NonRec: Env is " ++ show env) $ return []
      let df = defOfCtx ctx
      call <- case c of
        ModuleC{} -> do
          -- trace (query ++ "DEF NonRec: In module binding " ++ show c ++ " looking for usages of " ++ show (lamVarDef df)) $ return ()
          findAllUsage True (lamVarDef df) c env
        _ -> do
          -- trace (query ++ "DEF NonRec: In other binding " ++ show c ++ " looking for usages of " ++ show (lamVarDef df)) $ return ()
          findAllUsage True (lamVarDef df) (fromJust $ contextOf c) env
      -- trace (query ++ "DEF: Usages are " ++ show ctxs) $ return []
      if isMain ctx then return $ AChangeClos c (EnvTail TopCtx) else qexpr call
    DefCRec _ c _ _ _ -> do
      -- trace (query ++ "DEF Rec: Env is " ++ show env) $ return []
      let df = defOfCtx ctx
      call <- case c of
        ModuleC{} -> do
          -- trace (query ++ "DEF Rec: In module binding " ++ show c ++ " looking for usages of " ++ show (lamVarDef df)) $ return ()
          findAllUsage True (lamVarDef df) c env
        _ -> do
          -- trace (query ++ "DEF Rec: In other binding " ++ show c ++ " looking for usages of " ++ show (lamVarDef df)) $ return ()
          findAllUsage True (lamVarDef df) (fromJust $ contextOf c) env
      -- trace (query ++ "DEF: Usages are " ++ show ctxs) $ return []
      qexpr call
    ExprCBasic _ c _ -> error "Should never get here" -- qexpr (c, env)
    ModuleC{} -> do -- This is for calls to main
      -- trace (query ++ "Module: " ++ show ctx) $ return []
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
            else if cc0 `subsumesCtx` cc1 then do -- cc1 is more refined
              trace (query ++ "UNKNOWN CALL: " ++ showSimpleCtx cc1 ++ " " ++ showSimpleCtx cc0) $ return ()
              instantiate query (EnvCtx cc1 p) env
              doBottom
            else do
              -- trace (query ++ "CALL ERROR:\n\nFIRST:" ++ show cc1 ++ "\n\nSECOND:" ++ show cc0) $ return ()
              doBottom
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

analyzeEachChild :: Show a => ExprContext -> (ExprContext -> FixDemandR x s e a) -> FixDemandR x s e a
analyzeEachChild ctx analyze = do
  let self = analyze ctx
      children = do
        visitEachChild ctx $ do
          childCtx <- currentContext <$> getEnv
          analyzeEachChild childCtx analyze
  each [self, children]

showEscape :: Show a => a -> String
showEscape = escape . show

escape :: String -> String
escape (s:xs) = if s == '\"' then "\\" ++ s:escape xs else s : escape xs
escape [] = []

instance Label (FixOutput m) where
  label (A a) = ""
  label (E e) = ""
  label N = "⊥"

instance Label FixInput where
  label (QueryInput q) = label q
  label (EnvInput e) = "Env Refinements: " ++ escape (showSimpleEnv e)

instance Label Query where
  label (CallQ (ctx, env)) = "Call: " ++ showEscape ctx ++ escape (showSimpleEnv env)
  label (ExprQ (ctx, env)) = "Expr: " ++ showEscape ctx ++ escape (showSimpleEnv env)
  label (EvalQ (ctx, env)) = "Eval: " ++ showEscape ctx ++ escape (showSimpleEnv env)