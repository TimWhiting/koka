{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use uncurry" #-}
{-# LANGUAGE NamedFieldPuns #-}
module Core.Demand.Primitives(createPrimitives) where

import Data.Maybe(fromJust)
import Debug.Trace(trace)
import Common.Name
import Common.NamePrim
import Common.Failure
import Compile.Module
import Core.Demand.FixpointMonad
import Core.Demand.AbstractValue
import Core.Demand.StaticContext
import Core.Demand.DemandAnalysis
import Core.Demand.DemandMonad
import Core.Core as C
import Type.Type (splitFunScheme, Type (TCon), TypeCon (..), Effect, extractOrderedEffect, isEffectEmpty, effectEmpty)
import Data.List (findIndex)
import Type.Pretty (ppType)
import Lib.PPrint (pretty)
import Data.Either (isLeft)
import Type.Unify (runUnifyEx, unify)

nameIntMul = coreIntName "*"
nameIntDiv = coreIntName "/"
nameIntMod = coreIntName "%"
nameIntEq  = coreIntName "=="
nameIntLt  = coreIntName "<"
nameIntLe  = coreIntName "<="
nameIntGt  = coreIntName ">"
nameIntGe  = coreIntName ">="

intOp :: (Integer -> Integer -> Integer) -> (ExprContext, EnvCtx) -> FixDemandR x s e AChange
intOp f (ctx, env) = do
  p1 <- evalParam 0 ctx env
  p2 <- evalParam 1 ctx env
  case (p1, p2) of
    (AChangeLit (LiteralChangeInt (LChangeSingle i1)) _, AChangeLit (LiteralChangeInt (LChangeSingle i2)) _) -> return $! AChangeLit (LiteralChangeInt (LChangeSingle (f i1 i2))) env
    (AChangeLit (LiteralChangeInt _) _, AChangeLit (LiteralChangeInt _) _) -> return $ AChangeLit (LiteralChangeInt LChangeTop) env
    _ -> doBottom

trueCon = AChangeConstr $ ExprPrim C.exprTrue
falseCon = AChangeConstr $ ExprPrim C.exprFalse
toChange :: Bool -> EnvCtx -> AChange
toChange b env = if b then trueCon env else falseCon env

opCmpInt :: (Integer -> Integer -> Bool) -> (ExprContext, EnvCtx) -> FixDemandR x s e AChange
opCmpInt f (ctx, env) = do
  p1 <- evalParam 0 ctx env
  p2 <- evalParam 1 ctx env
  case (p1, p2) of
    (AChangeLit (LiteralChangeInt (LChangeSingle i1)) _, AChangeLit (LiteralChangeInt (LChangeSingle i2)) _) -> return $! toChange (f i1 i2) env
    (AChangeLit (LiteralChangeInt _) _, AChangeLit (LiteralChangeInt _) _) -> each [return $ toChange False env, return $ toChange True env]
    _ -> doBottom

createPrimitives :: FixDemandR x s e ()
createPrimitives = do
  -- Open applied to some function results in that function
  addPrimitive nameEffectOpen (\(ctx, env) -> evalParam 0 ctx env)
  addPrimitiveExpr nameEffectOpen (\i (ctx, env) -> do
    -- Open's first parameter is a function and flows anywhere that the application flows to
    qexpr (fromJust $ contextOf ctx, env)
    )
  addPrimitive (newQualified "std/core/hnd" "clause-control1") (\(ctx, env) -> do
    evalParam 0 ctx env
    )
  addPrimitiveExpr (newQualified "std/core/hnd" "clause-control1") (\index (ctx, env) -> do
    -- ClauseControl1's first parameter is the operation function and flows to wherever the function is applied
    let hnd = enclosingHandle ctx
    let hndapp = fromJust $ contextOf hnd
    let hndenv = envtail env
    let (nm,tp) = fromJust $ maybeHandlerName ctx
    act <- focusParam 2 hnd -- The first parameter is the operation clause, second is the return clause, third is the action lambda
    AChangeClos act actenv <- evalParam 2 hnd env
    (bd, bdenv) <- enterBod act actenv hndapp hndenv
    findEffectApps nm tp bd bdenv
    )
  addPrimitive (namePerform 1) (\(ctx, env) -> do
    -- Perform's second parameter is the function to run with the handler as an argument
    AChangeClos lam lamenv <- evalParam 1 ctx env
    (bd, bdenv) <- enterBod lam lamenv ctx env
    qeval (bd, bdenv)
    )
  addPrimitiveExpr (namePerform 1) (\i (ctx, env) -> do
    assertion "Expression for operator" (i == 1) $ return ()
    -- Perform's second parameter is the function to run with the handler as an argument (ctx)
    let parentCtx = fromJust $ contextOf ctx
    -- Perform's third paremeter is the argument to the operation
    arg <- focusParam 2 parentCtx
    trace ("Perform " ++ showSimpleContext parentCtx) $ return ()
    case exprOfCtx parentCtx of
      C.App perform _ rng -> do
        -- We need to search for the handler with the correct type
        let tp = typeOf perform
        AChangeConstr hnd hndEnv <- qexprx (parentCtx, env, tp)
        trace ("Perform Handler " ++ showSimpleContext hnd ++ "\n\n" ++ showSimpleContext ctx ++ "\n\n" ++ showSimpleContext arg ++ "\n\n") $ return ()
        -- TODO: Check to make sure this gets cached properly and not re-evaluated
        ap0 <- addContextId (\id -> LamCBody id parentCtx [] (C.App (C.App (exprOfCtx ctx) [exprOfCtx hnd] Nothing) [exprOfCtx arg] Nothing))
        appCtx <- focusChild 0 ap0
        -- trace ("Perform Application " ++ showSimpleContext appCtx) $ return ()
        -- This is where the function flows to (this is an application of the parameter - but the indexes of parameters adjusted)
        return $ AChangeClos appCtx hndEnv
      )
  addPrimitive nameHandle (\(ctx, env) -> do
      trace ("Handle " ++ showSimpleContext ctx) $ return ()
      AChangeClos ret retenv <- evalParam 1 ctx env -- The return clause is the result of a handler (as well as any ctl clauses TODO)
      (bd, bdenv) <- enterBod ret retenv ctx env
      qeval (bd, bdenv)
    )
  addPrimitiveExpr nameHandle (\i (ctx, env) -> do
      trace ("HandleExpr " ++ showSimpleContext ctx ++ " index " ++ show i) $ return ()
      if i == 1 then
        doBottom -- TODO: the return clause is "called" with the result of the action
      else if i == 3 then do 
        AChangeClos app appenv <- qexpr (fromJust $ contextOf ctx, env)
        trace ("HandleExprRet " ++ showSimpleContext ctx ++ " result " ++ show app) $ return ()
        return $ AChangeClos app appenv
      else doBottom
    )

  addPrimitive nameInternalSSizeT (\(ctx, env) -> evalParam 0 ctx env)
  -- Integer functions
  addPrimitive nameIntEq  (opCmpInt (==))
  addPrimitive nameIntLt  (opCmpInt (<))
  addPrimitive nameIntLe  (opCmpInt (<=))
  addPrimitive nameIntGt  (opCmpInt (>))
  addPrimitive nameIntGe  (opCmpInt (>=))
  addPrimitive nameIntAdd (intOp (+))
  addPrimitive nameIntSub (intOp (-))
  addPrimitive nameIntMul (intOp (*))
  addPrimitive nameIntDiv (intOp div) -- TODO: Handle division by zero
  addPrimitive nameIntMod (intOp mod) -- TODO: Handle division by zero

findEffectApps :: Name -> Effect -> ExprContext -> EnvCtx -> FixDemandR x s e AChange
findEffectApps nm eff' ctx env =
  qevalx (ctx, env, nm, eff')

