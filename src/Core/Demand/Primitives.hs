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
import Type.Type (splitFunScheme, Type (TCon), TypeCon (..))
import Data.List (findIndex)

nameIntMul = coreIntName "*"
nameIntDiv = coreIntName "/"
nameIntMod = coreIntName "%"

intOp :: (Integer -> Integer -> Integer) -> (ExprContext, EnvCtx) -> FixDemandR x s e AChange
intOp f (ctx, env) = do
  p1 <- evalParam 0 ctx env
  p2 <- evalParam 1 ctx env
  case (p1, p2) of
    (AChangeLit (LiteralChangeInt (LChangeSingle i1)) _, AChangeLit (LiteralChangeInt (LChangeSingle i2)) _) -> return $! AChangeLit (LiteralChangeInt (LChangeSingle (f i1 i2))) env
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
    let nm = handlerName ctx
    act <- focusParam 1 hnd -- The first parameter is the operation clause, second is the action
    findEffectApps nm act env
    )
  addPrimitive (namePerform 1) (\(ctx, env) -> do
    -- Perform's second parameter is the function to run with the handler as an argument
    AChangeClos lam lamenv <- evalParam 1 ctx env
    bod <- focusBody lam
    succ <- succAEnv ctx env
    let newEnv = EnvCtx succ lamenv
    qeval (bod, newEnv)
    )
  addPrimitiveExpr (namePerform 1) (\i (ctx, env) -> do
    let parentCtx = fromJust $ contextOf ctx
    -- Perform's second parameter is the function to run with the handler as an argument
    case exprOfCtx parentCtx of
      C.App _ _ rng -> do
        f <- focusParam 0 parentCtx
        arg <- focusParam 1 parentCtx
        -- TODO: Check to make sure this gets cached properly and not re-evaluated
        appCtx <- addContextId (\id -> LamCBody id parentCtx [] (C.App (exprOfCtx f) [exprOfCtx arg] Nothing))
        return $ AChangeClos appCtx env -- This is where the function flows to (this is an application of the parameter - but the indexes of parameters adjusted)
      )

  addPrimitive nameInternalSSizeT (\(ctx, env) -> evalParam 0 ctx env)
  -- Integer functions
  addPrimitive nameIntAdd (intOp (+))
  addPrimitive nameIntSub (intOp (-))
  addPrimitive nameIntMul (intOp (*))
  addPrimitive nameIntDiv (intOp div) -- TODO: Handle division by zero
  addPrimitive nameIntMod (intOp mod) -- TODO: Handle division by zero

findHandler :: Name -> ExprContext -> EnvCtx -> FixDemandR x s e AChange
findHandler nm ctx env = 
  trace ("FindHandler: " ++ show nm ++ " " ++ show ctx ++ " " ++ show env) $ do
  doBottom

findEffectApps :: Name -> ExprContext -> EnvCtx -> FixDemandR x s e AChange
findEffectApps nm ctx env = 
  trace ("FindEffectApps: " ++ show nm ++ " " ++ show ctx ++ " " ++ show env) $ do
  doBottom


