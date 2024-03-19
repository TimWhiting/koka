{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use uncurry" #-}
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
  newModId <- newContextId
  let modName = newName "primitives"
      modCtx = ModuleC newModId (moduleNull modName) modName
  do            
    -- Open applied to some function results in that function
    addPrimitive nameEffectOpen (\(ctx, env) -> evalParam 0 ctx env)
    addPrimitiveExpr nameEffectOpen (\i (ctx, env) -> do
      assertion ("EffectOpen: " ++ show i ++ " " ++ show ctx ++ " " ++ show env) (i == 0) $ return ()
      -- Open's first parameter is a function and flows anywhere that the application flows to
      qexpr (fromJust $ contextOf ctx, env)
      )
    -- Integer functions
    addPrimitive nameIntAdd (intOp (+))
    addPrimitive nameIntSub (intOp (-))
    addPrimitive nameIntMul (intOp (*))
    addPrimitive nameIntDiv (intOp div)
    addPrimitive nameIntMod (intOp mod)
  return ()