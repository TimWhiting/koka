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
    addPrimitive (namePerform 1) (\(ctx, env) -> do
      -- Perform's first parameter is the effiencient evidence index, but we will just find the handler dynamically
      case parentDefOfCtx ctx of
        C.Def _ sch _ _ _ _ _ _ -> do
          case splitFunScheme sch of
            Just (_, _, _, eff, _) -> do
              let effName = case eff of
                    TCon (TypeCon n _) -> n
                    _ -> failure "perform: Expected effect type"
              -- Find the handler for the effect
              AChangeConstr handlerCon handleEnv <- findHandler effName ctx env
              -- Perform's second parameter is the function to run with the handler as an argument
              AChangeClos sel selEnv <- evalParam 1 ctx env
              -- The third parameter is the argument to the operation
              opArg <- evalParam 2 ctx env
              -- Expression relation on the selector function needs to get the handler
              -- We've got a match statement with a asingle case, so just use the first case
              case exprOfCtx sel of
                C.Case scrutinee [C.Branch [p] _] -> 
                  case p of
                    C.PatCon{patConPatterns} ->
                      case findIndex (\p -> case p of {PatWild -> False; PatVar _ _-> True;}) patConPatterns of 
                        Just i -> do
                          AChangeConstr f fenv <- evalParam i handlerCon handleEnv
                          doBottom
                          -- Somehow we need to evaluate the f body with the argument being the opArg
            _ -> doBottom
      )

    addPrimitive nameInternalSSizeT (\(ctx, env) -> evalParam 0 ctx env)
    -- Integer functions
    addPrimitive nameIntAdd (intOp (+))
    addPrimitive nameIntSub (intOp (-))
    addPrimitive nameIntMul (intOp (*))
    addPrimitive nameIntDiv (intOp div) -- TODO: Handle division by zero
    addPrimitive nameIntMod (intOp mod) -- TODO: Handle division by zero
  return ()

findHandler :: Name -> ExprContext -> EnvCtx -> FixDemandR x s e AChange
findHandler nm ctx env = doBottom