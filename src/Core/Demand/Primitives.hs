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

nameCoreCharLt = newQualified "std/core/char" "<"
nameCoreCharLtEq = newQualified "std/core/char" "<="
nameCoreCharGt = newQualified "std/core/char" ">"
nameCoreCharGtEq = newQualified "std/core/char" ">="
nameCoreCharEq = newQualified "std/core/char" "=="
nameCoreCharToString = newLocallyQualified "std/core/string" "char" "@extern-string"
nameCoreStringListChar = newQualified "std/core/string" "list"
nameCoreSliceString = newQualified "std/core/sslice" "@extern-string"

nameCoreTypesExternAppend = newQualified "std/core/types" "@extern-x++"
nameCoreIntExternShow = newQualified "std/core/int" "@extern-show"
nameCoreCharInt = newQualified "std/core/char" "int"
nameClauseControl1 = newQualified "std/core/hnd" "clause-control1"
nameClauseControl2 = newQualified "std/core/hnd" "clause-control2"
nameClauseControl3 = newQualified "std/core/hnd" "clause-control3"
nameClauseTail1 = newQualified "std/core/hnd" "clause-tail1"
nameClauseTail2 = newQualified "std/core/hnd" "clause-tail2"
nameClauseTail3 = newQualified "std/core/hnd" "clause-tail3"


intOp :: (Integer -> Integer -> Integer) -> (ExprContext, EnvCtx) -> FixDemandR x s e AChange
intOp f (ctx, env) = do
  p1 <- evalParam 0 ctx env
  p2 <- evalParam 1 ctx env
  case (p1, p2) of
    (AChangeLit (LiteralChangeInt (LChangeSingle i1)) _, AChangeLit (LiteralChangeInt (LChangeSingle i2)) _) -> return $! AChangeLit (LiteralChangeInt (LChangeSingle (f i1 i2))) env
    (AChangeLit (LiteralChangeInt _) _, AChangeLit (LiteralChangeInt _) _) -> return $ AChangeLit (LiteralChangeInt LChangeTop) env
    _ -> doBottom

charCmpOp :: (Char -> Char -> Bool) -> (ExprContext, EnvCtx) -> FixDemandR x s e AChange
charCmpOp f (ctx, env) = do
  p1 <- evalParam 0 ctx env
  p2 <- evalParam 1 ctx env
  case (p1, p2) of
    (AChangeLit (LiteralChangeChar (LChangeSingle c1)) _, AChangeLit (LiteralChangeChar (LChangeSingle c2)) _) -> return $! toChange (f c1 c2) env
    (AChangeLit (LiteralChangeChar _) _, AChangeLit (LiteralChangeChar _) _) -> each [return $ toChange False env, return $ toChange True env]
    _ -> doBottom

anyListChar = AChangeConstr $ ExprPrim C.exprTrue
anyChar = AChangeConstr $ ExprPrim C.exprTrue
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
    qexpr (fromJust $ contextOf ctx, env))
  
  addPrimitive nameCoreIntExternShow (\(ctx, env) -> do
    param <- evalParam 0 ctx env
    case param of
      AChangeLit (LiteralChangeInt (LChangeSingle i)) _ -> return $ AChangeLit (LiteralChangeString $ LChangeSingle $ show i) env
      _ -> return $ AChangeLit (LiteralChangeString $ LChangeTop) env
    )
  addPrimitiveExpr nameCoreIntExternShow (\i (ctx, env) -> doBottom)

  addPrimitive nameCoreTypesExternAppend (\(ctx, env) -> do
    p0 <- evalParam 0 ctx env
    p1 <- evalParam 1 ctx env
    case (p0, p1) of
      (AChangeLit (LiteralChangeString (LChangeSingle s0)) _, AChangeLit (LiteralChangeString (LChangeSingle s1)) _) -> return $ AChangeLit (LiteralChangeString (LChangeSingle (s0 ++ s1))) env
      (AChangeLit (LiteralChangeString _) _, AChangeLit (LiteralChangeString _) _) -> return $ AChangeLit (LiteralChangeString LChangeTop) env
      _ -> doBottom
    )
  addPrimitiveExpr nameCoreTypesExternAppend (\i (ctx, env) -> doBottom)

  addPrimitive nameCoreCharToString (\(ctx, env) -> do
      p0 <- evalParam 0 ctx env
      case p0 of
        AChangeLit (LiteralChangeChar (LChangeSingle c)) _ -> return $ AChangeLit (LiteralChangeString (LChangeSingle [c])) env
        AChangeLit (LiteralChangeChar _) _ -> return $ AChangeLit (LiteralChangeString LChangeTop) env
        _ -> doBottom
    )
  addPrimitiveExpr nameCoreCharToString (\i (ctx, env) -> doBottom)

  addPrimitive nameCoreCharInt (\(ctx, env) -> do
      p0 <- evalParam 0 ctx env
      case p0 of
        AChangeLit (LiteralChangeChar (LChangeSingle c)) _ -> return $ AChangeLit (LiteralChangeInt (LChangeSingle $ fromIntegral $ fromEnum c)) env
        AChangeLit (LiteralChangeChar _) _ -> return $ AChangeLit (LiteralChangeInt LChangeTop) env
        _ -> doBottom
    )
  addPrimitiveExpr nameCoreCharInt (\i (ctx, env) -> doBottom)

  addPrimitive nameCoreStringListChar (\(ctx, env) -> do
      p0 <- evalParam 0 ctx env
      case p0 of
        AChangeLit (LiteralChangeString (LChangeSingle s)) _ -> return $ AChangeLit (LiteralChangeString (LChangeSingle "")) env
        AChangeLit (LiteralChangeString _) _ -> return $ AChangeLit (LiteralChangeString LChangeTop) env
        _ -> doBottom
    )
  addPrimitiveExpr nameCoreStringListChar (\i (ctx, env) -> doBottom)

  addPrimitive nameCoreSliceString (\(ctx, env) -> do
      p0 <- evalParam 0 ctx env
      case p0 of
        AChangeConstr _ _ -> return $ AChangeLit (LiteralChangeString LChangeTop) env
        _ -> doBottom
    )
  addPrimitiveExpr nameCoreSliceString (\i (ctx, env) -> doBottom)


  addPrimitive nameInternalSSizeT (\(ctx, env) -> evalParam 0 ctx env)
  -- Integer functions

  addPrimitive nameCoreCharLt (charCmpOp (<))
  addPrimitive nameCoreCharLtEq (charCmpOp (<=))
  addPrimitive nameCoreCharGt (charCmpOp (>))
  addPrimitive nameCoreCharGtEq (charCmpOp (>=))
  addPrimitive nameCoreCharEq (charCmpOp (==))
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

