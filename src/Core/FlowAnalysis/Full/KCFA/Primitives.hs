{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use uncurry" #-}
module Core.FlowAnalysis.Full.KCFA.Primitives where

import Data.Maybe(fromJust)
import Debug.Trace(trace)
import qualified Data.Map.Strict as M
import Common.NamePrim
import Common.Failure
import Compile.Module
import Core.FlowAnalysis.FixpointMonad
import Core.FlowAnalysis.StaticContext
import Core.FlowAnalysis.Full.KCFA.AbstractValue
import Core.FlowAnalysis.Full.KCFA.Monad
import Core.FlowAnalysis.Full.PrimComm
import Core.FlowAnalysis.Literals
import Core.Core as C
import Type.Type (splitFunScheme, Type (TCon), TypeCon (..), Effect, extractOrderedEffect, isEffectEmpty, effectEmpty)
import Data.List (findIndex)
import Type.Pretty (ppType)
import Lib.PPrint (pretty)
import Data.Either (isLeft)
import Type.Unify (runUnifyEx, unify)
import Common.Name
    ( newLocallyQualified,
      newQualified,
      Name(nameStem),
      newName,
      qualifier )
import Core.FlowAnalysis.Monad (FixAR)
import Common.File
import Data.Char (toUpper)
import Numeric (showFFloat, showEFloat)

trueCon ::  AChange
trueCon = AChangeConstr (ExprPrim (ExprContextId (-1001) (newName "true")) C.exprTrue) []
falseCon :: AChange
falseCon = AChangeConstr (ExprPrim (ExprContextId (-1002) (newName "false")) C.exprFalse) []
hole :: AChange 
hole = AChangeConstr (ExprPrim (ExprContextId (-2000) (newName "hole")) C.exprUnit) []
toChange :: Bool  -> AChange
toChange b = if b then trueCon else falseCon
anyBool :: (Ord i, Show c, Show o, Lattice o c) => FixAR x s e i o c AChange
anyBool = each [return $ toChange True, return $ toChange False]
changeUnit :: AChange
changeUnit = AChangeConstr (ExprPrim (ExprContextId (-1000) (newName "unit")) C.exprUnit) []

intOp :: (Integer -> Integer -> Integer) -> [AChange] -> FixAAMR x s e AChange
intOp f [p1, p2] = do
  case (p1, p2) of
    (AChangeLit (LiteralChangeIntX (LChangeSingle (e1, i1))), AChangeLit (LiteralChangeIntX (LChangeSingle (e2, i2)))) ->
      return $! AChangeLit (LiteralChangeIntX (LChangeSingle (e2, f i1 i2)))
    (AChangeLit (LiteralChangeIntX _), AChangeLit (LiteralChangeIntX _)) ->
      return $ AChangeLit (LiteralChangeIntX LChangeTop)
    _ -> doBottom

floatOp :: (Double -> Double -> Double) -> [AChange] -> FixAAMR x s e AChange
floatOp f [p1, p2] = do
  case (p1, p2) of
    (AChangeLit (LiteralChangeFloatX (LChangeSingle (e1, i1))), AChangeLit (LiteralChangeFloatX (LChangeSingle (e2, i2)))) ->
      return $! AChangeLit (LiteralChangeFloatX (LChangeSingle (e2, f i1 i2)))
    (AChangeLit (LiteralChangeFloatX _), AChangeLit (LiteralChangeFloatX _)) ->
      return $ AChangeLit (LiteralChangeFloatX LChangeTop)
    _ -> doBottom

float1Op :: (Double -> Double) -> [AChange] -> FixAAMR x s e AChange
float1Op f [p1] = do
  case p1 of
    (AChangeLit (LiteralChangeFloatX (LChangeSingle (e1, i1)))) ->
      return $! AChangeLit (LiteralChangeFloatX (LChangeSingle (e1, f i1)))
    (AChangeLit (LiteralChangeFloatX _)) ->
      return $ AChangeLit (LiteralChangeFloatX LChangeTop)
    _ -> doBottom

charCmpOp :: (Char -> Char -> Bool) -> [AChange] -> FixAAMR x s e AChange
charCmpOp f [p1, p2] = do
  case (p1, p2) of
    (AChangeLit (LiteralChangeCharX (LChangeSingle (_, c1))), AChangeLit (LiteralChangeCharX (LChangeSingle (_, c2)))) ->
      return $! toChange (f c1 c2)
    (AChangeLit (LiteralChangeCharX _), AChangeLit (LiteralChangeCharX _)) -> anyBool
    _ -> doBottom

opCmpInt :: (Integer -> Integer -> Bool) -> [AChange] -> FixAAMR x s e AChange
opCmpInt f [p1, p2] = do
  case (p1, p2) of
    (AChangeLit (LiteralChangeIntX (LChangeSingle (_, i1))), AChangeLit (LiteralChangeIntX (LChangeSingle (_, i2)))) ->
      return $! toChange (f i1 i2)
    (AChangeLit (LiteralChangeIntX _), AChangeLit (LiteralChangeIntX _)) ->
      -- trace "opCmpInt: top" 
      anyBool
    _ -> doBottom

opCmpFloat :: (Double -> Double -> Bool) -> [AChange] -> FixAAMR x s e AChange
opCmpFloat f [p1, p2] = do
  case (p1, p2) of
    (AChangeLit (LiteralChangeFloatX (LChangeSingle (_, i1))), AChangeLit (LiteralChangeFloatX (LChangeSingle (_, i2)))) ->
      return $! toChange (f i1 i2)
    (AChangeLit (LiteralChangeFloatX _), AChangeLit (LiteralChangeFloatX _)) ->
      -- trace "opCmpFloat: top"
      anyBool
    _ -> 
      doBottom

opCmpString :: (String -> String -> Bool) -> [AChange] -> FixAAMR x s e AChange
opCmpString f [p1, p2] = do
  case (p1, p2) of
    (AChangeLit (LiteralChangeStringX (LChangeSingle (_, s1))), AChangeLit (LiteralChangeStringX (LChangeSingle (_, s2)))) ->
      return $! toChange (f s1 s2)
    (AChangeLit (LiteralChangeStringX _), AChangeLit (LiteralChangeStringX _)) ->
      anyBool
    _ -> doBottom

doPrimitive :: Name -> [AChange]  -> FixAAMR r s e AChange
doPrimitive nm achanges = do
  -- trace (" Primitive " ++ show nm ++ " " ++ show achanges) $ return ()
  if nm == nameCCtxEmpty then 
    return hole
  else if nm == nameIntEq || nm == nameInt32Eq then
    opCmpInt (==) achanges
  else if nm == nameIntNEq || nm == nameInt32NEq then
    opCmpInt (/=) achanges
  else if nm == nameIntLt || nm == nameInt32Lt then
    opCmpInt (<) achanges
  else if nm == nameIntLe || nm == nameInt32Le then
    opCmpInt (<=) achanges
  else if nm == nameIntGt || nm == nameInt32Gt then
    opCmpInt (>) achanges
  else if nm == nameIntGe || nm == nameInt32Ge then
    opCmpInt (>=) achanges
  else if nm == nameIntAdd then
    intOp (+) achanges
  else if nm == nameIntMul then
    intOp (*) achanges
  else if nm == nameIntSub then
    intOp (-) achanges
  else if nm == nameIntDiv then
    intOp div achanges
  else if nm == nameIntMod then
    intOp mod achanges
  else if nm == nameFloatAdd then
    floatOp (+) achanges
  else if nm == nameFloatMul then
    floatOp (*) achanges
  else if nm == nameFloatSub then
    floatOp (-) achanges
  else if nm == nameFloatDiv then
    floatOp (/) achanges
  else if nm == nameFloatAbs then 
    float1Op abs achanges
  else if nm == nameFloatSqrt then
    float1Op sqrt achanges
  else if nm == nameFloatEq then
    opCmpFloat (==) achanges
  else if nm == nameFloatLt then
    opCmpFloat (<) achanges
  else if nm == nameFloatLe then
    opCmpFloat (<=) achanges
  else if nm == nameFloatGt then
    opCmpFloat (>) achanges
  else if nm == nameFloatGe then
    opCmpFloat (>=) achanges
  else if nm == nameInternalSSizeT || nm == nameCoreIntExternSSizeT || nm == nameNumInt32Int32 then
    return $ head achanges
  else if nm == nameNumSRandomFloat64 then
    return $ AChangeLit (LiteralChangeFloatX LChangeTop)
  else if nm == nameNumRandom then 
    return $ AChangeLit (LiteralChangeIntX LChangeTop)
  else if nm == nameOSReadline then
    return $ AChangeLit (LiteralChangeStringX LChangeTop)
  else if nm == nameCoreIntShow then
    case achanges of
      [AChangeLit (LiteralChangeIntX (LChangeSingle (e2, i)))] ->
        return $ AChangeLit (LiteralChangeStringX (LChangeSingle (e2, show i)))
      [AChangeLit (LiteralChangeIntX _)] ->
        return $ AChangeLit (LiteralChangeStringX LChangeTop)
      _ -> doBottom
  else if nm == nameFloatShowFixed then
    case achanges of
      [AChangeLit (LiteralChangeFloatX (LChangeSingle (e1, f))), AChangeLit (LiteralChangeIntX (LChangeSingle (e2, i)))] ->
        return $ AChangeLit (LiteralChangeStringX (LChangeSingle (e2, showFFloatNoZeros (fromIntegral i) f)))
      [AChangeLit (LiteralChangeFloatX _), AChangeLit (LiteralChangeIntX _)] ->
        return $ AChangeLit (LiteralChangeStringX LChangeTop)
      _ -> doBottom
  else if nm == nameFloatShowExpX then
    case achanges of
      [AChangeLit (LiteralChangeFloatX (LChangeSingle (e1, f))), AChangeLit (LiteralChangeIntX (LChangeSingle (e2, i)))] ->
        return $ AChangeLit (LiteralChangeStringX (LChangeSingle (e2, showEFloatNoZeros (fromIntegral i) f)))
      [AChangeLit (LiteralChangeFloatX _), AChangeLit (LiteralChangeIntX _)] ->
        return $ AChangeLit (LiteralChangeStringX LChangeTop)
      _ -> doBottom
  else if nm == nameBoolNegate then
    case achanges of
      [AChangeConstr (ExprPrim _ e) _] | isExprTrue e -> return falseCon
      [AChangeConstr (ExprPrim _ e) _] | isExprFalse e -> return trueCon
      _ -> doBottom
  else if nm == nameIntOdd then
    case achanges of
      [AChangeLit (LiteralChangeIntX (LChangeSingle (_, i)))] -> return $ toChange (odd i)
      [AChangeLit (LiteralChangeIntX _)] -> anyBool
  else if nm == nameStringEq then
    opCmpString (==) achanges
  else if nm == nameCoreStringExternRepeatZ then
    case achanges of
      [AChangeLit (LiteralChangeStringX (LChangeSingle (e2, s))), AChangeLit (LiteralChangeIntX (LChangeSingle (_, n)))] | n >= 0 ->
        return $ AChangeLit (LiteralChangeStringX (LChangeSingle (e2, concat (replicate (fromIntegral n) s))))
      [AChangeLit (LiteralChangeStringX _), AChangeLit (LiteralChangeIntX _)] ->
        return $ AChangeLit (LiteralChangeStringX LChangeTop)
      _ -> doBottom
  else if nm == nameCoreCharToString then 
    case achanges of
      [AChangeLit (LiteralChangeCharX (LChangeSingle (e2, c)))] ->
        return $ AChangeLit (LiteralChangeStringX (LChangeSingle (e2, [c])))
      [AChangeLit (LiteralChangeCharX _)] ->
        return $ AChangeLit (LiteralChangeStringX LChangeTop)
      _ -> doBottom
  else if nm == nameCoreStringToUpper then
    case achanges of
      [AChangeLit (LiteralChangeStringX (LChangeSingle (e2, s)))] ->
        return $ AChangeLit (LiteralChangeStringX (LChangeSingle (e2, map toUpper s)))
      [AChangeLit (LiteralChangeStringX _)] ->
        return $ AChangeLit (LiteralChangeStringX LChangeTop)
      _ -> doBottom
  else if nm == nameCoreStringCount then
    case achanges of
      [AChangeLit (LiteralChangeStringX (LChangeSingle (e2, s)))] ->
        return $ AChangeLit (LiteralChangeIntX (LChangeSingle (e2, fromIntegral (length s))))
      [AChangeLit (LiteralChangeStringX _)] ->
        return $ AChangeLit (LiteralChangeIntX LChangeTop)
      _ -> doBottom
  else if nm == nameCoreTypesExternAppend then
    case achanges of
      [AChangeLit (LiteralChangeStringX (LChangeSingle (_, s1))), AChangeLit (LiteralChangeStringX (LChangeSingle (u2, s2)))] ->
        return $ AChangeLit (LiteralChangeStringX (LChangeSingle (u2, s1 ++ s2)))
      [AChangeLit (LiteralChangeStringX _), AChangeLit (LiteralChangeStringX _)] -> do
        -- trace ("AChanges " ++ show achanges) $ return ()
        return $ AChangeLit (LiteralChangeStringX LChangeTop)
      _ -> doBottom
  else if nm == nameCoreCharLt then
    charCmpOp (<) achanges
  else if nm == nameCoreCharLtEq then
    charCmpOp (<=) achanges
  else if nm == nameCoreCharGt then
    charCmpOp (>) achanges
  else if nm == nameCoreCharGtEq then
    charCmpOp (>=) achanges
  else if nm == nameCoreCharEq then
    charCmpOp (==) achanges
  else if (nm == nameCoreTrace) || (nm == nameCoreTraceShow) || (nm == nameCorePrint)
          || (nm == nameCorePrintln) || (nm == nameCorePrintsLn) then
    -- trace ("Print / Trace " ++ show achanges)
    return changeUnit
  else if nm == nameUnsafeNoLocalCast || nm == namePretendDecreasing then return (head achanges)
  else
    error ("Primitive: " ++ show nm ++ " " ++ show achanges)