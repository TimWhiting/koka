{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use uncurry" #-}
module Core.FlowAnalysis.Full.DMCFAR.Primitives where

import Data.Maybe(fromJust)
import Debug.Trace(trace)
import qualified Data.Map.Strict as M
import Common.NamePrim
import Common.Failure
import Compile.Module
import Core.FlowAnalysis.FixpointMonad
import Core.FlowAnalysis.StaticContext
import Core.FlowAnalysis.Full.DMCFAR.AbstractValue
import Core.FlowAnalysis.Full.DMCFAR.Monad
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

nameIntMul = coreIntName "*"
nameIntDiv = coreIntName "/"
nameIntMod = coreIntName "%"
nameIntEq  = coreIntName "=="
nameIntNEq  = coreIntName "!="
nameIntLt  = coreIntName "<"
nameIntLe  = coreIntName "<="
nameIntGt  = coreIntName ">"
nameIntGe  = coreIntName ">="
nameIntOdd = coreIntName "is-odd"
nameFloatGt = newQualified "std/num/float64" ">"
nameFloatGe = newQualified "std/num/float64" ">="
nameFloatLt = newQualified "std/num/float64" "<"
nameFloatLe = newQualified "std/num/float64" "<="
nameFloatEq = newQualified "std/num/float64" "=="
nameFloatMul = newQualified "std/num/float64" "*"
nameFloatDiv = newQualified "std/num/float64" "/"
nameFloatAdd = newQualified "std/num/float64" "+"
nameFloatSub = newQualified "std/num/float64" "-"
nameStringEq = newQualified "std/core/string" "=="
nameBoolNegate = newLocallyQualified "std/core/types" "bool" "!"

nameCoreCharLt = newQualified "std/core/char" "<"
nameCoreCharLtEq = newQualified "std/core/char" "<="
nameCoreIntShow = newQualified "std/core/int" "show"
nameCoreCharGt = newQualified "std/core/char" ">"
nameCoreCharGtEq = newQualified "std/core/char" ">="
nameCoreCharEq = newQualified "std/core/char" "=="
nameCoreCharToString = newLocallyQualified "std/core/string" "char" "@extern-string"
nameCoreStringListChar = newQualified "std/core/string" "list"
nameCoreSliceString = newQualified "std/core/sslice" "@extern-string"

nameCoreTypesExternAppend = newQualified "std/core/types" "@extern-x++"
nameCoreIntExternShow = newQualified "std/core/int" "@extern-show"
nameCoreCharInt = newQualified "std/core/char" "int"
nameNumInt32Int = newQualified "std/num/int32" "int"
namePretendDecreasing = newQualified "std/core/undiv" "pretend-decreasing"
nameUnsafeTotalCast = newQualified "std/core/unsafe" "unsafe-total-cast"
nameUnsafeNoLocalCast = newQualified  "std/core/types" "unsafe-no-local-cast"
nameNumRandom = newQualified "std/num/random" "random-int"
nameNumSRandomFloat64 = newQualified "std/num/random" "@extern-srandom-float64"
nameCoreTrace = newQualified "std/core/debug" "trace"
nameCoreTraceShow = newQualified "std/core/debug" "trace-show"
nameCorePrint = newLocallyQualified "std/core/console" "string" "print"
nameCorePrintln = newLocallyQualified "std/core/console" "string" "println"
nameCorePrintsLn = newQualified "std/core/console" "printsln"


trueCon ::  AChange
trueCon = AChangeConstr (ExprPrim (ExprContextId (-1001) (newName "true")) C.exprTrue) []
falseCon :: AChange
falseCon = AChangeConstr (ExprPrim (ExprContextId (-1002) (newName "false")) C.exprFalse) []
toChange :: Bool  -> AChange
toChange b = if b then trueCon else falseCon
anyBool :: (Ord i, Show c, Show (o c), Lattice o c) => FixAR x s e i o c AChange
anyBool = each [return $ toChange True, return $ toChange False]
changeUnit :: AChange
changeUnit = AChangeConstr (ExprPrim (ExprContextId (-1000) (newName "unit")) C.exprUnit) []

isClauseName :: Name -> Bool
isClauseName name = qualifier name == nameCoreHnd && nameStem name `startsWith` "clause"

isNamePerform :: Name -> Bool
isNamePerform n = qualifier n == nameCoreHnd && nameStem n `startsWith` "@perform"

isPrimitive :: TName -> Bool
isPrimitive tn =
  let basics = getName tn `elem` [
                      nameIntAdd, nameIntMul, nameIntDiv, nameIntMod, nameIntSub,
                      nameIntEq, nameIntNEq, nameIntLt, nameIntLe, nameIntGt, nameIntGe,
                      nameIntOdd,
                      nameFloatAdd, nameFloatMul, nameFloatDiv, nameFloatSub,
                      nameFloatEq, nameFloatLt, nameFloatLe, nameFloatGt, nameFloatGe,
                      nameCoreIntShow,
                      nameCoreCharLt, nameCoreCharLtEq, nameCoreCharGt, nameCoreCharGtEq, nameCoreCharEq,
                      nameStringEq, 
                      nameCoreCharToString, nameCoreStringListChar, nameCoreSliceString,
                      nameCoreTypesExternAppend, nameCoreIntExternShow,
                      nameCoreCharInt, nameNumInt32Int,
                      namePretendDecreasing, nameUnsafeTotalCast, nameUnsafeNoLocalCast,
                      nameNumRandom, nameNumSRandomFloat64,
                      nameCoreTrace, nameCoreTraceShow,
                      nameCorePrint, nameCorePrintln, nameCorePrintsLn,
                      nameLocalGet, nameLocalSet,
                      nameHandle, nameHTag, nameEvvAt, nameLocalNew, nameLocalVar,
                      nameInternalSSizeT
                      ]
  in basics || isNamePerform (getName tn) || isClauseName (getName tn)

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
    _ -> doBottom

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
  -- trace (" Primitive " ++ show achanges) $ return ()
  if nm == nameIntEq then
    opCmpInt (==) achanges
  else if nm == nameIntNEq then
    opCmpInt (/=) achanges
  else if nm == nameIntLt then
    opCmpInt (<) achanges
  else if nm == nameIntLe then
    opCmpInt (<=) achanges
  else if nm == nameIntGt then
    opCmpInt (>) achanges
  else if nm == nameIntGe then
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
  else if nm == nameInternalSSizeT then
    return $ head achanges
  else if nm == nameNumSRandomFloat64 then
    return $ AChangeLit (LiteralChangeFloatX LChangeTop)
  else if nm == nameNumRandom then 
    return $ AChangeLit (LiteralChangeIntX LChangeTop)
  else if nm == nameCoreIntShow then
    case achanges of
      [AChangeLit (LiteralChangeIntX (LChangeSingle (e2, i)))] ->
        return $ AChangeLit (LiteralChangeStringX (LChangeSingle (e2, show i)))
      [AChangeLit (LiteralChangeIntX _)] ->
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