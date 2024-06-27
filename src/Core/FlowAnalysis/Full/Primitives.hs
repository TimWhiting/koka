{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use uncurry" #-}
module Core.FlowAnalysis.Full.Primitives where

import Data.Maybe(fromJust)
import Debug.Trace(trace)
import Common.NamePrim
import Common.Failure
import Compile.Module
import Core.FlowAnalysis.FixpointMonad
import Core.FlowAnalysis.StaticContext
import Core.FlowAnalysis.Full.Monad
import Core.FlowAnalysis.Full.AbstractValue
import Core.FlowAnalysis.Literals
import Core.Core as C
import Type.Type (splitFunScheme, Type (TCon), TypeCon (..), Effect, extractOrderedEffect, isEffectEmpty, effectEmpty)
import Data.List (findIndex)
import Type.Pretty (ppType)
import Lib.PPrint (pretty)
import Data.Either (isLeft)
import Type.Unify (runUnifyEx, unify)
import Common.Name (newLocallyQualified, newQualified, Name)

nameIntMul = coreIntName "*"
nameIntDiv = coreIntName "/"
nameIntMod = coreIntName "%"
nameIntEq  = coreIntName "=="
nameIntLt  = coreIntName "<"
nameIntLe  = coreIntName "<="
nameIntGt  = coreIntName ">"
nameIntGe  = coreIntName ">="
nameIntOdd = coreIntName "is-odd"
nameBoolNegate = newLocallyQualified "std/core/types" "bool" "!"

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
nameNumInt32Int = newQualified "std/num/int32" "int"
namePretendDecreasing = newQualified "std/core/undiv" "pretend-decreasing"
nameUnsafeTotalCast = newQualified "std/core/unsafe" "unsafe-total-cast"
nameNumRandom = newQualified "std/num/random" "random-int"
nameCoreTrace = newQualified "std/core/debug" "trace"
nameCorePrint = newLocallyQualified "std/core/console" "string" "print"
nameCorePrintln = newLocallyQualified "std/core/console" "string" "println"

trueCon :: VEnv -> AChange
trueCon = AChangeConstr $ ExprPrim C.exprTrue
falseCon :: VEnv -> AChange
falseCon = AChangeConstr $ ExprPrim C.exprFalse
toChange :: Bool -> VEnv -> AChange
toChange b env = if b then trueCon env else falseCon env
anyBool :: VEnv -> FixAACR x s e AChange
anyBool env = each [return $ toChange True env, return $ toChange False env]
changeUnit :: VEnv -> AChange
changeUnit = AChangeConstr (ExprPrim C.exprUnit)

isPrimitive :: TName -> Bool
isPrimitive tn =
  getName tn `elem` [
    nameIntAdd, nameIntMul, nameIntDiv, nameIntMod, nameIntSub,
    nameIntEq, nameIntLt, nameIntLe, nameIntGt, nameIntGe,
    nameIntOdd,
    nameCoreCharLt, nameCoreCharLtEq, nameCoreCharGt, nameCoreCharGtEq, nameCoreCharEq,
    nameCoreCharToString, nameCoreStringListChar, nameCoreSliceString, nameCoreTypesExternAppend, nameCoreIntExternShow,
    nameCoreCharInt, nameNumInt32Int,
    namePretendDecreasing, nameUnsafeTotalCast,
    nameNumRandom,
    nameCoreTrace,
    nameCorePrint, nameCorePrintln]

intOp :: (Integer -> Integer -> Integer) -> [AChange] -> VEnv -> FixAACR x s e AChange
intOp f [p1, p2] venv = do
  case (p1, p2) of
    (AChangeLit (LiteralChangeInt (LChangeSingle i1)) _, AChangeLit (LiteralChangeInt (LChangeSingle i2)) _) -> return $! AChangeLit (LiteralChangeInt (LChangeSingle (f i1 i2))) venv
    (AChangeLit (LiteralChangeInt _) _, AChangeLit (LiteralChangeInt _) _) -> return $ AChangeLit (LiteralChangeInt LChangeTop) venv
    _ -> doBottom

charCmpOp :: (Char -> Char -> Bool) -> [AChange] -> VEnv -> FixAACR x s e AChange
charCmpOp f [p1, p2] venv = do
  case (p1, p2) of
    (AChangeLit (LiteralChangeChar (LChangeSingle c1)) _, AChangeLit (LiteralChangeChar (LChangeSingle c2)) _) -> return $! toChange (f c1 c2) venv
    (AChangeLit (LiteralChangeChar _) _, AChangeLit (LiteralChangeChar _) _) -> anyBool venv
    _ -> doBottom

opCmpInt :: (Integer -> Integer -> Bool) -> [AChange] -> VEnv -> FixAACR x s e AChange
opCmpInt f [p1, p2] venv = do
  case (p1, p2) of
    (AChangeLit (LiteralChangeInt (LChangeSingle i1)) _, AChangeLit (LiteralChangeInt (LChangeSingle i2)) _) -> return $! toChange (f i1 i2) venv
    (AChangeLit (LiteralChangeInt _) _, AChangeLit (LiteralChangeInt _) _) -> 
      trace "opCmpInt: top" $
      anyBool venv
    _ -> doBottom

doPrimitive :: Name -> [Addr] -> VEnv -> VStore -> FixAACR r s e AChange
doPrimitive nm addrs env store = do
  achanges <- mapM (storeGet store) addrs
  trace ("Primitive: " ++ show nm ++ " " ++ show achanges) $ return ()
  if nm == nameIntEq then
    opCmpInt (==) achanges env
  else if nm == nameIntLt then
    opCmpInt (<=) achanges env
  else if nm == nameIntLe then
    opCmpInt (<) achanges env
  else if nm == nameIntGt then
    opCmpInt (>) achanges env
  else if nm == nameIntGe then
    opCmpInt (>=) achanges env
  else if nm == nameIntAdd then
    intOp (+) achanges env
  else if nm == nameIntMul then
    intOp (*) achanges env
  else if nm == nameIntSub then
    intOp (-) achanges env
  else if nm == nameIntDiv then
    intOp div achanges env
  else if nm == nameIntMod then
    intOp mod achanges env
  else if nm == nameBoolNegate then
    case achanges of
      [AChangeConstr (ExprPrim e) _] | isExprTrue e -> return $ AChangeConstr (ExprPrim C.exprFalse) env
      [AChangeConstr (ExprPrim e) _] | isExprFalse e -> return $ AChangeConstr (ExprPrim C.exprTrue) env
      _ -> doBottom
  else if nm == nameCoreCharLt then
    charCmpOp (<) achanges env
  else if nm == nameCoreCharLtEq then
    charCmpOp (<=) achanges env
  else if nm == nameCoreCharGt then
    charCmpOp (>) achanges env
  else if nm == nameCoreCharGtEq then
    charCmpOp (>=) achanges env
  else if nm == nameCoreCharEq then
    charCmpOp (==) achanges env
  else
    error $ "doPrimitive: " ++ show nm