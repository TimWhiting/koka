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
import Common.Name (newLocallyQualified, newQualified)

nameIntMul = coreIntName "*"
nameIntDiv = coreIntName "/"
nameIntMod = coreIntName "%"
nameIntEq  = coreIntName "=="
nameIntLt  = coreIntName "<"
nameIntLe  = coreIntName "<="
nameIntGt  = coreIntName ">"
nameIntGe  = coreIntName ">="
nameIntOdd = coreIntName "is-odd"

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

anyListChar = AChangeConstr $ ExprPrim C.exprTrue
anyChar = AChangeConstr $ ExprPrim C.exprTrue
trueCon = AChangeConstr $ ExprPrim C.exprTrue
falseCon = AChangeConstr $ ExprPrim C.exprFalse
toChange :: Bool -> VEnv -> AChange
toChange b env = if b then trueCon env else falseCon env
anyBool env = each [return $ toChange False env, return $ toChange True env]
changeUnit env = AChangeConstr (ExprPrim C.exprUnit) env

isPrimitive :: TName -> Bool
isPrimitive tn =
  getName tn `elem` [
    nameIntMul, nameIntDiv, nameIntMod, 
    nameIntEq, nameIntLt, nameIntLe, nameIntGt, nameIntGe, 
    nameIntOdd, 
    nameCoreCharLt, nameCoreCharLtEq, nameCoreCharGt, nameCoreCharGtEq, nameCoreCharEq, 
    nameCoreCharToString, nameCoreStringListChar, nameCoreSliceString, nameCoreTypesExternAppend, nameCoreIntExternShow, 
    nameCoreCharInt, nameNumInt32Int, 
    namePretendDecreasing, nameUnsafeTotalCast, 
    nameNumRandom, 
    nameCoreTrace, 
    nameCorePrint, nameCorePrintln]