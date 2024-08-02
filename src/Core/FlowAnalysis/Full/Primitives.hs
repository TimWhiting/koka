{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use uncurry" #-}
module Core.FlowAnalysis.Full.Primitives where

import Data.Maybe(fromJust)
import Debug.Trace(trace)
import qualified Data.Map.Strict as M
import Common.NamePrim
import Common.Failure
import Compile.Module
import Core.FlowAnalysis.FixpointMonad
import Core.FlowAnalysis.StaticContext
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
import Core.FlowAnalysis.Monad (FixAR)
import Core.FlowAnalysis.StaticContext

trueCon ::  AChange
trueCon = AChangeConstr (ExprPrim C.exprTrue) M.empty
falseCon :: AChange
falseCon = AChangeConstr (ExprPrim C.exprFalse) M.empty
toChange :: Bool  -> AChange
toChange b = if b then trueCon else falseCon
anyBool :: (Ord i, Show c, Show (o c), Lattice o c) => FixAR x s e i o c AChange
anyBool = each [return $ toChange True, return $ toChange False]
changeUnit :: AChange
changeUnit = AChangeConstr (ExprPrim C.exprUnit) M.empty

isPrimitive :: TName -> Bool
isPrimitive tn =
  getName tn `elem` [
    nameIntAdd, nameIntMul, nameIntDiv, nameIntMod, nameIntSub,
    nameIntEq, nameIntLt, nameIntLe, nameIntGt, nameIntGe,
    nameIntOdd,
    nameCoreIntShow,
    nameCoreCharLt, nameCoreCharLtEq, nameCoreCharGt, nameCoreCharGtEq, nameCoreCharEq,
    nameCoreCharToString, nameCoreStringListChar, nameCoreSliceString, nameCoreTypesExternAppend, nameCoreIntExternShow,
    nameCoreCharInt, nameNumInt32Int,
    namePretendDecreasing, nameUnsafeTotalCast,
    nameNumRandom,
    nameCoreTrace,
    nameCorePrint, nameCorePrintln,
    nameHandle, 
    namePerform 0, namePerform 1, namePerform 2, namePerform 3, namePerform 4,
    nameClause "tail" 0, nameClause "tail" 1, nameClause "tail" 2, nameClause "tail" 3, nameClause "tail" 4,
    nameClause "control" 0, nameClause "control" 1, nameClause "control" 2, nameClause "control" 3, nameClause "control" 4
    ]

intOp :: (Integer -> Integer -> Integer) -> [AChange] -> FixAR x s e i o c AChange
intOp f [p1, p2] = do
  case (p1, p2) of
    (AChangeLit (LiteralChangeInt (LChangeSingle i1)), AChangeLit (LiteralChangeInt (LChangeSingle i2))) -> return $! AChangeLit (LiteralChangeInt (LChangeSingle (f i1 i2)))
    (AChangeLit (LiteralChangeInt _), AChangeLit (LiteralChangeInt _)) -> return $ AChangeLit (LiteralChangeInt LChangeTop)
    _ -> doBottom

charCmpOp :: (Ord i, Show c, Show (o c), Lattice o c) => (Char -> Char -> Bool) -> [AChange] -> FixAR x s e i o c AChange
charCmpOp f [p1, p2] = do
  case (p1, p2) of
    (AChangeLit (LiteralChangeChar (LChangeSingle c1)), AChangeLit (LiteralChangeChar (LChangeSingle c2))) -> return $! toChange (f c1 c2)
    (AChangeLit (LiteralChangeChar _), AChangeLit (LiteralChangeChar _)) -> anyBool
    _ -> doBottom

opCmpInt ::(Ord i, Show c, Show (o c), Lattice o c) =>  (Integer -> Integer -> Bool) -> [AChange] -> FixAR x s e i o c AChange
opCmpInt f [p1, p2] = do
  case (p1, p2) of
    (AChangeLit (LiteralChangeInt (LChangeSingle i1)), AChangeLit (LiteralChangeInt (LChangeSingle i2))) -> return $! toChange (f i1 i2)
    (AChangeLit (LiteralChangeInt _), AChangeLit (LiteralChangeInt _)) ->
      trace "opCmpInt: top" anyBool
    _ -> doBottom

doPrimitive :: (Ord i, Show c, Show (o c), Lattice o c) => Name -> [Addr] -> VEnv -> VStore -> FixAR r s e i o c AChange
doPrimitive nm addrs env store = do
  achanges <- mapM (\a -> storeGet store a) addrs
  -- trace ("Primitive: " ++ show nm ++ " " ++ show achanges) $ return ()
  if nm == nameIntEq then
    opCmpInt (==) achanges
  else if nm == nameIntLt then
    opCmpInt (<=) achanges
  else if nm == nameIntLe then
    opCmpInt (<) achanges
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
  else if nm == nameCoreIntShow then
    case achanges of
      [AChangeLit (LiteralChangeInt (LChangeSingle i))] -> return $ AChangeLit (LiteralChangeString (LChangeSingle (show i)))
      [AChangeLit (LiteralChangeInt _)] -> return $ AChangeLit (LiteralChangeString LChangeTop)
      _ -> doBottom
  else if nm == nameBoolNegate then
    case achanges of
      [AChangeConstr (ExprPrim e) _] | isExprTrue e -> return $ AChangeConstr (ExprPrim C.exprFalse) M.empty
      [AChangeConstr (ExprPrim e) _] | isExprFalse e -> return $ AChangeConstr (ExprPrim C.exprTrue) M.empty
      _ -> doBottom
  else if nm == nameIntOdd then
    case achanges of
      [AChangeLit (LiteralChangeInt (LChangeSingle i))] -> return $ toChange (odd i)
      [AChangeLit (LiteralChangeInt _)] -> anyBool
  else if nm == nameCoreTypesExternAppend then
    case achanges of
      [AChangeLit (LiteralChangeString (LChangeSingle s1)), AChangeLit (LiteralChangeString (LChangeSingle s2))] -> return $ AChangeLit (LiteralChangeString (LChangeSingle (s1 ++ s2)))
      [AChangeLit (LiteralChangeString _), AChangeLit (LiteralChangeString _)] -> return $ AChangeLit (LiteralChangeString LChangeTop)
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
  else if (nm == nameCoreTrace) || (nm == nameCorePrint) || (nm == nameCorePrintln) then
    return changeUnit
  else
    error $ "doPrimitive: " ++ show nm