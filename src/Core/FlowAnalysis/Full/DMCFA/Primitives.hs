{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use uncurry" #-}
module Core.FlowAnalysis.Full.DMCFA.Primitives where

import Data.Maybe(fromJust)
import Debug.Trace(trace)
import qualified Data.Map.Strict as M
import qualified Data.Bits as Bits
import Data.Bits ((.&.), (.|.), xor)
import Data.Int (Int32, Int64)
import Data.Word (Word64, Word32)
import GHC.Float (castWord64ToDouble, castDoubleToWord64)
import Common.NamePrim
import Common.Failure
import Compile.Module
import Core.FlowAnalysis.FixpointMonad
import Core.FlowAnalysis.StaticContext
import Core.FlowAnalysis.Full.DMCFA.AbstractValue
import Core.FlowAnalysis.Full.DMCFA.Monad
import Core.FlowAnalysis.Literals
import Core.FlowAnalysis.Full.PrimComm
import Core.Core as C
import Type.Type (splitFunScheme, Type (..), TypeCon (..), Effect, extractOrderedEffect, isEffectEmpty, effectEmpty, typeInt)
import Data.List (findIndex, isPrefixOf, intercalate, isInfixOf)
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
import Data.Char (toUpper, toLower)
import Numeric (showFFloat, showEFloat, readHex)
import Kind.Kind

trueCon ::  AChange
trueCon = AChangeConstr nameTrue []
falseCon :: AChange
falseCon = AChangeConstr nameFalse []
justCon :: Addr -> Type -> AChange
justCon addr tp = AChangeObj nameJust [(justValueName, addr)]
nothingCon :: AChange
nothingCon = AChangeConstr nameNothing []
emptyCtx :: AChange
emptyCtx = AChangeConstr (newName "emptyCtx") []
hole :: AChange
hole = AChangeConstr (newName "hole") []
toChange :: Bool  -> AChange
toChange b = if b then trueCon else falseCon
anyBool :: (Ord i, Show c, Show o, Lattice o c) => FixAR x s e i o c AChange
anyBool = each [return $ toChange True, return $ toChange False]
changeUnit :: AChange
changeUnit = AChangeConstr (newName "unit") []

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
      -- trace ("opCmpFloat: bottom " ++ show (p1, p2)) $ 
      doBottom

opCmpString :: (String -> String -> Bool) -> [AChange] -> FixAAMR x s e AChange
opCmpString f [p1, p2] = do
  case (p1, p2) of
    (AChangeLit (LiteralChangeStringX (LChangeSingle (_, s1))), AChangeLit (LiteralChangeStringX (LChangeSingle (_, s2)))) ->
      return $! toChange (f s1 s2)
    (AChangeLit (LiteralChangeStringX _), AChangeLit (LiteralChangeStringX _)) ->
      anyBool
    _ -> doBottom

doPrimitive :: HasCallStack => Name -> [AChange] -> CombinedCtx -> ExprContextId -> (Addr -> FixAAMR r s e AChange) -> (Addr -> AChange -> FixAAMR r s e ()) -> FixAAMR r s e AChange
doPrimitive nm achanges ctx u store extendStore = do
  -- trace (" Primitive " ++ show achanges) $ return ()
  if nm == nameCCtxEmpty then
    return emptyCtx
  else if nm == nameCCtxHoleCreate then
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
  else if nm == nameIntAdd || nm == nameInt32Add then
    intOp (+) achanges
  else if nm == nameIntMul || nm == nameInt32Mul then
    intOp (*) achanges
  else if nm == nameIntSub || nm == nameInt32Sub then
    intOp (-) achanges
  else if nm == nameIntDiv || nm == nameInt32Div then
    intOp div achanges
  else if nm == nameInt32Shr then
    intOp (\i s -> toInteger (fromIntegral i `Bits.shiftR` fromIntegral s :: Word32)) achanges
  else if nm == nameInt32Sar then
    intOp (\i s -> toInteger (fromIntegral i `Bits.shiftR` fromIntegral s :: Int32)) achanges
  else if nm == nameInt32Shl then
    intOp (\i s -> toInteger (fromIntegral i `Bits.shiftL` fromIntegral s :: Word32)) achanges
  else if nm == nameInt32And then
    intOp (\i1 i2 -> toInteger (fromIntegral i1 .&. fromIntegral i2 :: Word32)) achanges
  else if nm == nameInt32Or then
    intOp (\i1 i2 -> toInteger (fromIntegral i1 .|. fromIntegral i2 :: Word32)) achanges
  else if nm == nameInt32Xor then
    intOp (\i1 i2 -> toInteger (xor (fromIntegral i1) (fromIntegral i2) :: Word32)) achanges
  else if nm == nameInt32RotL then
    intOp (\i s -> toInteger (Bits.rotateL (fromIntegral i :: Word32) (fromIntegral s))) achanges
  else if nm == nameInt32RotR then
    intOp (\i s -> toInteger (Bits.rotateR (fromIntegral i :: Word32) (fromIntegral s))) achanges
  else if nm == nameInt32Clz || nm == nameInt32Ctz || nm == nameInt32PopCount then
    case achanges of
      [AChangeLit (LiteralChangeIntX (LChangeSingle (e1, i1)))] ->
        let f = if nm == nameInt32Clz then Bits.countLeadingZeros 
                else if nm == nameInt32Ctz then Bits.countTrailingZeros
                else Bits.popCount
        in return $ AChangeLit (LiteralChangeIntX (LChangeSingle (e1, toInteger (f (fromIntegral i1 :: Word32)))))
      [AChangeLit (LiteralChangeIntX _)] -> return $ AChangeLit (LiteralChangeIntX LChangeTop)
      _ -> doBottom
  else if nm == nameInt64And then
    intOp (\i1 i2 -> toInteger (fromIntegral i1 .&. fromIntegral i2 :: Word64)) achanges
  else if nm == nameInt64Or then
    intOp (\i1 i2 -> toInteger (fromIntegral i1 .|. fromIntegral i2 :: Word64)) achanges
  else if nm == nameInt64Xor then
    intOp (\i1 i2 -> toInteger (xor (fromIntegral i1) (fromIntegral i2) :: Word64)) achanges
  else if nm == nameInt64Shr then
    intOp (\i s -> toInteger (fromIntegral i `Bits.shiftR` fromIntegral s :: Word64)) achanges
  else if nm == nameInt64Sar then
    intOp (\i s -> toInteger (fromIntegral i `Bits.shiftR` fromIntegral s :: Int64)) achanges
  else if nm == nameInt64Shl then
    intOp (\i s -> toInteger (fromIntegral i `Bits.shiftL` fromIntegral s :: Word64)) achanges
  else if nm == nameInt64RotL then
    intOp (\i n -> toInteger (Bits.rotateL (fromIntegral i :: Word64) (fromIntegral n))) achanges
  else if nm == nameInt64RotR then
    intOp (\i n -> toInteger (Bits.rotateR (fromIntegral i :: Word64) (fromIntegral n))) achanges
  else if nm == nameInt64HiLo32 || (nm == nameNumInt64ExternInt64 && length achanges == 2) || (nm == nameNumInt64Int64 && length achanges == 2) then
    intOp (\hi lo -> (hi `Bits.shiftL` 32) Bits..|. (lo Bits..&. 0xFFFFFFFF)) achanges
  else if nm == nameInt64Clz || nm == nameInt64Ctz || nm == nameInt64PopCount then
    case achanges of
      [AChangeLit (LiteralChangeIntX (LChangeSingle (e1, i1)))] ->
        let f = if nm == nameInt64Clz then Bits.countLeadingZeros 
                else if nm == nameInt64Ctz then Bits.countTrailingZeros
                else Bits.popCount
        in return $ AChangeLit (LiteralChangeIntX (LChangeSingle (e1, toInteger (f (fromIntegral i1 :: Word64)))))
      [AChangeLit (LiteralChangeIntX _)] -> return $ AChangeLit (LiteralChangeIntX LChangeTop)
      _ -> doBottom
  else if nm == nameNumInt64Int64 || nm == nameNumInt64ExternInt64 then
    return $ head achanges
  else if nm == nameIntMod then
    intOp mod achanges
  else if nm == nameFloatAdd then
    floatOp (+) achanges
  else if nm == nameNumFloat64ExternFloat64FromBits then
    case achanges of
      [AChangeLit (LiteralChangeIntX (LChangeSingle (e1, i)))] ->
        return $ AChangeLit (LiteralChangeFloatX (LChangeSingle (e1, castWord64ToDouble (fromIntegral i))))
      [AChangeLit (LiteralChangeIntX _)] -> return $ AChangeLit (LiteralChangeFloatX LChangeTop)
      _ -> doBottom
  else if nm == nameNumFloat64ExternFloat64ToBits then
    case achanges of
      [AChangeLit (LiteralChangeFloatX (LChangeSingle (e1, d)))] ->
        return $ AChangeLit (LiteralChangeIntX (LChangeSingle (e1, toInteger (castDoubleToWord64 d))))
      [AChangeLit (LiteralChangeFloatX _)] -> return $ AChangeLit (LiteralChangeIntX LChangeTop)
      _ -> doBottom
  else if nm == nameNumFloat64Float64 then
    case achanges of
      [AChangeLit (LiteralChangeIntX (LChangeSingle (e1, i)))] ->
        return $ AChangeLit (LiteralChangeFloatX (LChangeSingle (e1, fromInteger i)))
      [AChangeLit (LiteralChangeIntX _)] -> return $ AChangeLit (LiteralChangeFloatX LChangeTop)
      _ -> doBottom
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
  else if nm == nameInternalSSizeT || nm == nameCoreIntExternSSizeT || nm == nameNumInt32Int32 || nm == nameNumInt64Int32 || nm == nameNumInt64UInt32 then
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
      [AChangeConstr nm _] | nameTrue == nm -> return falseCon
      [AChangeConstr nm _] | nameFalse == nm -> return trueCon
      _ -> doBottom
  else if nm == nameIntOdd then
    case achanges of
      [AChangeLit (LiteralChangeIntX (LChangeSingle (_, i)))] -> return $ toChange (odd i)
      [AChangeLit (LiteralChangeIntX _)] -> anyBool
  else if nm == nameStringEq then
    opCmpString (==) achanges
  else if nm == nameCoreStringNeq then
    opCmpString (/=) achanges
  else if nm == nameCoreSliceXStartsWith then
    opCmpString (\s1 s2 -> s2 `isPrefixOf` s1) achanges
  else if nm == nameCoreXParse then
    case achanges of
      [AChangeLit (LiteralChangeStringX (LChangeSingle (e1, s))), AChangeConstr e _] ->
        if nameTrue == e then
          case readHex s of
            [(v, "")] -> do
              let addr = ConImplicitAddr justValueName ctx u
              extendStore addr (AChangeLit $ LiteralChangeIntX (LChangeSingle (e1, v)))
              return $ justCon addr typeInt
            _ -> return nothingCon
        else do
          let addr = ConImplicitAddr justValueName ctx u
          extendStore addr (AChangeLit $ LiteralChangeIntX (LChangeSingle (e1, read s)))
          return $ justCon addr typeInt
      [AChangeLit (LiteralChangeStringX _), AChangeConstr e _] -> do
        let addr = ConImplicitAddr justValueName ctx u
        extendStore addr (AChangeLit $ LiteralChangeIntX LChangeTop)
        each [return nothingCon, return $ justCon addr typeInt]
      _ -> doBottom
  else if nm == nameCoreSliceLength then
    case achanges of
      [AChangeLit (LiteralChangeStringX (LChangeSingle (e2, s)))] -> return $ AChangeLit (LiteralChangeIntX (LChangeSingle (e2, fromIntegral $ length s)))
      [AChangeLit (LiteralChangeStringX LChangeTop)] -> return $ AChangeLit (LiteralChangeIntX LChangeTop)
      _ -> doBottom
  else if nm == nameCoreSliceString then
    case achanges of
      [AChangeObj _ [(_, str), (_, start), (_, len)]] -> do
        rString <- store str
        rStart <- store start
        rLen <- store len
        case (rString, rStart, rLen) of
          (AChangeLit (LiteralChangeStringX (LChangeSingle (e1, s))),
           AChangeLit (LiteralChangeIntX (LChangeSingle (e2, st))),
           AChangeLit (LiteralChangeIntX (LChangeSingle (e3, ln)))) ->
            return $ AChangeLit (LiteralChangeStringX (LChangeSingle (e2, take (fromInteger ln) (drop (fromInteger st) s))))
          _ -> return $ AChangeLit (LiteralChangeStringX LChangeTop)
  else if nm == nameCoreStringVectorJoin then
    case achanges of
      [AChangeObj _ args] -> do
        vals <- mapM (store . snd) args
        if all (\v -> case v of AChangeLit (LiteralChangeStringX (LChangeSingle (e1, s))) -> True; _ -> False) vals then do
          let vals2 = map (\(AChangeLit (LiteralChangeStringX (LChangeSingle (e1, s)))) -> s) vals
          let change = (\(AChangeLit (LiteralChangeStringX (LChangeSingle (e2, s)))) -> e2) (last vals)
          return $ AChangeLit (LiteralChangeStringX (LChangeSingle (change, intercalate "" vals2)))
        else return $ AChangeLit (LiteralChangeStringX LChangeTop)
  else if nm == nameCoreVectorUnvlist then 
    error ("Unsupported")
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
  else if nm == nameCoreStringCount then
    case achanges of
      [AChangeLit (LiteralChangeStringX (LChangeSingle (e2, s)))] ->
        return $ AChangeLit (LiteralChangeIntX (LChangeSingle (e2, fromIntegral (length s))))
      [AChangeLit (LiteralChangeStringX _)] ->
        return $ AChangeLit (LiteralChangeIntX LChangeTop)
      _ -> doBottom
  else if nm == nameCoreStringToUpper then
    case achanges of
      [AChangeLit (LiteralChangeStringX (LChangeSingle (e2, s)))] ->
        return $ AChangeLit (LiteralChangeStringX (LChangeSingle (e2, map toUpper s)))
      [AChangeLit (LiteralChangeStringX _)] ->
        return $ AChangeLit (LiteralChangeStringX LChangeTop)
      _ -> doBottom
  else if nm == nameCoreStringToLower then
    case achanges of
      [AChangeLit (LiteralChangeStringX (LChangeSingle (e, s)))] ->
        return $ AChangeLit (LiteralChangeStringX (LChangeSingle (e, map toLower s)))
      [AChangeLit (LiteralChangeStringX _)] ->
        return $ AChangeLit (LiteralChangeStringX LChangeTop)
      _ -> doBottom
  else if nm == nameCoreStringContains then
    opCmpString (\s1 s2 -> s2 `isInfixOf` s1) achanges  
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