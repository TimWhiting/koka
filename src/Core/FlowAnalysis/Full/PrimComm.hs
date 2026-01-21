
module Core.FlowAnalysis.Full.PrimComm where
import Core.Core
import Common.Name
import Common.NamePrim
import Common.File (startsWith)
import qualified Data.Map.Strict as M
import Numeric (showFFloat, showEFloat)
import Data.List (dropWhileEnd)
import Debug.Trace
import Type.Type
import Kind.Kind

nameIntMul = coreIntName "*"
nameIntDiv = coreIntName "/"
nameIntMod = coreIntName "%"
nameIntEq  = coreIntName "=="
nameIntNEq = coreIntName "!="
nameIntLt  = coreIntName "<"
nameIntLe  = coreIntName "<="
nameIntGt  = coreIntName ">"
nameIntGe  = coreIntName ">="
nameIntOdd = coreIntName "is-odd"
nameInt32Gt = newQualified "std/num/int32" ">"
nameInt32Ge = newQualified "std/num/int32" ">="
nameInt32Lt = newQualified "std/num/int32" "<"
nameInt32Le = newQualified "std/num/int32" "<="
nameInt32Eq = newQualified "std/num/int32" "=="
nameInt32NEq = newQualified "std/num/int32" "!="
nameInt32Add = newQualified "std/num/int32" "+"
nameInt32Sub = newQualified "std/num/int32" "-"
nameInt32Mul = newQualified "std/num/int32" "*"
nameInt32Div = newQualified "std/num/int32" "/"
nameInt32Shr = newQualified "std/num/int32" "shr32"
nameInt32Sar = newQualified "std/num/int32" "sar32"
nameInt32Shl = newQualified "std/num/int32" "shl32"
nameInt32And = newQualified "std/num/int32" "and"
nameInt32Or  = newQualified "std/num/int32" "or"
nameInt32Xor = newQualified "std/num/int32" "xor"
nameInt32RotL = newQualified "std/num/int32" "rotl32"
nameInt32RotR = newQualified "std/num/int32" "rotr32"
nameInt32Clz = newQualified "std/num/int32" "clz"
nameInt32Ctz = newQualified "std/num/int32" "ctz"
nameInt32PopCount = newQualified "std/num/int32" "popcount"
nameInt64And = newQualified "std/num/int64" "and"
nameInt64Or  = newQualified "std/num/int64" "or"
nameInt64Xor = newQualified "std/num/int64" "xor"
nameInt64Shr = newQualified "std/num/int64" "shr64"
nameInt64Sar = newQualified "std/num/int64" "sar64"
nameInt64Shl = newQualified "std/num/int64" "shl64"
nameInt64RotL = newQualified "std/num/int64" "rotl64"
nameInt64RotR = newQualified "std/num/int64" "rotr64"
nameInt64Clz = newQualified "std/num/int64" "clz"
nameInt64Ctz = newQualified "std/num/int64" "ctz"
nameInt64PopCount = newQualified "std/num/int64" "popcount64"
nameInt64HiLo32 = newLocallyQualified "std/num/int64" "hilo32" "int64"
nameNumInt64Int32 = newQualified "std/num/int64" "int32"
nameNumInt64UInt32 = newQualified "std/num/int64" "uint32"
nameNumInt64Int64 = newQualified "std/num/int64" "int64"
nameNumInt64ExternInt64 = newQualified "std/num/int64" "@extern-int64"
nameNumFloat64ExternFloat64FromBits = newQualified "std/num/float64" "@extern-float64-from-bits"
nameNumFloat64ExternFloat64ToBits = newQualified "std/num/float64" "@extern-float64-to-bits"
nameNumFloat64Float64 = newQualified "std/num/float64" "float64"
nameFloatGt = newQualified "std/num/float64" ">"
nameFloatGe = newQualified "std/num/float64" ">="
nameFloatLt = newQualified "std/num/float64" "<"
nameFloatLe = newQualified "std/num/float64" "<="
nameFloatEq = newQualified "std/num/float64" "=="
nameFloatMul = newQualified "std/num/float64" "*"
nameFloatDiv = newQualified "std/num/float64" "/"
nameFloatAdd = newQualified "std/num/float64" "+"
nameFloatSub = newQualified "std/num/float64" "-"
nameFloatAbs = newQualified "std/num/float64" "abs"
nameFloatSqrt = newQualified "std/num/float64" "sqrt"
nameFloatShowFixed = newQualified "std/num/float64" "@extern-show-fixedx"
nameFloatShowExpX = newQualified "std/num/float64" "@extern-show-expx"
nameBoolNegate = newLocallyQualified "std/core/types" "bool" "!"

nameCoreCharLt = newQualified "std/core/char" "<"
nameCoreCharLtEq = newQualified "std/core/char" "<="
nameCoreIntShow = newQualified "std/core/int" "show"
nameCoreCharGt = newQualified "std/core/char" ">"
nameCoreCharGtEq = newQualified "std/core/char" ">="
nameCoreCharEq = newQualified "std/core/char" "=="
nameCoreCharToString = newLocallyQualified "std/core/string" "char" "@extern-string"
nameCoreStringContains = newQualified "std/core/string" "contains"
nameCoreStringToLower = newQualified "std/core/string" "to-lower"
nameCoreStringListChar = newQualified "std/core/string" "list"
nameCoreSliceString = newQualified "std/core/sslice" "@extern-string"
nameCoreSliceXStartsWith = newQualified "std/core/sslice" "xstarts-with"
nameCoreSliceLength = newQualified "std/core/sslice" "length"
nameCoreStringToUpper = newQualified "std/core/string" "@extern-to-upper"
nameCoreStringExternRepeatZ = newQualified "std/core/string" "@extern-repeatz"
nameCoreStringCount = newLocallyQualified "std/core/string" "chars" "@extern-count"
nameCoreStringVectorJoin = newLocallyQualified "std/core/string" "vector" "join"
nameOSReadline = newQualified "std/os/readline" "readline"
nameStringEq = newQualified "std/core/string" "=="
nameCoreVectorUnvlist = newQualified "std/core/vector" "@extern-unvlist"
nameCoreStringJoinSep = newQualified "std/core/list" "joinsep"
nameCoreStringJoinSep2 = newQualified "std/core/list" "joinsep2"
nameCoreStringJoin = newLocallyQualified "std/core/list" "concat" "join"
nameCoreStringJoin2 = newLocallyQualified "std/core/list" "concat" "join2"

justValueName = newName "value"
maybeType :: Type -> Type
maybeType tp = TApp (TCon (TypeCon nameTpMaybe (kindFun kindStar kindStar))) [tp]
nameCoreTypesExternAppend = newQualified "std/core/types" "@extern-x++"
nameCoreIntExternShow = newQualified "std/core/int" "@extern-show"
nameCoreCharInt = newQualified "std/core/char" "int"
nameNumInt32Int = newQualified "std/num/int32" "int"
nameNumInt32Int32 = newQualified "std/num/int32" "int32"
nameCoreIntExternSSizeT = newQualified "std/core/int" "@extern-ssize_t"
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
nameCoreXParse = newQualified "std/core/int" "@extern-xparse"
nameCoreMInt = newQualified "std/num/random" "mrandom-int"
showMap st = M.foldlWithKey (\acc k v -> acc ++ show k ++ ": " ++ show v ++ "\n") "" st
primitiveFuncWrappers = [nameUnsafeNoLocalCast, nameUnsafeTotalCast]

-- | Show a float with a given precision. 
-- If `numDigits` >= 0, it acts as "%.<numDigits>f" (fixed precision).
-- If `numDigits` < 0, it acts as "%.<abs(numDigits)>g" (general precision).
--
-- This mimics Koka's `show-fixed` (and C's `printf("%g")` for negative precision), 
-- where scientific notation is used if the exponent is < -4 or >= precision.
--
-- Note: Haskell's `Numeric.showGFloat` does not exactly match C's `%g` behavior 
-- regarding trailing zeros and exact switch points, so we implement the logic manually here.
showFFloatNoZeros :: Int -> Double -> String
showFFloatNoZeros numDigits f
  | isNaN f = "nan"
  | isInfinite f = if f < 0 then "-inf" else "inf"
  | numDigits >= 0 = showFFloat (Just numDigits) f ""
  | otherwise =
      let p = abs numDigits
          e = exponent10 f
      in if e < -4 || e >= p
           then formatGExp (p - 1) f
           else removeTrailingZeros (showFFloat (Just (max 0 (p - 1 - e))) f "")

-- | Show a float in exponential notation.
-- If `numDigits` >= 0, it acts as "%.<numDigits>e".
-- If `numDigits` < 0, it falls back to `showFFloatNoZeros` (general behavior).
showEFloatNoZeros :: Int -> Double -> String
showEFloatNoZeros numDigits f
  | isNaN f = "nan"
  | isInfinite f = if f < 0 then "-inf" else "inf"
  | numDigits >= 0 = formatExp numDigits f
  | otherwise = showFFloatNoZeros numDigits f

exponent10 :: Double -> Int
exponent10 0 = 0
exponent10 x = floor (logBase 10 (abs x))

-- Formats exponent to match C style e+NN (at least 2 digits, unlike Haskell's show)
formatExpon :: String -> String
formatExpon "" = ""
formatExpon (_:es) =
    let (sign, num) = if null es then ("+", "0") else if head es == '-' then ("-", tail es) else ("+", es) -- handle potential "e" with no number? Unlikely.
        p = if null num then 0 else read num :: Int
    in "e" ++ sign ++ (if p < 10 then "0" else "") ++ show p

stripExpon :: String -> String
stripExpon s = if s == "e+00" || s == "e-00" then "" else s

formatGExp :: Int -> Double -> String
formatGExp digits f =
    let s = showEFloat (Just digits) f ""
        (mant, expPart) = break (== 'e') s
        mant' = removeTrailingZeros mant
        exp' = stripExpon (formatExpon expPart)
    in mant' ++ exp'

formatExp :: Int -> Double -> String
formatExp digits f =
    let s = showEFloat (Just digits) f ""
        (mant, expPart) = break (== 'e') s
        exp' = stripExpon (formatExpon expPart)
    in mant ++ exp'

removeETrailingZeros :: String -> String
removeETrailingZeros = removeTrailingZeros

removeTrailingZeros :: String -> String
removeTrailingZeros s =
    let (whole, frac) = break (== '.') s
    in case frac of
        [] -> whole
        '.' : rest ->
            let trimmedFrac = dropWhileEnd (== '0') rest
            in if null trimmedFrac
                then whole
                else whole ++ "." ++ trimmedFrac

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
                      nameInt32Gt, nameInt32Ge, nameInt32Lt, nameInt32Le, nameInt32Eq, nameInt32NEq,
                      nameInt32Add, nameInt32Sub, nameInt32Mul, nameInt32Div,
                      nameInt32Shr, nameInt32Sar, nameInt32Shl, nameInt32And, nameInt32Or, nameInt32Xor, nameInt32RotL, nameInt32RotR,
                      nameInt32Clz, nameInt32Ctz, nameInt32PopCount,
                      nameInt64Shr, nameInt64Sar, nameInt64Shl, nameInt64And, nameInt64Or, nameInt64Xor, nameInt64RotL, nameInt64RotR, nameInt64Clz, nameInt64Ctz, nameInt64PopCount, nameInt64HiLo32,
                      nameNumInt64Int32, nameNumInt64UInt32,
                      nameNumInt64Int64, nameNumInt64ExternInt64, nameNumFloat64ExternFloat64FromBits, nameNumFloat64ExternFloat64ToBits, nameNumFloat64Float64,
                      nameFloatAdd, nameFloatMul, nameFloatDiv, nameFloatSub, nameFloatAbs, nameFloatSqrt,
                      nameFloatShowFixed, nameFloatShowExpX,
                      nameFloatEq, nameFloatLt, nameFloatLe, nameFloatGt, nameFloatGe,
                      nameCoreIntShow,
                      nameCoreCharLt, nameCoreCharLtEq, nameCoreCharGt, nameCoreCharGtEq, nameCoreCharEq,
                      nameStringEq, nameCoreStringToUpper, nameCoreStringToLower, nameCoreStringContains, nameCoreStringCount, nameCoreStringExternRepeatZ,
                      nameCoreCharToString, nameCoreStringListChar, nameCoreStringVectorJoin, nameCoreVectorUnvlist,
                      nameCoreSliceString, nameCoreSliceXStartsWith, nameCoreSliceLength,
                      nameCoreStringJoinSep, nameCoreStringJoin,
                      nameCoreTypesExternAppend, nameCoreIntExternShow,
                      nameCoreCharInt, nameNumInt32Int, nameCoreIntExternSSizeT, nameNumInt32Int32,
                      namePretendDecreasing, nameUnsafeTotalCast, nameUnsafeNoLocalCast,
                      nameNumRandom, nameNumSRandomFloat64,
                      nameCoreTrace, nameCoreTraceShow,
                      nameCorePrint, nameCorePrintln, nameCorePrintsLn,
                      nameLocalGet, nameLocalSet,
                      nameHandle, nameHTag, nameEvvAt, nameLocalNew, nameLocalVar,
                      nameInternalSSizeT,
                      nameCCtxEmpty, nameCCtxExtend, nameCCtxCompose, nameCCtxComposeExtend, nameCCtxApply,
                      nameCCtxHoleCreate, nameFieldAddrOf,
                      nameOSReadline, nameCoreXParse, nameCoreMInt
                      ]
  in -- trace (show tn ++ " isPrimitive: " ++ show nameCCtxCompose) $
       basics || isNamePerform (getName tn) || isClauseName (getName tn)


unmakeOpHidden :: Name -> [Char] -> Name
unmakeOpHidden opName ('@':'v':'a':'l':'-':op) = opName
unmakeOpHidden opName ('-':rest) = newName rest
unmakeOpHidden opName (_:rest) = unmakeOpHidden opName rest

isTailOpOrVal :: [Char] -> Bool
isTailOpOrVal ('@':'v':'a':'l':'-':op) = True
isTailOpOrVal ('-':rest) = isTailOp $ newName rest
isTailOpOrVal (_:rest) = isTailOpOrVal rest

isTailOp :: Name -> Bool
isTailOp tn = nameStem tn `startsWith` "clause-tail"

isTailOpT :: TName -> Bool
isTailOpT tn = isTailOp (getName tn)

isNeverOp :: TName -> Bool
isNeverOp tn = nameStem (getName tn) `startsWith` "clause-never"

isTrickyPrimitive :: TName -> Bool
isTrickyPrimitive n = getName n `elem` [nameCoreStringJoin, nameCoreStringJoinSep]

equalPrimitive :: TName -> TName
equalPrimitive name | getName name == nameCoreStringJoin = name{getName = nameCoreStringJoin2}
equalPrimitive name | getName name == nameCoreStringJoinSep = name{getName = nameCoreStringJoinSep2}
equalPrimitive name = name