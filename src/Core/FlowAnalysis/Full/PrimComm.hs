
module Core.FlowAnalysis.Full.PrimComm where
import Core.Core
import Common.Name
import Common.NamePrim
import Common.File (startsWith)
import qualified Data.Map.Strict as M
import Numeric (showFFloat, showEFloat)
import Data.List (dropWhileEnd)

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
nameCoreStringListChar = newQualified "std/core/string" "list"
nameCoreSliceString = newQualified "std/core/sslice" "@extern-string"
nameCoreStringToUpper = newQualified "std/core/string" "@extern-to-upper"
nameCoreStringExternRepeatZ = newQualified "std/core/string" "@extern-repeatz"
nameCoreStringCount = newLocallyQualified "std/core/string" "chars" "@extern-count"
nameOSReadline = newQualified "std/os/readline" "readline"
nameStringEq = newQualified "std/core/string" "=="

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

showFFloatNoZeros :: Int -> Double -> String
showFFloatNoZeros numDigits f =
    let sigDigits = length $ show $ truncate f
        decimalDigits = if numDigits > 0 then numDigits else abs numDigits - sigDigits
        formatted = showFFloat (Just decimalDigits) f ""
    in removeTrailingZeros formatted

showEFloatNoZeros :: Int -> Double -> String
showEFloatNoZeros numDigits f =
    let sigDigits = length $ show $ truncate f
        decimalDigits = if numDigits > 0 then numDigits else abs numDigits - sigDigits
        formatted = showEFloat (Just decimalDigits) f ""
    in removeETrailingZeros formatted

removeETrailingZeros :: String -> String
removeETrailingZeros s =
    let (whole, frac) = break (== 'e') s
        (fracPart, expPart) = break (== 'E') frac
        fracCleaned = removeTrailingZeros fracPart
    in case expPart of
        [] -> whole ++ fracCleaned
        _  -> whole ++ fracCleaned ++ expPart

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
                      nameFloatAdd, nameFloatMul, nameFloatDiv, nameFloatSub, nameFloatAbs, nameFloatSqrt,
                      nameFloatShowFixed, nameFloatShowExpX,
                      nameFloatEq, nameFloatLt, nameFloatLe, nameFloatGt, nameFloatGe,
                      nameCoreIntShow,
                      nameCoreCharLt, nameCoreCharLtEq, nameCoreCharGt, nameCoreCharGtEq, nameCoreCharEq,
                      nameStringEq, nameCoreStringToUpper, nameCoreStringCount, nameCoreStringExternRepeatZ,
                      nameCoreCharToString, nameCoreStringListChar, nameCoreSliceString,
                      nameCoreTypesExternAppend, nameCoreIntExternShow,
                      nameCoreCharInt, nameNumInt32Int, nameCoreIntExternSSizeT, nameNumInt32Int32,
                      namePretendDecreasing, nameUnsafeTotalCast, nameUnsafeNoLocalCast,
                      nameNumRandom, nameNumSRandomFloat64,
                      nameCoreTrace, nameCoreTraceShow,
                      nameCorePrint, nameCorePrintln, nameCorePrintsLn,
                      nameLocalGet, nameLocalSet,
                      nameHandle, nameHTag, nameEvvAt, nameLocalNew, nameLocalVar,
                      nameInternalSSizeT,
                      nameOSReadline, nameCoreXParse, nameCoreMInt
                      ]
  in basics || isNamePerform (getName tn) || isClauseName (getName tn)


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
isTrickyPrimitive n = getName n `elem` [nameCoreXParse]

equalPrimitive :: TName -> TName
equalPrimitive name | getName name == nameCoreXParse = name{getName = nameCoreMInt}
equalPrimitive name = name