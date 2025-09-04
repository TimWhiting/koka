
module Core.FlowAnalysis.Full.PrimComm where
import Core.Core
import Common.Name
import Common.NamePrim
import Common.File (startsWith)

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


primitiveFuncWrappers = [nameUnsafeNoLocalCast, nameUnsafeTotalCast]

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
                      nameFloatAdd, nameFloatMul, nameFloatDiv, nameFloatSub, nameFloatAbs, nameFloatSqrt,
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
                      nameInternalSSizeT
                      ]
  in basics || isNamePerform (getName tn) || isClauseName (getName tn)
