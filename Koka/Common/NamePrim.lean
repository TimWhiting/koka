/-
  Ported from Haskell Koka:
  File:   src/Common/NamePrim.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
import Koka.Common.Name
import Koka.Common.Syntax

namespace Koka.Common.NamePrim

open Koka.Common.Name

--------------------------------------------------------------------------
-- Special
--------------------------------------------------------------------------
def nameExpr := newName "@expr"
def nameType := newName "@type"

def nameInteractiveModule := newModuleName "interactive"

def nameMain   := newName "@main"
def nameCopy   := newName "@copy"
def nameOpExpr := newName "@opexpr"

def copyNameOf (typeName : Name) : Name :=
  typeQualifiedNameOf typeName nameCopy

def nameIf   := newName "if"
def nameCase := newName "case"

--------------------------------------------------------------------------
-- Core
--------------------------------------------------------------------------
def nameSystemCore := newModuleName "std/core"

def preludeName (s : String) : Name := qualify nameSystemCore (newName s)

def nameTpIO        := preludeName "io"
def nameTpNamed     := preludeName "nmd"
def nameTpScope     := preludeName "scope"
def nameTpPure      := preludeName "pure"

def nameTpAsync     := newQualified "std/async" "async"
def nameTpAsyncX    := newQualified "std/async" "asyncx"
def nameTpBuilder   := newQualified "std/text/string" "builder"
def nameTpArray     := newQualified "std/data/array" "array"

def nameDict        := newModuleName "std/data/dict"
def nameTpMDict     := qualify nameDict (newName "mdict")
def nameTpDict      := qualify nameDict (newName "dict")

def nameTpDelay     := preludeName "delay"
def nameMainConsole := preludeName "main-console"

def coreStringName (s : String) : Name := newQualified "std/core/string" s
def nameSubStr1     := coreStringName "substr1"

def namesSameSize   : List Name := List.map preludeName ["id","map","reverse","foldl","foldr","filter"]


--------------------------------------------------------------------------
-- Lists
--------------------------------------------------------------------------
def nameCoreTypes := newModuleName "std/core/types"
def coreTypesName (s : String) : Name := qualify nameCoreTypes (newName s)

def nameListNil     := coreTypesName "Nil"
def nameCons        := coreTypesName "Cons"
def nameTpList      := coreTypesName "list"

--------------------------------------------------------------------------
-- std/core/debug
--------------------------------------------------------------------------
def nameCoreDebug   := newModuleName "std/core/debug"

def nameAssert      := qualify nameCoreDebug (newName "assert")
def nameTrace       := qualify nameCoreDebug (newName "trace")
def nameLog         := qualify nameCoreDebug (newName "log")

def nameCoreFileFile   := qualify nameCoreDebug (newLocallyQualified "" "file" "kk-file")
def nameCoreFileLine   := qualify nameCoreDebug (newLocallyQualified "" "file" "kk-line")
def nameCoreFileModule := qualify nameCoreDebug (newLocallyQualified "" "file" "kk-module")

--------------------------------------------------------------------------
-- std/core/lazy
--------------------------------------------------------------------------
def coreLazyName (s : String) : Name := newQualified "std/core/lazy" s

def nameLazyMemoizeTarget := coreLazyName "memoize-target"
def nameLazyMemoize       := coreLazyName "memoize"
def nameLazyEnter         := coreLazyName "atomic-enter"
def nameLazyLeave         := coreLazyName "atomic-leave"
def nameLazyIsWhnf        := coreLazyName "datatype-is-whnf"
def nameLazyPtrIsWhnf     := coreLazyName "datatype-ptr-is-whnf"
def nameDataTypePtrIsUnique := coreLazyName "datatype-ptr-is-unique"
def nameDataTypePtrIsThreadShared := coreLazyName "datatype-ptr-is-thread-shared"
def nameLazyIndirectCompress := coreLazyName "indirect-compress"

--------------------------------------------------------------------------
-- std/core/vector
--------------------------------------------------------------------------
def coreVectorName (s : String) : Name := newQualified "std/core/vector" s

def nameVector              := coreVectorName "unvlist"
def nameVectorFromList      := newLocallyQualified "std/core/vector" "list" "vector"
def nameVectorUnsafeCreate  := coreVectorName "@unsafe-vector"

--------------------------------------------------------------------------
-- std/core/int
--------------------------------------------------------------------------
def nameByte        := newQualified "std/core/int"  "uint8"
def nameInt8        := newQualified "std/core/int"  "int8"
def nameInt16       := newQualified "std/core/int"  "int16"
def nameInt32       := newQualified "std/num/int32" "int32"
def nameInt64       := newQualified "std/num/int64" "int64"
def nameSSizeT      := newQualified "std/core/int"  "ssize_t"
def nameIntPtrT     := newQualified "std/core/int"  "intptr_t"

def coreIntName (s : String) : Name := newQualified "std/core/int" s
def nameIntAdd      := coreIntName "int-add"
def nameIntSub      := coreIntName "int-sub"

def nameInternalInt32  := coreTypesName "@make-int32"
def nameInternalSSizeT := coreTypesName "@make-ssize_t"

def nameIntConst    := coreTypesName "@int-const"

--------------------------------------------------------------------------
-- std/core/exn
--------------------------------------------------------------------------
def coreExnName (s : String) : Name := newQualified "std/core/exn" s

def nameTpException := coreExnName "exception"
def nameTpPartial   := coreExnName "exn"
def namePatternMatchError := coreExnName "error-pattern"

--------------------------------------------------------------------------
-- Contexts: std/core/types
--------------------------------------------------------------------------
def cfieldName (name : String) : Name := coreTypesName name

def nameTpCCtxx       := cfieldName "cctx"
def nameTpCCtx        := cfieldName "ctx"

def nameEtaHole       := newName "_"

def nameCCtxCreate    := cfieldName "@cctx-create"
def nameCCtxHoleCreate:= cfieldName "@cctx-hole-create"
def nameCCtxExtend    := cfieldName "@cctx-extend"
def nameCCtxComposeExtend := cfieldName "@cctx-compose-extend"
def nameCCtxSetCtxPath:= cfieldName "@cctx-setcp"

def nameCCtxEmpty     := newLocallyQualified "std/core/types" "cctx" "empty"
def nameCCtxApply     := newLocallyQualified "std/core/types" "cctx" "++."
def nameCCtxCompose   := newLocallyQualified "std/core/types" "cctx" "++"

def nameTpFieldAddr   := cfieldName "@field-addr"
def nameFieldAddrOf   := cfieldName "@field-addr-of"

--------------------------------------------------------------------------
-- std/core/hnd
--------------------------------------------------------------------------
def nameCoreHnd := newModuleName "std/core/hnd"
def coreHndName (s : String) : Name := qualify nameCoreHnd (newName s)

def nameTpMarker    := coreHndName "marker"
def nameTpHTag      := coreHndName "htag"
def nameTpClause (i : Int) := coreHndName (s!"clause{i}")
def nameTpEv        := coreHndName "ev"
def nameTpEvv       := coreHndName "evv"
def nameTpEvIndex   := coreHndName "ev-index"
def nameClause (sort : String) (i : Int) := coreHndName (s!"clause-{sort}{i}")
def nameTpResumeContext := coreHndName "resume-context"

def nameHTag        := coreHndName "@new-htag"
def namePerform (i : Int) := coreHndName (s!"@perform{i}")
def nameEvvAt       := coreHndName "@evv-at"
def nameEvvIndex    := coreHndName "@evv-index"
def nameEvvIndexMask:= coreHndName "@evv-index-mask"
def nameMaskAt      := coreHndName "@mask-at"
def nameMaskBuiltin := coreHndName "@mask-builtin"
def nameOpenAt (i : Int) := coreHndName (s!"@open-at{i}")
def nameOpenNone (i : Int) := coreHndName (s!"@open-none{i}")
def nameOpen (i : Int) := coreHndName (s!"@open{i}")
def nameEvvIsAffine := coreHndName "@evv-is-affine"

def nameHandle      := coreHndName "@hhandle"
def nameNamedHandle := coreHndName "@named-handle"

def nameYielding    := coreHndName "yielding"
def nameYieldExtend := coreHndName "yield-extend"
def nameBind        := coreHndName "yield-bind"
def nameBind2       := coreHndName "yield-bind2"
def nameEffectOpen  := coreTypesName "@open"

def nameInitially   := coreHndName "initially"
def nameFinally     := coreHndName "finally"

def nameClauseTailNoOp (n : Int) := coreHndName (s!"clause-tail-noop{n}")

def isClauseTailName (name : Name) : Option Int :=
  if name.module != nameCoreHnd.module then none
  else
    let s := nameLocal name
    if s.startsWith "clause-tail" && (s.drop 11).toString.toList.all Char.isDigit && s.length > 11 then
      (s.drop 11).toString.toInt?
    else none

--------------------------------------------------------------------------
-- std/core/types (cont)
--------------------------------------------------------------------------
def nameToAny       := coreTypesName "@toany"
def nameValueOp     := coreTypesName "@Valueop"
def nameTpValueOp   := coreTypesName "@valueop"

def nameCoreUndiv   := newModuleName "std/core/undiv"
def nameCoreUnsafe  := newModuleName "std/core/unsafe"

def nameDecreasing  := qualify nameCoreUndiv (newName "pretend-decreasing")
def nameUnsafeTotal := qualify nameCoreUnsafe (newName "unsafe-total")

def nameIndex       := newHiddenName "index"
def nameReturn      := newHiddenName "return"
def nameAssign      := newHiddenName "@assign"

def nameRefSet      := coreTypesName "set"
def nameLocalSet    := coreTypesName "local-set"
def nameLocalGet    := coreTypesName "local-get"
def nameDeref       := qualifyLocally (newModuleName "ref") (coreTypesName "!")
def nameByref       := coreTypesName "@byref"

def nameTypeHeapDiv := coreTypesName "hdiv"
def nameEvHeapDiv   := coreTypesName "@Hdiv"
def nameEvHeapNoDiv := coreTypesName "@Hnodiv"
def nameHeapDiv     := newName "hdiv"

def nameTpRef       := coreTypesName "ref"
def nameTpLocalVar  := coreTypesName "local-var"
def nameTpLocal     := coreTypesName "local"
def nameRef         := coreTypesName "ref"
def nameLocalNew    := coreTypesName "local-new"
def nameLocalVar    := coreHndName   "local-var"
def nameRunLocal    := coreTypesName "local-scope"

def nameEffectEmpty := coreTypesName "total"
def nameTpTotal     := nameEffectEmpty
def nameTpDiv       := coreTypesName "div"
def nameTpAlloc     := coreTypesName "alloc"
def nameTpRead      := coreTypesName "read"
def nameTpWrite     := coreTypesName "write"
def nameTpST        := coreTypesName "st"

def nameEffectExtend:= coreTypesName "effect-extend"
def nameEffectAppend:= newName "@effect-append"

def nameAnd         := coreTypesName "&&"
def nameOr          := coreTypesName "||"

def makeTpHandled (named : Bool) (linear : Bool) : Name :=
  coreTypesName (if named then "nhandled" else "handled" ++ if linear then "1" else "")

def nameTpHandled   := makeTpHandled false false
def nameTpHandled1  := makeTpHandled false true
def nameTpNHandled  := makeTpHandled true false
def nameTpNHandled1 := makeTpHandled true true

def nameIdentity    := coreTypesName "id"

def nameUnit        := coreTypesName "Unit"
def nameTrue        := coreTypesName "True"
def nameFalse       := coreTypesName "False"

def nameJust        := coreTypesName "Just"
def nameNothing     := coreTypesName "Nothing"
def nameTpMaybe     := coreTypesName "maybe"

def nameOptional    := coreTypesName "@Optional"
def nameOptionalNone:= coreTypesName "@None"
def nameTpOptional  := coreTypesName "@optional"

def nameTpVoid      := coreTypesName "void"
def nameTpUnit      := coreTypesName "unit"
def nameTpBool      := coreTypesName "bool"
def nameTpInt       := coreTypesName "int"

def nameTpInt8      := coreTypesName "int8"
def nameTpInt16     := coreTypesName "int16"
def nameTpInt32     := coreTypesName "int32"
def nameTpInt64     := coreTypesName "int64"
def nameTpSSizeT    := coreTypesName "ssize_t"
def nameTpIntPtrT   := coreTypesName "intptr_t"

def nameTpFloat     := coreTypesName "float64"
def nameTpFloat32   := coreTypesName "float32"
def nameTpFloat16   := coreTypesName "float16"

def nameTpChar      := coreTypesName "char"
def nameTpString    := coreTypesName "string"
def nameTpAny       := coreTypesName "any"
def nameTpVector    := coreTypesName "vector"

def nameTpBox       := coreTypesName "@box"
def nameBoxCon      := coreTypesName "@Box"
def nameBox         := coreTypesName "@box"
def nameUnbox       := coreTypesName "@unbox"

def nameTpReuse     := coreTypesName "@reuse"
def nameReuseNull   := coreTypesName "@no-reuse"
def nameDropReuse   := coreTypesName "@drop-reuse"
def nameFreeReuse   := coreTypesName "@free-reuse"
def nameAllocAt     := coreTypesName "@alloc-at"
def nameAssignReuse := coreTypesName "@assign-reuse"
def nameReuse       := coreTypesName "@reuse"
def nameReuseIsValid:= coreTypesName "@reuse-is-valid"
def nameConFieldsAssign := coreTypesName "@con-fields-assign"
def nameConTagFieldsAssign := coreTypesName "@con-tag-fields-assign"
def nameConTagScanFieldsAssign := coreTypesName "@con-tag-scan-fields-assign"
def nameSetTag      := coreTypesName "@set-tag"
def nameKeep        := coreTypesName "keep"

def nameDup         := coreTypesName "@dup"
def nameDrop        := coreTypesName "@drop"
def nameFree        := coreTypesName "@free"
def nameDecRef      := coreTypesName "@dec-ref"
def nameIsUnique    := coreTypesName "@is-unique"
def nameKeepMatch   := coreTypesName "@keep-match"
def nameDropMatch   := coreTypesName "@drop-match"
def nameReuseMatch  := coreTypesName "@reuse-match"

def nameReuseDrop   := coreTypesName "@reuse-drop"

def nameDropSpecial := coreTypesName "@drop-special"

def nameTuple (n : Int) : Name :=
  if n <= 1 then nameUnit else coreTypesName (s!"Tuple{n}")

def nameTpTuple (n : Int) : Name :=
  if n <= 1 then nameTpUnit else coreTypesName (s!"tuple{n}")

def isNameTuple (name : Name) : Bool :=
  name == nameUnit ||
  (name.module == nameCoreTypes.module &&
   (nameLocal name).startsWith "Tuple" &&
   ((nameLocal name).drop 5).toString.toList.all Char.isDigit && (nameLocal name).length > 5)

def isNameTpTuple (name : Name) : Bool :=
  name == nameTpUnit ||
  (name.module == nameCoreTypes.module &&
   (nameLocal name).startsWith "tuple" &&
   ((nameLocal name).drop 5).toString.toList.all Char.isDigit && (nameLocal name).length > 5)

def isSystemCoreName (name : Name) : Bool :=
  let m := name.module
  m == "std/core" || m.startsWith "std/core/"

def shortenSystemCoreName (name : Name) : Name :=
  let m := name.module
  if m == "std/core" || m == "std/core/types" || m == "std/core/exn" then unqualify name
  else if m.startsWith "std/core/" then qualify (newModuleName ((m.drop 9).toString)) (unqualify name)
  else name

def isPrimitiveModule (name : Name) : Bool :=
  name == nameCoreHnd || name == nameCoreTypes

def isPrimitiveName (name : Name) : Bool :=
  isPrimitiveModule (qualifier name)

--------------------------------------------------------------------------
-- Primitive kind constructors
--------------------------------------------------------------------------
def nameKindStar    := newName "V"
def nameKindLabel   := newName "X"
def nameKindFun     := newName "->"
def nameKindEffect  := newName "E"
def nameKindHeap    := newName "H"
def nameKindScope   := newName "S"
def nameKindHandled := newName "HX"
def nameKindHandled1 := newName "HX1"

end Koka.Common.NamePrim
