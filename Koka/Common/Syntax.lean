/-
  Ported from Haskell Koka:
  File:   src/Common/Syntax.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
namespace Koka.Common.Syntax

inductive JsTarget
  | JsDefault | JsNode | JsWeb
  deriving Inhabited, Repr, DecidableEq

inductive CTarget
  | CDefault | LibC | Wasm | WasmJs | WasmWeb
  deriving Inhabited, Repr, DecidableEq

inductive Target
  | CS
  | JS (t : JsTarget)
  | C (t : CTarget)
  | Default
  deriving Inhabited, Repr, DecidableEq

def isTargetC : Target → Bool
  | Target.C _ => true
  | _ => false

def isTargetJS : Target → Bool
  | Target.JS _ => true
  | _ => false

def isTargetWasm : Target → Bool
  | Target.C CTarget.Wasm => true
  | Target.C CTarget.WasmJs => true
  | Target.C CTarget.WasmWeb => true
  | _ => false

instance : ToString Target where
  toString tgt :=
    match tgt with
    | Target.CS => "cs"
    | Target.JS JsTarget.JsWeb => "jsweb"
    | Target.JS JsTarget.JsNode => "jsnode"
    | Target.JS _ => "js"
    | Target.C CTarget.Wasm => "wasm"
    | Target.C CTarget.WasmJs => "wasmjs"
    | Target.C CTarget.WasmWeb => "wasmweb"
    | Target.C CTarget.LibC => "libc"
    | Target.C _ => "c"
    | Target.Default => ""

structure Platform where
  sizePtr : Int
  sizeSize : Int
  sizeField : Int
  sizeHeader : Int
  deriving Inhabited, Repr, DecidableEq

def platform32 : Platform := ⟨4, 4, 4, 8⟩
def platform64 : Platform := ⟨8, 8, 8, 8⟩
def platform64c : Platform := ⟨8, 8, 4, 8⟩
def platformJS : Platform := ⟨8, 4, 8, 0⟩
def platformCS : Platform := ⟨8, 4, 8, 0⟩

def platformHasCompressedFields (p : Platform) : Bool :=
  p.sizePtr ≠ p.sizeField

instance : ToString Platform where
  toString p :=
    s!"Platform(sizeof(void*)={p.sizePtr},sizeof(size_t)={p.sizeSize},sizeof(kk_box_t)={p.sizeField},sizeof(kk_header_t)={p.sizeHeader})"

def alignUp (x y : Int) : Int :=
  if y ≤ 0 then x
  else ((x + y - 1) / y) * y

def alignedAdd (x y : Int) : Int :=
  alignUp x y + y

def alignedSum (start : Int) (xs : List Int) : Int :=
  xs.foldl alignedAdd start

inductive BuildType
  | DebugFull | Debug | RelWithDebInfo | Release
  deriving Inhabited, Repr, DecidableEq

instance : ToString BuildType where
  toString
  | BuildType.DebugFull => "debugfull"
  | BuildType.Debug => "debug"
  | BuildType.RelWithDebInfo => "drelease"
  | BuildType.Release => "release"

inductive Visibility
  | Public | Private
  deriving Inhabited, Repr, DecidableEq

def isPublic : Visibility → Bool
  | Visibility.Public => true
  | _ => false

def isPrivate : Visibility → Bool
  | Visibility.Private => true
  | _ => false

inductive HandlerSort
  | HandlerNormal | HandlerInstance
  deriving Inhabited, Repr, DecidableEq

instance : ToString HandlerSort where
  toString
  | HandlerSort.HandlerNormal => "normal"
  | HandlerSort.HandlerInstance => "named"

def isHandlerInstance : HandlerSort → Bool
  | HandlerSort.HandlerInstance => true
  | _ => false

def isHandlerNormal : HandlerSort → Bool
  | HandlerSort.HandlerNormal => true
  | _ => false

inductive OperationSort
  | OpVal | OpFun | OpExcept | OpControlRaw | OpControl | OpControlErr
  deriving Inhabited, Repr, DecidableEq

instance : ToString OperationSort where
  toString
  | OperationSort.OpVal => "val"
  | OperationSort.OpFun => "fun"
  | OperationSort.OpExcept => "final ctl"
  | OperationSort.OpControl => "ctl"
  | OperationSort.OpControlRaw => "raw ctl"
  | OperationSort.OpControlErr => ""

def opSortString : OperationSort → String
  | OperationSort.OpVal => "val"
  | OperationSort.OpFun => "fun"
  | OperationSort.OpExcept => "brk"
  | OperationSort.OpControl => "ctl"
  | OperationSort.OpControlRaw => "rawctl"
  | OperationSort.OpControlErr => ""

def readOperationSort (s : String) : Option OperationSort :=
  match s with
  | "val" => some OperationSort.OpVal
  | "fun" => some OperationSort.OpFun
  | "brk" => some OperationSort.OpExcept
  | "ctl" => some OperationSort.OpControl
  | "rawctl" => some OperationSort.OpControlRaw
  | "except" => some OperationSort.OpExcept
  | "control" => some OperationSort.OpControl
  | "rcontrol" => some OperationSort.OpControlRaw
  | _ => none

structure DataEffect where
  isNamed : Bool
  isLinear : Bool
  deriving Inhabited, Repr, DecidableEq

inductive DataKind
  | Inductive | CoInductive | Retractive
  deriving Inhabited, Repr, DecidableEq

instance : ToString DataKind where
  toString
  | DataKind.Inductive => "type"
  | DataKind.CoInductive => "co type"
  | DataKind.Retractive => "div type"

structure ValueRepr where
  rawSize : Int
  scanCount : Int
  alignment : Int
  deriving Inhabited, Repr, DecidableEq

instance : ToString ValueRepr where
  toString v := s!"\{{v.rawSize},{v.scanCount},{v.alignment}}"

def valueReprSize (platform : Platform) (vrepr : ValueRepr) : Int :=
  vrepr.rawSize + (vrepr.scanCount * platform.sizeField)

def valueReprSizeScan (platform : Platform) (vrepr : ValueRepr) : Int × Int :=
  (valueReprSize platform vrepr, vrepr.scanCount)

def valueReprIsMixed (v : ValueRepr) : Bool :=
  v.rawSize > 0 && v.scanCount > 0

def valueReprIsRaw (v : ValueRepr) : Bool :=
  v.rawSize > 0 && v.scanCount == 0

def valueReprNew (rawSize scanCount align : Int) : ValueRepr :=
  ⟨rawSize, scanCount, align⟩

def valueReprZero : ValueRepr :=
  ⟨0, 0, 0⟩

def valueReprRaw (m : Int) : ValueRepr :=
  ⟨m, 0, m⟩

def valueReprScan (n : Int) : ValueRepr :=
  ⟨0, n, 0⟩

inductive FipAlloc
  | AllocAtMost (n : Int)
  | AllocFinitely
  | AllocUnlimited
  deriving Inhabited, Repr, DecidableEq

inductive Fip
  | Fip (alloc : FipAlloc)
  | Fbip (alloc : FipAlloc) (isTail : Bool)
  | NoFip (isTail : Bool)
  deriving Inhabited, Repr, DecidableEq

def fipTail : Fip → Bool
  | Fip.Fbip _ t => t
  | Fip.NoFip t => t
  | _ => true

def fipAlloc : Fip → FipAlloc
  | Fip.Fip n => n
  | Fip.Fbip n _ => n
  | Fip.NoFip _ => FipAlloc.AllocUnlimited

def fipAllocGe (a1 a2 : FipAlloc) : Bool :=
  match a1, a2 with
  | FipAlloc.AllocUnlimited, _ => true
  | _, FipAlloc.AllocUnlimited => false
  | FipAlloc.AllocFinitely, _ => true
  | _, FipAlloc.AllocFinitely => false
  | FipAlloc.AllocAtMost n, FipAlloc.AllocAtMost m => n ≥ m

def fipSubsumes : Fip → Fip → Bool
  | Fip.NoFip _, Fip.Fip _ => true
  | Fip.NoFip t1, f2 => not t1 || fipTail f2
  | Fip.Fbip a1 t1, Fip.Fbip a2 t2 => fipAllocGe a1 a2 && (not t1 || t2)
  | Fip.Fbip a1 _, Fip.Fip a2 => fipAllocGe a1 a2
  | Fip.Fip a1, Fip.Fip a2 => fipAllocGe a1 a2
  | _, _ => false

def fipAllocMax (a1 a2 : FipAlloc) : FipAlloc :=
  match a1, a2 with
  | FipAlloc.AllocUnlimited, _ => FipAlloc.AllocUnlimited
  | _, FipAlloc.AllocUnlimited => FipAlloc.AllocUnlimited
  | FipAlloc.AllocFinitely, _ => FipAlloc.AllocFinitely
  | _, FipAlloc.AllocFinitely => FipAlloc.AllocFinitely
  | FipAlloc.AllocAtMost n1, FipAlloc.AllocAtMost n2 => FipAlloc.AllocAtMost (max n1 n2)

def fipMax (fip1 fip2 : Fip) : Fip :=
  match fip1, fip2 with
  | Fip.NoFip t1, Fip.NoFip t2 => Fip.NoFip (t1 && t2)
  | Fip.NoFip t1, _ => Fip.NoFip (t1 && fipTail fip2)
  | _, Fip.NoFip t2 => Fip.NoFip (fipTail fip1 && t2)
  | Fip.Fbip a1 t1, Fip.Fbip a2 t2 => Fip.Fbip (fipAllocMax a1 a2) (t1 && t2)
  | Fip.Fbip a1 t1, Fip.Fip a2 => Fip.Fbip (fipAllocMax a1 a2) t1
  | Fip.Fip a1, Fip.Fbip a2 t2 => Fip.Fbip (fipAllocMax a1 a2) t2
  | Fip.Fip a1, Fip.Fip a2 => Fip.Fip (fipAllocMax a1 a2)

def fipBot : Fip := Fip.Fip (FipAlloc.AllocAtMost 0)
def fipTop : Fip := Fip.NoFip false
def fipNoAlloc : Fip := fipBot

def isNoFip : Fip → Bool
  | Fip.NoFip _ => true
  | _ => false

def isFipTop : Fip → Bool
  | Fip.NoFip false => true
  | _ => false

inductive DataDef
  | DataDefValue (v : ValueRepr)
  | DataDefNormal
  | DataDefLazy (fip : Fip)
  | DataDefOpen (isExtend : Bool)
  | DataDefAuto (declaredAsStruct : Bool)
  deriving Inhabited, Repr, DecidableEq

instance : ToString DataDef where
  toString
  | DataDef.DataDefValue v => "value" ++ toString v
  | DataDef.DataDefNormal => "reference"
  | DataDef.DataDefLazy _ => "lazy" -- TODO: improve
  | DataDef.DataDefOpen isExtend => if isExtend then "extend" else "open"
  | DataDef.DataDefAuto isStruct => "auto" ++ (if isStruct then " struct" else "")

def dataDefIsExtend : DataDef → Bool
  | DataDef.DataDefOpen isExtend => isExtend
  | _ => false

def dataDefIsOpen : DataDef → Bool
  | DataDef.DataDefOpen _ => true
  | _ => false

def dataDefIsValue : DataDef → Bool
  | DataDef.DataDefValue _ => true
  | _ => false

def dataDefIsNormal : DataDef → Bool
  | DataDef.DataDefNormal => true
  | _ => false

def dataDefIsLazy : DataDef → Bool
  | DataDef.DataDefLazy _ => true
  | _ => false

def dataDefSize (platform : Platform) : DataDef → Int
  | DataDef.DataDefValue v => valueReprSize platform v
  | _ => platform.sizeField

inductive ParamInfo
  | Borrow | Own
  deriving Inhabited, Repr, DecidableEq

inductive DefSort
  | DefFun (paramInfos : List ParamInfo) (fip : Fip)
  | DefVal
  | DefVar
  deriving Inhabited, Repr, DecidableEq

def isDefFun : DefSort → Bool
  | DefSort.DefFun _ _ => true
  | _ => false

def defFunEx (pinfos : List ParamInfo) (fip : Fip) : DefSort :=
  if pinfos.all (· == ParamInfo.Own) then
    DefSort.DefFun [] fip
  else
    DefSort.DefFun pinfos fip

def noFip : Fip := fipTop

def defFun (pinfos : List ParamInfo) : DefSort :=
  defFunEx pinfos noFip

instance : ToString DefSort where
  toString
  | DefSort.DefFun _ _ => "fun"
  | DefSort.DefVal => "val"
  | DefSort.DefVar => "var"

inductive DefInline
  | InlineNever | InlineAlways | InlineAuto
  deriving Inhabited, Repr, DecidableEq

instance : ToString DefInline where
  toString
  | DefInline.InlineNever => "noinline"
  | DefInline.InlineAlways => "inline"
  | DefInline.InlineAuto => "autoinline"

inductive Assoc
  | AssocNone | AssocRight | AssocLeft
  deriving Inhabited, Repr, DecidableEq

inductive Fixity
  | FixInfix (prec : Int) (assoc : Assoc)
  | FixPrefix
  | FixPostfix
  deriving Inhabited, Repr, DecidableEq

def sepBySpace (xs : List String) : String :=
  String.intercalate " " (xs.filter (not ∘ String.isEmpty))

def memberDoc (doc header : String) (members : List String) : String :=
  let mdoc := "// " ++ header ++ ":\n// ```koka\n" ++
              String.join (members.map (fun m => "// " ++ m ++ "\n")) ++
              "// ```\n"
  if doc.isEmpty then mdoc else doc ++ "\n// * * *\n" ++ mdoc

end Koka.Common.Syntax
