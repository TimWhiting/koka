/-
  Ported from Haskell Koka:
  File:   src/Common/Name.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
import Koka.Common.File
import Koka.Common.Id
import Koka.Common.IdSet
import Koka.Common.IdMap
import Koka.Lib.PPrint
import Koka.Common.ColorScheme

namespace Koka.Common.Name

open Koka.Common.File

-- We use `String` directly to simplify, the hash functions will be implemented as well.
structure Name where
  module     : String
  hashModule : Int
  localQual  : String
  hashLocalQual : Int
  stem       : String
  hashStem   : Int
  deriving Repr, Inhabited

abbrev ModuleName := Name

-- The hash is done taking the first 4 characters. This is of course a
-- terrible hash but we use it mostly to speed up *comparisions* for the NameMap
def hashStr (s : String) : Int :=
  -- Taking first 4 characters and adding 4 null bytes to pad if short
  let chars := (s ++ "\x00\x00\x00\x00").toList.take 4
  chars.foldl (fun h c => h * 256 + c.toLower.toNat) 0

def joinWith (sep m n : String) : String :=
  if m.isEmpty then n else if n.isEmpty then m else m ++ sep ++ n

def joinStr (m n : String) : String :=
  joinWith "/" m n

def joins (ms : List String) : String :=
  ms.foldr joinStr ""

def nameLocal (name : Name) : String :=
  joinStr name.localQual name.stem

def splitModuleName (name : Name) : List String :=
  splitOn (· == '/') name.module

def nameCaseEqual (name1 name2 : Name) : Bool :=
  nameLocal name1 == nameLocal name2 &&
  ((splitModuleName name1).reverse.zip (splitModuleName name2).reverse).all (fun (a, b) => a == b)

def isConstructorName (name : Name) : Bool :=
  match name.stem.toList with
  | '@' :: c :: _ => c.isUpper
  | c :: _ => c.isUpper
  | _ => false

def isSameNamespace (name1 name2 : Name) : Bool :=
  isConstructorName name1 == isConstructorName name2

def nameCaseOverlap (name1 name2 : Name) : Bool :=
  !nameCaseEqual name1 name2 && isSameNamespace name1 name2

def nameCaseEqualPrefixOf (name1 name2 : Name) : Bool :=
  (nameLocal name2).startsWith (nameLocal name1) &&
  ((splitModuleName name1).reverse.zip (splitModuleName name2).reverse).all (fun (a, b) => a == b)

def nameCaseOverlapPrefixOf (name1 name2 : Name) : Bool :=
  !nameCaseEqualPrefixOf name1 name2 && isSameNamespace name1 name2

def lowerCompareS (s1 s2 : List Char) : Ordering :=
  match s1, s2 with
  | _ :: cs, _ :: ds =>
    -- We can't use c and d in the pattern if they are also bound in match, so bind them explicitly:
    let c := s1.head!
    let d := s2.head!
    let cmp := compare c.toLower d.toLower
    if cmp == Ordering.eq then lowerCompareS cs ds else cmp
  | _ :: _, [] => Ordering.gt
  | [], _ :: _ => Ordering.lt
  | [], [] => Ordering.eq

def lowerCompare (name1 name2 : Name) : Ordering :=
  match lowerCompareS name1.module.toList name2.module.toList with
  | Ordering.eq =>
    match lowerCompareS name1.localQual.toList name2.localQual.toList with
    | Ordering.eq => lowerCompareS name1.stem.toList name2.stem.toList
    | lg => lg
  | lg => lg

instance : Hashable Name where
  hash nm := mixHash (hash nm.hashStem) (mixHash (hash nm.hashLocalQual) (hash nm.hashModule))

instance : BEq Name where
  beq nm1 nm2 :=
    nm1.hashStem == nm2.hashStem &&
    nm1.hashLocalQual == nm2.hashLocalQual &&
    nm1.hashModule == nm2.hashModule &&
    lowerCompare nm1 nm2 == Ordering.eq

instance : Ord Name where
  compare nm1 nm2 :=
    match compare nm1.hashModule nm2.hashModule with
    | Ordering.eq =>
      match compare nm1.hashStem nm2.hashStem with
      | Ordering.eq =>
        match compare nm1.hashLocalQual nm2.hashLocalQual with
        | Ordering.eq => lowerCompare nm1 nm2
        | lg => lg
      | lg => lg
    | lg => lg

def labelNameCompare (name1 name2 : Name) : Ordering :=
  match lowerCompareS (name1.stem ++ "@").toList (name2.stem ++ "@").toList with
  | Ordering.eq =>
    match compare name1.localQual name2.localQual with
    | Ordering.eq => compare name1.module name2.module
    | lg => lg
  | lg => lg

def stemIsEqual (name1 name2 : Name) : Bool :=
  name1.hashStem == name2.hashStem && name1.stem == name2.stem

def isIdChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '@' || c == '-'

def isIdStartChar (c : Char) : Bool :=
  c.isAlpha || c == '_' || c == '@'

def isIdEndChar (c : Char) : Bool :=
  isIdChar c || c == '\''

def isSymbolId (s : String) : Bool :=
  if s.isEmpty then false
  else !isIdStartChar s.front || !isIdEndChar s.back

def wrapId (s : String) : String :=
  if isSymbolId s then "(" ++ s ++ ")" else s

def showName (explicitLocalQualifier : Bool) (name : Name) : String :=
  let ln := joinStr name.localQual (wrapId name.stem)
  if name.module.isEmpty then ln
  else if ln.isEmpty then name.module
  else name.module ++ (if explicitLocalQualifier && !name.localQual.isEmpty then "/#" else "/") ++ ln

def showFullyExplicit (name : Name) : String :=
  let ln := joinStr name.localQual (wrapId name.stem)
  if name.module.isEmpty then "#" ++ ln
  else if ln.isEmpty then name.module
  else name.module ++ "/#" ++ ln

def showExplicit (name : Name) : String :=
  showName true name

def showPlain (name : Name) : String :=
  joinStr name.module (joinStr name.localQual name.stem)

instance : ToString Name where
  toString := showExplicit

def newLocallyQualified (m l n : String) : Name :=
  ⟨m, hashStr m, l, hashStr l, n, hashStr n⟩

def newQualified (m n : String) : Name :=
  newLocallyQualified m "" n

def newName (s : String) : Name :=
  newQualified "" s

def newModuleName (s : String) : Name :=
  newQualified s ""

def nameMapStem (name : Name) (f : String → String) : Name :=
  let fn := f name.stem
  ⟨name.module, name.hashModule, name.localQual, name.hashLocalQual, fn, hashStr fn⟩

def isModuleName (name : Name) : Bool :=
  name.stem.isEmpty

def isQualified (name : Name) : Bool :=
  !name.module.isEmpty

def isLocallyQualified (name : Name) : Bool :=
  !name.localQual.isEmpty

def isSymbolName (name : Name) : Bool :=
  isSymbolId name.stem

def isWildcard (name : Name) : Bool :=
  match name.stem.toList with
  | '_' :: _ => true
  | '@' :: '_' :: _ => true
  | _ => false

def unWildcard (post : String) (name : Name) : Name :=
  match name.stem.toList with
  | '_' :: _ => nameMapStem name (fun s => (s.drop 1).toString ++ post)
  | '@' :: '_' :: _ => nameMapStem name (fun s => "@" ++ (s.drop 2).toString ++ post)
  | _ => name

def nameIsEtaHole (name : Name) : Bool :=
  isWildcard name

def isHiddenName (name : Name) : Bool :=
  match name.stem.toList with
  | '@' :: _ => true
  | _ => false

def nameNil : Name :=
  newName ""

def nameIsNil (name : Name) : Bool :=
  name.stem.isEmpty && name.module.isEmpty

def qualify (name1 name2 : Name) : Name :=
  match name1, name2 with
  | ⟨m, hm, _, 0, _, 0⟩, ⟨_, 0, l, hl, n, hn⟩ => ⟨m, hm, l, hl, n, hn⟩
  | ⟨m1, _, _, 0, _, 0⟩, nm@⟨m2, _, _, _, _, _⟩ => if m1 == m2 then nm else panic! s!"Common.Name.qualify: illegal qualification: {m1} {nm.module}"
  | _, _ => panic! s!"Common.Name.qualify: illegal qualification"

def unqualify (name : Name) : Name :=
  ⟨"", 0, name.localQual, name.hashLocalQual, name.stem, name.hashStem⟩

def qualifier (name : Name) : Name :=
  ⟨name.module, name.hashModule, "", 0, "", 0⟩

def nameAsModuleName (name : Name) : Name :=
  newModuleName (joinStr name.module (joinStr name.localQual name.stem))

def qualifyLocally (name1 name2 : Name) : Name :=
  match name1, name2 with
  | ⟨loc, _, _, 0, _, 0⟩, ⟨m, _, l, _, n, _⟩ => newLocallyQualified m (joinStr loc l) n
  | n1, n2 => panic! s!"Common.Name.qualifyLocally: illegal qualification: {n1}, {n2}"

def requalifyLocally (name : Name) : Name :=
  if name.module.isEmpty then name else newLocallyQualified "" (joinStr name.module name.localQual) name.stem

def unqualifyFull (name : Name) : Name :=
  ⟨"", 0, "", 0, name.stem, name.hashStem⟩

def fullQualifier (name : Name) : String :=
  if name.localQual.isEmpty then name.module else joinStr name.module name.localQual

def unqualifyLocally (name : Name) : Name :=
  if name.localQual.isEmpty then name else newQualified (joinStr name.module name.localQual) name.stem

def unqualifyAsModuleName (name : Name) : Name :=
  newModuleName (joinStr name.module name.localQual)

def unsplitModuleName (xs : List String) : Name :=
  newModuleName (xs.intersperse "/" |>.foldl (· ++ ·) "")

def mergeCommonPath (mname name : Name) : Name :=
  let ns := splitModuleName name
  let ms := splitModuleName mname
  let rec merge (m : List String) (n : List String) : List String :=
    match m, n with
    | mx :: mxs, nx :: nxs =>
      if mx == nx && (mxs.zip nxs |>.all (fun (a,b) => a == b)) then (mx :: mxs) ++ nxs.drop mxs.length
      else mx :: merge mxs (nx :: nxs)
    | mx :: mxs, ns => mx :: merge mxs ns
    | [], ns => ns
  unsplitModuleName (merge ms ns)

def splitLocalQualName (name : Name) : List String :=
  splitOn (· == '/') name.localQual

def toConstructorName (name : Name) : Name :=
  nameMapStem name fun stem =>
    match stem.toList with
    | '@' :: c :: cs => String.ofList ('@' :: c.toUpper :: cs)
    | c :: cs => String.ofList (c.toUpper :: cs)
    | [] => ""

def toVarName (name : Name) : Name :=
  let rec toLowers (s : List Char) : List Char :=
    match s with
    | c :: cs => if c.isUpper then c.toLower :: toLowers cs else c :: cs
    | [] => []
  nameMapStem name fun stem =>
    match stem.toList with
    | '@' :: cs => String.ofList ('@' :: toLowers cs)
    | cs => String.ofList (toLowers cs)

def prepend (pre : String) (name : Name) : Name :=
  nameMapStem name fun stem =>
    let append p s :=
      match p.toList.reverse, s.toList with
      | '-' :: _, c :: _ => if !c.isAlpha then p ++ "x" ++ s else p ++ s
      | _, _ => p ++ s
    match stem.toList with
    | '@' :: t =>
      match pre.toList with
      | '@' :: _ => append pre (String.ofList t)
      | _ => "@" ++ append pre (String.ofList t)
    | _ => append pre stem

def postpend (post : String) (name : Name) : Name :=
  if isSymbolName name then
    nameMapStem name fun stem =>
      let (rsyms, rid) := stem.toList.reverse.span (fun c => !isIdChar c)
      let rids := String.ofList rid.reverse
      (if rids.isEmpty || rids == "@" then "@x" else rids) ++ post ++ String.ofList rsyms.reverse
  else
    nameMapStem name fun stem =>
      let (xs, ys) := stem.toList.reverse.span (fun c => c == '?' || c == '\'')
      String.ofList (xs.reverse ++ post.toList ++ ys.reverse)

def makeHidden (name : Name) : Name :=
  prepend "@" name

def makeHiddenName (s : String) (name : Name) : Name :=
  prepend ("@" ++ s ++ "-") name

def unmakeHidden (pre : String) (name : Name) : Name :=
  nameMapStem name fun stem =>
    if stem.startsWith ("@" ++ pre ++ "-") then
      (stem.drop (pre.length + 2)).toString
    else panic! s!"Name.unmakeHidden: expecting hidden name prefixed with @{pre}-, but found: {name.stem}"

def toHandlerConName (name : Name) : Name :=
  makeHiddenName "Hnd" name

def isHandlerConName (name : Name) : Bool :=
  name.stem.startsWith ("@Hnd") || name.stem.startsWith ("@Hnd-")

def nameStartsWith (name : Name) (pre : String) : Bool :=
  name.stem.startsWith pre

def typeQualifiedName (typeName : Name) (stem : String) : Name :=
  qualify (qualifier typeName) (qualifyLocally (nameAsModuleName (unqualify typeName)) (newName stem))

def typeQualifiedNameOf (typeName name : Name) : Name :=
  typeQualifiedName typeName name.stem

def typeQualifiedGetTypeName (name : Name) : Name :=
  match splitLocalQualName name |>.reverse with
  | m :: ms => newLocallyQualified name.module (joins ms.reverse) m
  | [] => panic! s!"Common.Name.typeQualifiedGetTypeName: no locally qualified type: {name}"

def newHiddenNameEx (base s : String) : Name :=
  makeHiddenName base (newName s)

def newHiddenName (base : String) : Name :=
  makeHidden (newName base)

def toUniqueName (i : Int) (name : Name) : Name :=
  postpend ("@" ++ toString i) name

def toHiddenUniqueName (i : Int) (pre : String) (name : Name) : Name :=
  makeHiddenName pre (toUniqueName i name)

def hiddenNameStartsWith (name : Name) (pre : String) : Bool :=
  name.stem.startsWith ("@" ++ pre) || name.stem.startsWith ("@" ++ pre ++ "-")

def newPaddingName (i : Int) : Name :=
  newHiddenNameEx "padding" (toString i)

def isPaddingName (name : Name) : Bool :=
  hiddenNameStartsWith name "padding"

def newCCtxName (s : String) : Name :=
  newHiddenNameEx "cctx" s

def isCCtxName (name : Name) : Bool :=
  hiddenNameStartsWith name "cctx"

def newFieldName (i : Int) : Name :=
  newHiddenNameEx "field" (toString i)

def isFieldName (name : Name) : Bool :=
  hiddenNameStartsWith name "field"

def newImplicitTypeVarName (i : Int) : Name :=
  newHiddenNameEx "tv" (toString i)

def isImplicitTypeVarName (name : Name) : Bool :=
  name.stem.startsWith "@tv"

def newHiddenExternalName (name : Name) : Name :=
  makeHiddenName "extern" name

def isHiddenExternalName (name : Name) : Bool :=
  hiddenNameStartsWith name "extern"

def newCreatorName (name : Name) : Name :=
  makeHiddenName "create" name

def isCreatorName (name : Name) : Bool :=
  hiddenNameStartsWith name "create"

def hndName := newHiddenName "hnd"
def handleName := newHiddenName "handle"
def effectTagName := newHiddenName "tag"
def effectOpsName := newHiddenName "ops"
def opsSelectName := newHiddenName "select"

def toHandlerName (typeName : Name) : Name :=
  typeQualifiedNameOf typeName hndName

def isHandlerName (name : Name) : Bool :=
  stemIsEqual hndName name

def fromHandlerName (name : Name) : Name :=
  typeQualifiedGetTypeName name

def toHandleName (typeName : Name) : Name :=
  typeQualifiedNameOf typeName handleName

def isHandleName (name : Name) : Bool :=
  stemIsEqual handleName name

def toOperationsName (typeName : Name) : Name :=
  typeQualifiedNameOf typeName effectOpsName

def isOperationsName (name : Name) : Bool :=
  stemIsEqual name effectOpsName

def fromOperationsName (name : Name) : Name :=
  typeQualifiedGetTypeName name

def toOpSelectorName (typeName : Name) : Name :=
  typeQualifiedNameOf typeName opsSelectName

def isOpSelectorName (name : Name) : Bool :=
  stemIsEqual name opsSelectName

def fromOpSelectorName (name : Name) : Name :=
  typeQualifiedGetTypeName name

def toEffectTagName (typeName : Name) : Name :=
  typeQualifiedNameOf typeName effectTagName

def toOpTypeName (name : Name) : Name :=
  makeHiddenName "op" name

def toOpConName (name : Name) : Name :=
  makeHiddenName "Op" name

def toOpsConName (name : Name) : Name :=
  makeHiddenName "Ops" name

def indirectName := newName "Indirect"

def toLazyIndirectConName (typeName : Name) : Name :=
  typeQualifiedNameOf typeName indirectName

def isLazyIndirectConName (name : Name) : Bool :=
  stemIsEqual name indirectName

def toOpenTagName (name : Name) : Name :=
  makeHiddenName "tag" name

def isOpenTagName (name : Name) : Bool :=
  hiddenNameStartsWith name "tag"

def toValueOperationName (name : Name) : Name :=
  makeHiddenName "val" name

def isValueOperationName (name : Name) : Bool :=
  hiddenNameStartsWith name "val"

def fromValueOperationsName (name : Name) : Name :=
  unmakeHidden "val" name

def toBasicOperationsName (name : Name) : Name :=
  if isValueOperationName name then unmakeHidden "val" name else name

def implicitNameSpace : String := "@implicit"

def toImplicitParamName (name : Name) : Name :=
  qualifyLocally (newModuleName implicitNameSpace) name

partial def readQualifiedName (s : String) : Name :=
  if s.startsWith "?" then
    toImplicitParamName (requalifyLocally (readQualifiedName (s.drop 1).toString))
  else
    let rec splitQualIdRev (rs : List Char) : String × String :=
      let (rid, rqual) := rs.span (· ≠ '/')
      match rqual with
      | '/' :: rs1 => (String.ofList rs1.reverse, String.ofList rid.reverse)
      | _ => ("", String.ofList rid.reverse)

    let rec splitIdNameRev (rs : List Char) : String × String × String :=
      let (rid, rest) := rs.span (· ≠ '#')
      match rest with
      | '#' :: '/' :: rs2 =>
        let (lqual, id) := splitQualIdRev rid
        (String.ofList rs2.reverse, lqual, id)
      | [] =>
        let (qual, id) := splitQualIdRev rid
        (qual, "", id)
      | _ => panic! s!"Lexer.splitName.IdName: illegal locally qualified name: {String.ofList rs.reverse}"

    let rec splitName (s : List Char) : String × String × String :=
      match s.reverse with
      | ')' :: rs1 =>
        let (rop, rest) := rs1.span (· ≠ '(')
        match rest with
        | '(' :: rs2 =>
          let (qual, lqual, id) := splitIdNameRev rs2
          (qual, lqual, id ++ (String.ofList rop.reverse))
        | _ => panic! s!"Lexer.splitName: unmatched parenthesis in name: {s}"
      | rs => splitIdNameRev rs

    let (qual, lqual, id) := splitName s.toList
    newLocallyQualified qual lqual id

def missingQualifier (currentMod name qname : Name) : String :=
  let missing0 :=
    let pnLen := (showPlain name).length
    let rq := (showPlain qname).toList.reverse
    String.ofList (rq.drop pnLen).reverse
  let standard := [showPlain currentMod, "std/core/types", "std/core/hnd", "std/core"]
  let rec findMissing stds :=
    match stds with
    | std :: rest =>
      if missing0.startsWith (std ++ "/") then
        missing0.drop (std.length + 1)
      else findMissing rest
    | [] => missing0
  let missing := findMissing standard
  if missing.startsWith "@implicit/" then
    "?" ++ (missing.drop "@implicit/".length).toString
  else missing.toString

def readQualified (s : String) : Name :=
  readQualifiedName s -- Simplified since showTupled/readTupled was deprecated in Koka

def showHexChar (d : Nat) : Char :=
  if d <= 9 then Char.ofNat (d + '0'.toNat)
  else Char.ofNat (d - 10 + 'A'.toNat)

partial def hexDigits (i : Nat) : List Nat :=
  let rec go (x : Nat) (acc : List Nat) :=
    if x == 0 then acc else go (x / 16) ((x % 16) :: acc)
  if i == 0 then [0] else go i [] |>.reverse

def showHex (len : Nat) (i : Nat) : String :=
  let hexs := String.ofList (hexDigits i |>.map showHexChar)
  if len > hexs.length then String.ofList (List.replicate (len - hexs.length) '0') ++ hexs else hexs

def showBinary (len : Nat) (i : Nat) : String :=
  let rec go (x : Nat) (acc : List Char) : List Char :=
    if h : x = 0 then acc else
      have : x / 2 < x := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
      go (x / 2) (if x % 2 == 1 then '1' :: acc else '0' :: acc)
  termination_by x
  let bits := if i == 0 then ['0'] else go i []
  let s := String.ofList bits
  if len > s.length then String.ofList (List.replicate (len - s.length) '0') ++ s else s

def showHexFloat (d : Float) : String :=
  if d == 0.0 then "0x0p+0"
  else if d.isNaN then "NaN"
  else if d == 1.0 / 0.0 then "Infinity"
  else if d == -1.0 / 0.0 then "-Infinity"
  else
    let bits := d.toBits
    let sign := if (bits >>> 63) == 1 then "-" else ""
    let exp := (bits >>> 52) &&& 0x7FF
    let mantissa := bits &&& 0xFFFFFFFFFFFFF
    if exp == 0 then -- Subnormal
      s!"{sign}0x0.{showHex 13 mantissa.toNat}p-1022"
    else
      s!"{sign}0x1.{showHex 13 mantissa.toNat}p{Int.ofNat exp.toNat - 1023}"

def asciiEncode (isModule : Bool) (name : String) : String :=
  if name == "" then "_null_"
  else if name == "@<>" then "_total_"
  else if name == "@<|>" then "_extend_"
  else if name == "@()" then "_unit_"
  else if name == "@(,)" then "_tuple2_"
  else if name == "@(,,)" then "_tuple3_"
  else if name == "@(,,,)" then "_tuple4_"
  else if name == "()" then "_Unit_"
  else if name == "(,)" then "_Tuple2_"
  else if name == "(,,)" then "_Tuple3_"
  else if name == "(,,,)" then "_Tuple4_"
  else if name == "[]" then "_index_"
  else
    let chars := name.toList
    let preChars := ' ' :: chars
    let postChars := chars.drop 1 ++ [' ']
    let encodeChar (pre c post : Char) : String :=
      if c.isAlphanum then c.toString
      else if c == '/' && isModule then "_"
      else if c == '-' && !isModule && post.isAlphanum then "_"
      else if c == '@' && (post.isDigit || post == ' ' || pre == ' ' || pre == '/') then "_"
      else match c with
      | '_' => "__"
      | '.' => "_dot_"
      | '-' => "_dash_"
      | '/' => "_fs_"
      | '+' => "_plus_"
      | '*' => "_star_"
      | '&' => "_amp_"
      | '~' => "_tilde_"
      | '!' => "_excl_"
      | '@' => "_at_"
      | '#' => "_hash_"
      | '$' => "_dollar_"
      | '%' => "_perc_"
      | '^' => "_hat_"
      | '=' => "_eq_"
      | ':' => "_colon_"
      | '<' => "_lt_"
      | '>' => "_gt_"
      | '[' => "_lb_"
      | ']' => "_rb_"
      | '?' => "_ques_"
      | '\\' => "_bs_"
      | '(' => "_lp_"
      | ')' => "_rp_"
      | ',' => "_comma_"
      | ' ' => "_space_"
      | '\'' => "_sq_"
      | '"' => "_dq_"
      | '`' => "_bq_"
      | '{' => "_lc_"
      | '}' => "_rc_"
      | '|' => "_bar_"
      | _ => "_x" ++ showHex 2 c.toNat ++ "_"
    let encoded := preChars.zip chars |>.zip postChars |>.map (fun ((pre, c), post) => encodeChar pre c post)
    encoded.foldl (· ++ ·) ""

def moduleNameToPath (name : Name) : String :=
  asciiEncode true (showPlain name)

partial def decodePathToModule (s : String) : String :=
  if s == "" then ""
  else if s.startsWith "_dash_" then "-" ++ decodePathToModule (s.drop 6 |>.toString)
  else if s.startsWith "__" then "_" ++ decodePathToModule (s.drop 2 |>.toString)
  else if s.startsWith "_" then "/" ++ decodePathToModule (s.drop 1 |>.toString)
  else if s.startsWith "." then decodePathToModule (s.drop 1 |>.toString)
  else if s.startsWith "\\" then "/" ++ decodePathToModule (s.drop 1 |>.toString)
  else String.singleton s.front ++ decodePathToModule (s.drop 1 |>.toString)

def pathToModuleName (path : String) : Name :=
  let path1 := path.replace "\\" "/"
  let decoded := decodePathToModule path1
  let chars := decoded.toList
  let path2 := String.ofList (chars.dropWhile (fun c => c == '_' || c == '.' || c == '/'))
  let path3 := if path2.endsWith "/" then path2.dropEnd 1 |>.toString else path2
  newModuleName path3

open Koka.Lib.PPrint Koka.Common.ColorScheme

def isImplicitParamName (name : Name) : Bool :=
  match splitLocalQualName name with
  | m :: _ => m == implicitNameSpace
  | _ => false

def fromImplicitParamName (name : Name) : Name :=
  match splitLocalQualName name with
  | m :: ms =>
    if m == implicitNameSpace then qualifyLocally (unsplitModuleName ms) (unqualifyFull name)
    else name
  | _ => name

def splitImplicitParamName (name : Name) : Name × Name :=
  (name, unqualifyFull name)

def prettyNameEx (lsep : String) (cs : ColorScheme) (name : Name) : Doc :=
  let ln := joinStr name.localQual (wrapId name.stem)
  if name.module.isEmpty then textP ln
  else color cs.colorModule (textP name.module <.> (if ln.isEmpty then empty else (if name.localQual.isEmpty then textP "/" else textP lsep))) <.> textP ln

def prettyName (cs : ColorScheme) (name : Name) : Doc :=
  if isImplicitParamName name
  then textP "?" <.> prettyNameEx "/" cs (requalifyLocally (fromImplicitParamName name))
  else prettyNameEx "/" cs name

def prettyCoreName (cs : ColorScheme) (name : Name) : Doc :=
  prettyNameEx "/#" cs name

instance : Pretty Name where
  pretty name := textP (toString name)

end Koka.Common.Name
