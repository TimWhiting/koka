/-
  Ported from Haskell Koka:
  File:   src/Common/Range.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
import Koka.Lib.PPrint
import Koka.Common.File
import Koka.Common.Failure

namespace Koka.Common.Range

open Koka.Lib.PPrint
open Koka.Common.File
open Koka.Common.Failure

--------------------------------------------------------------------------
-- BStrings
--------------------------------------------------------------------------
abbrev BString := String

def bstringIsEmpty (b : BString) := b.isEmpty
def bstringEmpty : BString := ""
def bstringToText (b : BString) : String := b
def bstringToString (b : BString) : String := b
def stringToBString (s : String) : BString := s

def readInput (fname : String) : IO BString := do
  let input ← IO.FS.readFile fname
  if input.startsWith "\xEF\xBB\xBF" then
    return (input.drop 3).toString
  else
    return input

-- Mocks for extractLiterate (can be implemented later)
partial def extractLiterate (input : BString) : BString := input

--------------------------------------------------------------------------
-- Source
--------------------------------------------------------------------------
structure Source where
  name : String
  bstring : BString
  deriving Repr

instance : BEq Source where
  beq s1 s2 := s1.name == s2.name

def sourceNull := Source.mk "" ""

def sourceText (src : Source) : String := src.bstring

--------------------------------------------------------------------------
-- Positions
--------------------------------------------------------------------------
structure Pos where
  source : Source
  ofs : Int
  line : Int
  col : Int
  deriving Repr

def posNull := Pos.mk sourceNull (-1) 0 0

instance : BEq Pos where
  beq p1 p2 := p1.line == p2.line && p1.col == p2.col

instance : Ord Pos where
  compare p1 p2 :=
    match compare p1.line p2.line with
    | Ordering.eq => compare p1.col p2.col
    | lg => lg

instance : LE Pos where
  le a b := compare a b != Ordering.gt

instance : LT Pos where
  lt a b := compare a b == Ordering.lt

instance : Hashable Pos where
  hash p := mixHash (hash p.line) (hash p.col)

instance : ToString Pos where
  toString p := s!"({if p.line >= 67108864 then s!"({p.line - 67108864})" else if p.line <= 0 then "1" else toString p.line},{p.col})"

def bigLine : Int := 67108864 -- 2^26

def makePos (src : Source) (o l c : Int) : Pos := Pos.mk src o l c

def tabSize : Int := 2

def posMove8 (p : Pos) (ch : Char) : Pos :=
  let o1 := if p.ofs < 0 then p.ofs else p.ofs + 1
  match ch with
  | '\t' => Pos.mk p.source o1 p.line (((p.col + tabSize - 1) / tabSize) * tabSize + 1)
  | '\n' => Pos.mk p.source o1 (p.line + 1) 1
  | _ => Pos.mk p.source o1 p.line (p.col + 1)

def posMoves8 (p : Pos) (bstr : String) : Pos :=
  bstr.foldl posMove8 p

--------------------------------------------------------------------------
-- Ranges
--------------------------------------------------------------------------
structure Range where
  start : Pos
  «end» : Pos
  isHidden : Bool
  deriving Repr, BEq

instance : Inhabited Range where
  default := Range.mk posNull posNull false

instance : Ord Range where
  compare r1 r2 :=
    match compare r1.start r2.start with
    | Ordering.eq => compare r1.«end» r2.«end»
    | lg => lg

instance : ToString Range where
  toString r := toString r.start

def showPos (alignWidth : Nat) (p : Pos) : String :=
  let lstr := if p.line >= bigLine then s!"({p.line - bigLine})" else if p.line <= 0 then "1" else toString p.line
  let cstr := toString p.col
  let align (n : Nat) (s : String) := String.ofList (List.replicate (n - s.length) ' ') ++ s
  lstr ++ "," ++ align alignWidth cstr

def showCompactRange (r : Range) : String :=
  s!"[{showPos 0 r.start},{showPos 0 r.«end»}]"

-- Mock pretty
-- instance : Pretty Range where
--   pretty r := text (showCompactRange r)

def relativeToPath (cwd : String) (p : String) : String :=
  if p.startsWith cwd then
    let rest := p.drop cwd.length |>.toString
    if rest.startsWith "/" then rest.drop 1 |>.toString else rest
  else p

def showRange (cwd : String) (endToo : Bool) (r : Range) : String :=
  let base :=
    if r.start.line >= bigLine then ""
    else relativeToPath cwd r.start.source.name
  if endToo then
    base ++ s!"({showPos 0 r.start}-{showPos 0 r.«end»})"
  else
    base ++ toString r.start

def after (r1 r2 : Range) : Bool :=
  compare r1.«end» r2.start != Ordering.gt

def rangeNull := Range.mk posNull posNull false

def rangeIsNull (r : Range) : Bool :=
  r.start.ofs < 0 || r.«end».ofs < 0

def showFullRange (cwd : String) (r : Range) : String :=
  showRange cwd true r

def minPos (p1 p2 : Pos) : Pos :=
  if p1.line <= 0 then p2
  else if p2.line <= 0 then p1
  else if compare p1 p2 != Ordering.gt then p1 else p2

def maxPos (p1 p2 : Pos) : Pos :=
  if compare p1 p2 != Ordering.gt then p2 else p1

def makeRange (p1 p2 : Pos) : Range :=
  if p1.source != p2.source then
    panic! "Range.makeRange: positions from different sources"
  else
    Range.mk (minPos p1 p2) (maxPos p1 p2) false

def makeSourceRange (srcPath : String) (l1 c1 l2 c2 : Int) : Range :=
  let src := Source.mk srcPath ""
  makeRange (makePos src (-1) l1 c1) (makePos src (-1) l2 c2)

def rangeLength (r : Range) : Int := r.«end».ofs - r.start.ofs

def rangeSource (r : Range) : Source := r.start.source

def combineRange (r1 r2 : Range) : Range :=
  Range.mk (minPos r1.start r2.start) (maxPos r1.«end» r2.«end») (r1.isHidden || r2.isHidden)

def combineRanges (rs : List Range) : Range :=
  rs.foldr combineRange rangeNull

def rangeHide (r : Range) : Range :=
  Range.mk r.start r.«end» true

def extendRange (r : Range) (ofs : Int) : Range :=
  let e := r.«end»
  Range.mk r.start (Pos.mk e.source e.ofs e.line (e.col + ofs)) r.isHidden

def endOfRange (r : Range) : Range :=
  let ofs1 := r.start.ofs
  let ofs2 := r.«end».ofs
  if (ofs2 - ofs1) <= 1 then r else Range.mk r.«end» r.«end» r.isHidden

def startOfRange (r : Range) : Range :=
  Range.mk r.start r.start r.isHidden

def rangeContains (r : Range) (p : Pos) : Bool :=
  compare r.start p != Ordering.gt && compare r.«end» p != Ordering.lt

def rangeIsBefore (r : Range) (p : Pos) : Bool :=
  compare r.«end» p == Ordering.lt

def rangeStartsAt (r : Range) (p : Pos) : Bool :=
  r.start == p

def rangeJustBefore (r : Range) : Range :=
  if r.start.ofs < 0 then r
  else
    let p := Pos.mk r.start.source (r.start.ofs - 1) r.start.line (r.start.col - 1)
    Range.mk p p r.isHidden

def rangeJustAfter (r : Range) : Range :=
  let p := Pos.mk r.«end».source (r.«end».ofs + 1) r.«end».line (r.«end».col + 1)
  Range.mk p p r.isHidden

--------------------------------------------------------------------------
-- Ranged class
--------------------------------------------------------------------------
class Ranged (α : Type) where
  getRange : α → Range

instance : Ranged Range where
  getRange r := r

instance {α : Type} [Ranged α] : Ranged (Option α) where
  getRange
  | none => rangeNull
  | some r => Ranged.getRange r

def combineRanged {α β : Type} [Ranged α] [Ranged β] (x : α) (y : β) : Range :=
  combineRange (Ranged.getRange x) (Ranged.getRange y)

def combineRangeds {α : Type} [Ranged α] (xs : List α) : Range :=
  combineRanges (xs.map Ranged.getRange)

--------------------------------------------------------------------------
-- Extracts
--------------------------------------------------------------------------
def sourceFromRange (r : Range) : String :=
  if r.start.ofs >= 0 then
    -- Note: This just extracts substring using offset. In actual compiler, we might need UTF-8 specific indices.
    let text := (r.start.source.bstring.drop r.start.ofs.toNat).take (r.«end».ofs.toNat - r.start.ofs.toNat) |>.toString
    String.ofList (List.replicate (r.start.col.toNat - 1) ' ') ++ text
  else
    -- Fallback for lines without offsets
    let lines := r.start.source.bstring.splitOn "\n"
    let l1 := if r.start.line >= bigLine then 1 else r.start.line.toNat
    let l2 := if r.«end».line >= bigLine then (if r.start.line >= bigLine then r.«end».line.toNat - r.start.line.toNat + 1 else 1) else r.«end».line.toNat
    let subset := lines.drop (l1 - 1) |>.take (l2 - l1 + 1)
    -- This ignores exact column slicing logic for simplicity of fallback
    String.intercalate "\n" subset

def rawSourceFromRange (r : Range) : String :=
  let text := (r.start.source.bstring.drop r.start.ofs.toNat).take (r.«end».ofs.toNat - r.start.ofs.toNat) |>.toString
  text

end Koka.Common.Range
