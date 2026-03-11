/-
  Ported from Haskell Koka:
  File:   src/Lib/PPrint.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
import Koka.Lib.Printer
import Koka.Common.ColorScheme

namespace Koka.Lib.PPrint

open Koka.Lib.Printer Koka.Common.ColorScheme

mutual
inductive Doc where
  | Empty
  | Char (c : Char)
  | Text (s : String)
  | Line (break_ : Bool)
  | Cat (x y : Doc)
  | Nest (i : Int) (x : Doc)
  | Union (x y : Doc)
  | Column (f : Int → Doc)
  | Nesting (f : Int → Doc)
  | Colored (f : Bool) (c : Color) (d : Doc)
  | ColoredEnd
  deriving Inhabited
end

inductive SimpleDoc where
  | SEmpty
  | SChar (i : Int) (c : Char) (d : SimpleDoc)
  | SText (i : Int) (s : String) (d : SimpleDoc)
  | SLine (i : Int) (d : SimpleDoc)
  | SColorOpen (f : Bool) (c : Color) (d : SimpleDoc)
  | SColorClose (d : SimpleDoc)
  deriving Inhabited

def isEmptyDoc : Doc → Bool
  | .Empty => true
  | _ => false

def beside (x y : Doc) : Doc :=
  match x, y with
  | .Empty, y => y
  | x, .Empty => x
  | x, y => .Cat x y

infixr:6 " <.> " => beside

def empty : Doc := .Empty
def charP : Char → Doc
  | '\n' => .Line false
  | c => .Char c

-- Can't use `char` because it's a keyword in Lean (the type `Char`). So we use `charP` internally and export as `char` or just use `charP`. Let's use `charP`.

def textP (s : String) : Doc :=
  if s.isEmpty then .Empty else .Text s

def text' (s : String) : Doc :=
  if s.isEmpty then .Empty else .Text s

def line : Doc := .Line false
def linebreak : Doc := .Line true

def nest (i : Int) (x : Doc) : Doc := .Nest i x
def column (f : Int → Doc) : Doc := .Column f
def nesting (f : Int → Doc) : Doc := .Nesting f

mutual
partial def flatten : Doc → Doc
  | .Cat x y => .Cat (flatten x) (flatten y)
  | .Nest i x => .Nest i (flatten x)
  | .Line break_ => if break_ then .Empty else .Text " "
  | .Union x _ => flatten x
  | .Column f => .Column (fun k => flatten (f k))
  | .Nesting f => .Nesting (fun k => flatten (f k))
  | .Colored f c d => .Colored f c (flatten d)
  | other => other
end

def group (x : Doc) : Doc := .Union (flatten x) x

def color (c : Color) (doc : Doc) : Doc := .Colored true c doc
def bcolor (c : Color) (doc : Doc) : Doc := .Colored false c doc

def space : Doc := charP ' '
def softline : Doc := group line
def softbreak : Doc := group linebreak

def lparen : Doc := charP '('
def rparen : Doc := charP ')'
def langle : Doc := charP '<'
def rangle : Doc := charP '>'
def lbrace : Doc := charP '{'
def rbrace : Doc := charP '}'
def lbracket : Doc := charP '['
def rbracket : Doc := charP ']'

def squote : Doc := charP '\''
def dquote : Doc := charP '"'
def semi : Doc := charP ';'
def colon : Doc := charP ':'
def comma : Doc := charP ','
def dot : Doc := charP '.'
def backslash : Doc := charP '\\'
def equals : Doc := charP '='

def squotes (d : Doc) : Doc := squote <.> d <.> squote
def dquotes (d : Doc) : Doc := dquote <.> d <.> dquote
def braces (d : Doc) : Doc := lbrace <.> d <.> rbrace
def parens (d : Doc) : Doc := lparen <.> d <.> rparen
def angles (d : Doc) : Doc := langle <.> d <.> rangle
def brackets (d : Doc) : Doc := lbracket <.> d <.> rbracket
def enclose (l r x : Doc) : Doc := l <.> x <.> r

infixr:6 " <+> " => fun x y => x <.> space <.> y
infixr:5 " </> " => fun x y => match x, y with
  | .Empty, y => y
  | x, .Empty => x
  | x, y => x <.> softline <.> y
infixr:5 " <//> " => fun x y => x <.> softbreak <.> y
infixr:5 " <-> " => fun x y => match x, y with
  | .Empty, y => y
  | x, .Empty => x
  | x, y => x <.> line <.> y
infixr:5 " <--> " => fun x y => x <.> linebreak <.> y

def foldDoc : (Doc → Doc → Doc) → List Doc → Doc
  | _, [] => empty
  | _, [x] => x
  | f, x :: xs => f x (foldDoc f xs)

def hcat : List Doc → Doc := foldDoc beside
def hsep : List Doc → Doc := foldDoc (· <+> ·)
def vcat : List Doc → Doc := fun ds => foldDoc (· <--> ·) (ds.filter (not ∘ isEmptyDoc))
def vsep : List Doc → Doc := fun ds => foldDoc (· <-> ·) (ds.filter (not ∘ isEmptyDoc))
def cat : List Doc → Doc := group ∘ vcat
def sep : List Doc → Doc := group ∘ vsep
def fillCat : List Doc → Doc := foldDoc (· <//> ·)
def fillSep : List Doc → Doc := foldDoc (· </> ·)

def encloseSep (left right sepD : Doc) (ds : List Doc) : Doc :=
  match ds with
  | [] => left <.> right
  | [d] => left <.> d <.> right
  | _ => nest 2 (hcat (List.zipWith beside (left :: List.replicate (ds.length - 1) sepD) ds) <.> right)

def listD : List Doc → Doc := encloseSep lbracket rbracket (textP ", ")
def tupled : List Doc → Doc := encloseSep lparen rparen (textP ", ")
def semiBraces : List Doc → Doc := encloseSep lbrace rbrace semi
def angled : List Doc → Doc := encloseSep langle rangle comma

def punctuate (p : Doc) : List Doc → List Doc
  | [] => []
  | [d] => [d]
  | d :: ds => (d <.> p) :: punctuate p ds

-- string printing
partial def stringP (s : String) : Doc :=
  if s.isEmpty then empty
  else if s.startsWith "\n" then line <.> stringP (s.drop 1).toString
  else
    let (xs, ys) := s.toList.span (· ≠ '\n')
    textP (String.ofList xs) <.> stringP (String.ofList ys)

def boolP (b : Bool) : Doc := textP (toString b)
def intP (i : Int) : Doc := textP (toString i)
def natP (i : Nat) : Doc := textP (toString i)
def floatP (f : Float) : Doc := textP (toString f)

class Pretty (α : Type) where
  pretty : α → Doc
  prettyList : List α → Doc := fun xs => listD (xs.map pretty)

instance [Pretty α] : Pretty (List α) where
  pretty := Pretty.prettyList

instance : Pretty Doc where
  pretty := id

instance : Pretty Unit where
  pretty _ := textP "()"

instance : Pretty Bool where
  pretty b := boolP b

instance : Pretty Char where
  pretty c := charP c
  prettyList s := stringP (String.ofList s)

instance : Pretty Int where
  pretty i := intP i

instance : Pretty Nat where
  pretty i := natP i

instance : Pretty Float where
  pretty f := floatP f

instance [Pretty α] [Pretty β] : Pretty (α × β) where
  pretty p := tupled [Pretty.pretty p.fst, Pretty.pretty p.snd]

instance [Pretty α] : Pretty (Option α) where
  pretty | none => empty | some x => Pretty.pretty x

def spaces (n : Int) : String :=
  if n <= 0 then "" else String.ofList (List.replicate n.toNat ' ')

def width (d : Doc) (f : Int → Doc) : Doc :=
  column (fun k1 => d <.> column (fun k2 => f (k2 - k1)))

def fill (f : Int) (d : Doc) : Doc :=
  width d (fun w => if w >= f then empty else text' (spaces (f - w)))

def fillBreak (f : Int) (x : Doc) : Doc :=
  width x (fun w => if w > f then nest f linebreak else text' (spaces (f - w)))

def align (d : Doc) : Doc :=
  column (fun k => nesting (fun i => nest (k - i) d))

def hang (i : Int) (d : Doc) : Doc :=
  align (nest i d)

def indent (i : Int) (d : Doc) : Doc :=
  hang i (text' (spaces i) <.> d)

mutual
partial def best (r w : Int) (b n k : Int) (ds : List (Int × Doc)) : SimpleDoc :=
  match ds with
  | [] => .SEmpty
  | (i, d) :: ds =>
    match d with
    | .Empty => best r w b n k ds
    | .Char c =>
      let k' := k + 1
      .SChar b c (best r w b n k' ds)
    | .Text s =>
      let k' := k + s.length
      .SText b s (best r w b n k' ds)
    | .Line _ =>
      .SLine i (best r w b i i ds)
    | .Cat x y =>
      best r w b n k ((i, x) :: (i, y) :: ds)
    | .Nest j x =>
      let i' := i + j
      best r w (if b == 0 then i' else b) n k ((i', x) :: ds)
    | .Union x y =>
      nicest r w n k (best r w b n k ((i, x) :: ds)) (best r w b n k ((i, y) :: ds))
    | .Column f =>
      best r w b n k ((i, f k) :: ds)
    | .Nesting f =>
      best r w b n k ((i, f i) :: ds)
    | .Colored f c x =>
      .SColorOpen f c (best r w b n k ((i, x) :: (i, .ColoredEnd) :: ds))
    | .ColoredEnd =>
      .SColorClose (best r w b n k ds)

partial def nicest (r w n k : Int) (x y : SimpleDoc) : SimpleDoc :=
  let width := min (w - k) (r - k + n)
  if fits width x then x else y

partial def fits (w : Int) (d : SimpleDoc) : Bool :=
  if w < 0 then false
  else match d with
  | .SEmpty => true
  | .SChar _ _ x => fits (w - 1) x
  | .SText _ s x => fits (w - s.length) x
  | .SLine _ _ => true
  | .SColorOpen _ _ x => fits w x
  | .SColorClose x => fits w x
end

partial def renderCompact (x : Doc) : SimpleDoc :=
  let rec scan (k : Int) (ds : List Doc) : SimpleDoc :=
    match ds with
    | [] => .SEmpty
    | d :: ds =>
      match d with
      | .Empty => scan k ds
      | .Char c =>
        let k' := k + 1
        .SChar 0 c (scan k' ds)
      | .Text s =>
        let k' := k + s.length
        .SText 0 s (scan k' ds)
      | .Line _ =>
        .SLine 0 (scan 0 ds)
      | .Cat x y =>
        scan k (x :: y :: ds)
      | .Nest _ x =>
        scan k (x :: ds)
      | .Union _ y =>
        scan k (y :: ds)
      | .Column f =>
        scan k (f k :: ds)
      | .Nesting f =>
        scan k (f 0 :: ds)
      | .Colored f c x =>
        .SColorOpen f c (scan k (x :: .ColoredEnd :: ds))
      | .ColoredEnd =>
        .SColorClose (scan k ds)
  scan 0 [x]

partial def makeMarkdown : Doc → Doc
  | .Line true => .Text "\n\n"
  | .Column f => .Column (fun k => makeMarkdown (f k))
  | .Nesting f => .Nesting (fun k => makeMarkdown (f k))
  | .Cat l r => .Cat (makeMarkdown l) (makeMarkdown r)
  | .Nest i d => .Nest i (makeMarkdown d)
  | .Union l r => .Union (makeMarkdown l) (makeMarkdown r)
  | .Colored f c d => .Colored f c (makeMarkdown d)
  | other => other

partial def texts : Doc → List String
  | .Empty => []
  | .Char c => [c.toString]
  | .Text s => [s]
  | .Line break_ => if break_ then [] else ["\n"]
  | .Union x _ => texts x
  | .Cat x y => texts x ++ texts y
  | .Nest _ x => texts x
  | .Column f => texts (f 0)
  | .Nesting f => texts (f 0)
  | .Colored _ _ d => texts d
  | _ => []

partial def rtexts : Doc → List String
  | .Empty => []
  | .Char c => [c.toString]
  | .Text s => [String.ofList s.toList.reverse]
  | .Line break_ => if break_ then [] else ["\n"]
  | .Union x _ => rtexts x
  | .Cat x y => rtexts y ++ rtexts x
  | .Nest _ x => rtexts x
  | .Column f => rtexts (f 0)
  | .Nesting f => rtexts (f 0)
  | .Colored _ _ d => rtexts d
  | _ => []

def dcontains (doc : Doc) (p : Char → Bool) : Bool :=
  (texts doc).any (fun s => s.any p)

def dstartsWith (doc : Doc) (pre : String) : Bool :=
  let rec check (ts : List String) (p : String) (n : Nat) : Bool :=
    if n == 0 then true
    else match ts with
      | [] => false
      | s :: xs =>
        let m := s.length
        if m >= n then s.startsWith (p.take n)
        else p.startsWith s && check xs (p.drop m).toString (n - m)
  check (texts doc) pre pre.length

def dendswith (doc : Doc) (post : String) : Bool :=
  let rec check (rts : List String) (rp : String) (n : Nat) : Bool :=
    if n == 0 then true
    else match rts with
      | [] => false
      | s :: xs =>
        let m := s.length
        if m >= n then s.startsWith (rp.take n)
        else rp.startsWith s && check xs (rp.drop m).toString (n - m)
  check (rtexts doc) (String.ofList post.toList.reverse) post.length

def defaultWidth : Int := 512

def displayS (sdoc : SimpleDoc) : String :=
  let rec go (x : SimpleDoc) : List String :=
    match x with
    | .SEmpty => []
    | .SChar _ c x => c.toString :: go x
    | .SText _ s x => s :: go x
    | .SLine i x => ("\n" ++ spaces i) :: go x
    | .SColorOpen _ _ x => go x
    | .SColorClose x => go x
  String.join (go sdoc)

def asString (doc : Doc) : String :=
  displayS (renderCompact doc)

partial def displayP {p : Type} [Printer p] (printer : p) (w : Int) (sdoc : SimpleDoc) : IO Unit :=
  let rec skipSpaces (s : SimpleDoc) : SimpleDoc :=
    match s with
    | .SChar i c x => if c.isWhitespace then skipSpaces x else .SChar i c x
    | .SText i str x =>
      let str' := String.ofList (str.toList.dropWhile Char.isWhitespace)
      if str'.isEmpty then skipSpaces x else .SText i str' x
    | _ => s
  let rec display (k : Int) (s : SimpleDoc) : IO (Int × SimpleDoc) :=
    match s with
    | .SEmpty => pure (k, .SEmpty)
    | .SChar i c x => do
      if k + 1 >= w && i + 1 < w then
        display k (.SLine (i + 1) (skipSpaces (.SChar i c x)))
      else
        Printer.write printer c.toString
        display (k + 1) x
    | .SText i str x => do
      if k + str.length >= w && i + str.length < w then
        display k (.SLine (i + 1) (skipSpaces (.SText i str x)))
      else
        Printer.write printer str
        display (k + str.length) x
    | .SLine i x => do
      Printer.writeLn printer ""
      Printer.write printer (spaces i)
      display i x
    | .SColorOpen f c x => do
      let withFn := if f then Printer.withColor else Printer.withBackColor
      let (kc, cont) ← withFn printer c (display k x)
      display kc cont
    | .SColorClose x => pure (k, x)
  do
    let _ ← display 0 sdoc
    pure ()

def writePretty {p : Type} [Printer p] (printer : p) (doc : Doc) : IO Unit :=
  let w := defaultWidth
  let r := (w * 8) / 10
  let rw := max 0 (min w r)
  displayP printer w (best rw w 0 0 0 [(0, doc)])

def writePrettyLn {p : Type} [Printer p] (printer : p) (doc : Doc) : IO Unit :=
  writePretty printer (doc <.> linebreak)

def writePrettyW {p : Type} [Printer p] (printer : p) (w : Int) (doc : Doc) : IO Unit :=
  let r := (w * 8) / 10
  let rw := max 0 (min w r)
  displayP printer w (best rw w 0 0 0 [(0, doc)])

def writeAtomicPrettyLn {p : Type} [Printer p] (printer : p) (doc : Doc) : IO Unit := do
  let r := (defaultWidth * 8) / 10
  let rw := max 0 (min defaultWidth r)
  Printer.writeLn printer (displayS (best rw defaultWidth 0 0 0 [(0, doc)]))

def writeDocW (width : Int) (fpath : String) (doc : Doc) : IO Unit := do
  let r := (width * 5) / 10
  let rw := max 0 (min width r)
  let sdoc := best rw width 0 0 0 [(0, doc)]
  let s := displayS sdoc
  try
    let handle ← IO.FS.Handle.mk fpath IO.FS.Mode.write
    handle.putStr s
    handle.flush
  catch _ => pure ()

def writeDoc (fpath : String) (doc : Doc) : IO Unit :=
  writeDocW defaultWidth fpath doc

end Koka.Lib.PPrint
