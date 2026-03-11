/-
  Ported from Haskell Koka:
  File:   src/Syntax/Lexeme.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
import Koka.Common.Name
import Koka.Common.NamePrim
import Koka.Common.Range
import Koka.Common.Syntax

namespace Koka.Syntax.Lexeme

open Koka.Common
open Koka.Common.Name
open Koka.Common.NamePrim
open Koka.Common.Range
open Koka.Common.Syntax

def isTypeVar (n : Name) : Bool :=
  match nameLocal n |>.toList with
  | c :: cs => c.isLower && cs.all Char.isDigit
  | [] => false

-----------------------------------------------------------
-- Lexer tokens
-----------------------------------------------------------

-- | A lexical token.
inductive Lex
  | LexInt (i : Int) (s : String)
  | LexFloat (f : Float) (s : String)
  | LexChar (c : Char)
  | LexString (s : String)
  | LexId (n : Name)
  | LexCons (n : Name) (s : String)
  | LexOp (n : Name)
  | LexPrefix (n : Name)
  | LexIdOp (n : Name)
  | LexWildCard (n : Name)
  | LexKeyword (k d : String)
  | LexSpecial (s : String)
  | LexComment (s : String)
  | LexWhite (s : String)
  | LexModule (m1 m2 : Name)
  | LexTypedId (n : Name) (s : String)
  | LexInsLCurly
  | LexInsRCurly
  | LexInsSemi
  | LexError (s : String)
  deriving Repr, BEq, Inhabited

-- | A lexical token with an associated range.
structure Lexeme where
  range : Range
  lex : Lex
  deriving Repr, BEq, Inhabited

open Lex

-- | 'True' when the lexical token is whitespace
def lexIsWhite : Lex → Bool
  | LexWhite _ => true
  | LexComment _ => true
  | _ => false

-- | 'True' when the lexeme is whitespace
def lexemeIsWhite (l : Lexeme) : Bool :=
  lexIsWhite l.lex

def fromEnumLex : Lex → Nat
  | LexInt _ _      => 0
  | LexFloat _ _    => 1
  | LexChar _       => 2
  | LexString _     => 3
  | LexId _         => 4
  | LexOp _         => 5
  | LexWildCard _   => 6
  | LexModule _ _   => 7
  | LexKeyword _ _  => 8
  | LexSpecial _    => 9
  | LexComment _    => 10
  | LexWhite _      => 11
  | LexInsLCurly    => 13
  | LexInsRCurly    => 14
  | LexInsSemi      => 15
  | LexError _      => 16
  | LexCons _ _     => 17
  | LexTypedId _ _  => 18
  | LexPrefix _     => 19
  | LexIdOp _       => 20

-- | Returns 'True' if the lexical tokens are of the same kind (i.e. same constructor)
def sameLex (lex1 lex2 : Lex) : Bool :=
  match lex1, lex2 with
  | LexKeyword name1 _, LexKeyword name2 _ => name1 == name2
  | LexSpecial name1, LexSpecial name2 => name1 == name2
  | _, _ => fromEnumLex lex1 == fromEnumLex lex2

-- | Returns 'True' if the lexical tokens of the lexeme are of the same kind.
def sameLexeme (l1 l2 : Lexeme) : Bool :=
  sameLex l1.lex l2.lex

def showLex : Lex → String
  | LexInt _ s => s
  | LexFloat _ s => s
  | LexChar c => reprStr c
  | LexString s => reprStr s
  | LexId id => s!"identifier \"{id}\""
  | LexOp id => s!"operator \"{id}\""
  | LexPrefix id => s!"prefix operator \"{id}\""
  | LexIdOp id => s!"identifier (operator) \"{id}\""
  | LexWildCard id => s!"wildcard \"{id}\""
  | LexModule id _ => s!"module \"{id}\""
  | LexKeyword k d => s!"\"{k}\"" ++ (if d.isEmpty then "" else s!" ({d})")
  | LexSpecial s => s!"\"{s}\""
  | LexComment s => s!"comment \"{s}\""
  | LexWhite _w => "white"
  | LexInsLCurly => "start of statements ('{')"
  | LexInsRCurly => "end of statements ('}')"
  | LexInsSemi => "end of statement (';')"
  | LexError msg => msg
  | LexCons id _ => s!"constructor \"{id}\""
  | LexTypedId id tp => s!"typedid {id}:{tp}"

def showLexeme (l : Lexeme) : String :=
  showFullRange "" l.range ++ ": " ++ showLex l.lex

instance : ToString Lexeme := ⟨showLexeme⟩
instance : ToString Lex := ⟨showLex⟩

instance : Ranged Lexeme where
  getRange l := l.range

-----------------------------------------------------------
-- Lexical imports
-----------------------------------------------------------

structure LexImport where
  name : Name
  alias : Name
  vis : Visibility
  isOpen : Bool
  deriving Repr, Inhabited

def showLexImport (li : LexImport) : String :=
  (if li.vis == Visibility.Public then "pub " else "") ++
  (if li.isOpen then "@open " else "") ++
  (if nameIsNil li.alias then "" else s!"{li.alias} = ") ++
  toString li.name

instance : ToString LexImport := ⟨showLexImport⟩

instance : BEq LexImport where
  beq li1 li2 := li1.name == li2.name

partial def lexImportNub (imports : List LexImport) : List LexImport :=
  match imports with
  | [] => []
  | li :: lis =>
    match lis.find? (fun x => x.name == li.name) with
    | some li' =>
      let new_vis := if li.vis == Visibility.Public || li'.vis == Visibility.Public then Visibility.Public else Visibility.Private
      let new_alias := if nameIsNil li.alias then li'.alias else li.alias
      let new_isOpen := li.isOpen || li'.isOpen
      let updated := { li with vis := new_vis, alias := new_alias, isOpen := new_isOpen }
      let filtered := lis.filter (fun x => x.name != li.name)
      updated :: lexImportNub filtered
    | none =>
      li :: lexImportNub lis

end Koka.Syntax.Lexeme
