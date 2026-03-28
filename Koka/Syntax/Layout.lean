/-
  Ported from Haskell Koka:
  File:   src/Syntax/Layout.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
import Koka.Common.Range
import Koka.Lib.Trace
import Koka.Syntax.Lexeme
import Koka.Common.Name
import Koka.Common.File

namespace Koka.Syntax.Layout

open Koka.Common.Range
open Koka.Lib.Trace
open Koka.Syntax.Lexeme
open Koka.Common.Name
open Koka.Common.File

def isLexError : Lexeme → Bool
  | ⟨_, .LexError _⟩ => true
  | _ => false

def removeWhite (lexemes : List Lexeme) : List Lexeme :=
  lexemes.filter (fun l => not (lexemeIsWhite l))

def removeWhiteSpace (lexemes : List Lexeme) : List Lexeme :=
  let isWhiteSpace : Lexeme → Bool
    | ⟨_, .LexWhite _⟩ => true
    | _ => false
  lexemes.filter (not ∘ isWhiteSpace)

def endLine (r : Range) : Int := r.«end».line
def startLine (r : Range) : Int := r.start.line
def startCol (r : Range) : Int := r.start.col
def endCol (r : Range) : Int := r.«end».col

def before (rng : Range) : Range := makeRange rng.start rng.start
def after (rng : Range) : Range := makeRange rng.«end» rng.«end»

partial def associateComments (lexs : List Lexeme) : List Lexeme :=
  let trimRight (s : String) : String :=
    String.ofList (s.toList.reverse.dropWhile Char.isWhitespace |>.reverse)

  let docKeyword := [
    "fun","val","ctl","final","raw"
    ,"type","effect","struct","alias"
    ,"extern","module"
    ,"control","rcontrol","except","rawctl","brk"
    ,"cotype","rectype"
    ,"external","function"
  ]

  let isValidPrefix (lex : Lex) : Bool :=
    match lex with
    | .LexKeyword _ _ => true
    | .LexId _ => true
    | .LexInt _ _ => true
    | .LexSpecial s => s ∈ ["(",")","{","}",","]
    | _ => false
    
  let rec scanDocKeyword (doc : String) (line : Int) (acc : List Lexeme) (ls : List Lexeme) : Option (List Lexeme × List Lexeme) :=
    match ls with
    | [] => none
    | ⟨rng, lex⟩ :: rest =>
      if startLine rng != line then none
      else
        match lex with
        | .LexKeyword k _ =>
          if k ∈ docKeyword then
            some (acc.reverse ++ [⟨rng, .LexKeyword k doc⟩], rest)
          else none
        | .LexCons c _ =>
          some (acc.reverse ++ [⟨rng, .LexCons c doc⟩], rest)
        | _ =>
          if isValidPrefix lex then
            scanDocKeyword doc line (⟨rng, lex⟩ :: acc) rest
          else none

  let rec scan (ls : List Lexeme) : List Lexeme :=
    match ls with
    | ⟨r1, .LexComment comment⟩ :: rest =>
      let cs := (comment.drop 3).toString -- '//.'
      if comment.startsWith "//." && not ((trimRight cs).any Char.isWhitespace) then
        ⟨r1, .LexSpecial (trimRight cs)⟩ :: scan rest
      else
        let line := if comment.endsWith "\n" then endLine r1 else endLine r1 + 1
        match scanDocKeyword comment line [] rest with
        | some (pre, rest') => pre ++ scan rest'
        | none => ⟨r1, .LexComment comment⟩ :: scan rest
    | l :: rest => l :: scan rest
    | [] => []
    
  scan lexs

partial def combineLineComments (lexs : List Lexeme) : List Lexeme :=
  let rec scan (ls : List Lexeme) : List Lexeme :=
    match ls with
    | ⟨r1, .LexComment c1⟩ :: ⟨r2, .LexComment c2⟩ :: rest =>
      if c1.startsWith "//" && c2.startsWith "//" then
        scan (⟨combineRange r1 r2, .LexComment ("//" ++ c1.drop 2 ++ "//" ++ c2.drop 2)⟩ :: rest)
      else ⟨r1, .LexComment c1⟩ :: scan (⟨r2, .LexComment c2⟩ :: rest)
    | l :: rest => l :: scan rest
    | [] => []
  scan lexs

mutual
  partial def checkId (rng : Range) (id : Name) (lexs : List Lexeme) : List Lexeme :=
    if id.stem.any (· == '@') then
      ⟨rng, .LexError ("\"@\": identifiers cannot contain '@' characters (in '" ++ toString id ++ "')")⟩ :: check lexs
    else check lexs

  partial def check (ls : List Lexeme) : List Lexeme :=
    match ls with
    | [] => []
    | l1 :: l2 :: rest =>
      match l1, l2 with
      | ⟨_, .LexKeyword keyw _⟩, ⟨_, .LexId _⟩ =>
        if keyw ∈ ["fun","val","extern"] then
          l1 :: l2 :: check rest
        else
          process l1 (l2 :: rest)
      | _, _ => process l1 (l2 :: rest)
    | l :: rest => process l rest

  partial def process (lexeme : Lexeme) (lexs : List Lexeme) : List Lexeme :=
    match lexeme with
    | ⟨rng, lex⟩ =>
      lexeme :: match lex with
      | .LexId id => checkId rng id lexs
      | .LexCons id _ => checkId rng id lexs
      | .LexOp id => checkId rng id lexs
      | .LexPrefix id => checkId rng id lexs
      | .LexIdOp id => checkId rng id lexs
      | .LexWildCard id => checkId rng id lexs
      | _ => check lexs
end

partial def checkIds (lexemes : List Lexeme) : List Lexeme := check lexemes

partial def checkComments (lexemes : List Lexeme) : List Lexeme :=
  let rec check (prevLine : Int) (commentRng : Range) (ls : List Lexeme) : List Lexeme :=
    match ls with
    | [] => []
    | lexeme@⟨rng, lex⟩ :: rest =>
      lexeme ::
      match lex with
      | .LexComment s =>
        if not (s.startsWith "\n#") then check prevLine rng rest
        else
          let checkIndent :=
            if startLine rng > prevLine && startLine rng == endLine commentRng && endCol commentRng > 1 then
              [⟨commentRng, .LexError "layout: comments cannot be placed in the indentation of a line"⟩]
            else []
          checkIndent ++ check (endLine rng) commentRng rest
      | .LexWhite _ => check prevLine commentRng rest
      | _ =>
        let checkIndent :=
          if startLine rng > prevLine && startLine rng == endLine commentRng && endCol commentRng > 1 then
            [⟨commentRng, .LexError "layout: comments cannot be placed in the indentation of a line"⟩]
          else []
        checkIndent ++ check (endLine rng) commentRng rest
  check 0 rangeNull lexemes

structure Layout where
  openLexeme : Lexeme
  column : Int

def insertLCurly (prev : Lexeme) : List Lexeme :=
  match prev with
  | ⟨prevRng, _⟩ => [⟨after prevRng, .LexInsLCurly⟩]

def insertRCurly (layout : Layout) (prev : Lexeme) : List Lexeme :=
  match layout, prev with
  | Layout.mk ⟨layoutRng, layoutLex⟩ layoutCol, ⟨prevRng, _⟩ =>
    (if layoutLex == .LexInsLCurly then [] else [⟨after prevRng, .LexError ("layout: an open brace '{' (at " ++ toString layoutRng ++ ", layout column " ++ toString layoutCol ++ ") is matched by an implicit closing brace")⟩]) ++
    [⟨after prevRng, .LexInsRCurly⟩]

def isSemi (lex : Lex) : Bool :=
  match lex with
  | .LexSpecial ";" => true
  | .LexInsSemi => true
  | _ => false

def insertSemi (prev : Lexeme) : List Lexeme :=
  match prev with
  | ⟨prevRng, prevLex⟩ =>
    if isSemi prevLex then [] else [⟨after prevRng, .LexInsSemi⟩]

def isStartContinuationToken (lex : Lex) : Bool :=
  match lex with
  | .LexSpecial s => s ∈ [")",">","]",",","{","}"]
  | .LexKeyword k _ => k ∈ ["then","else","elif","->","=","|",":",".",":="]
  | .LexOp op => not (nameLocal op ∈ ["<"])
  | .LexInsLCurly => true
  | .LexInsRCurly => true
  | _ => false

def isEndContinuationToken (lex : Lex) : Bool :=
  match lex with
  | .LexSpecial s => s ∈ ["(","<","[",",","{"]
  | .LexKeyword k _ => k ∈ ["."]
  | .LexInsLCurly => true
  | .LexOp op => not (nameLocal op ∈ [">"])
  | _ => false

def isExprContinuation (prevLex lex : Lex) : Bool :=
  isStartContinuationToken lex || isEndContinuationToken prevLex

def isCloseBrace (lex : Lex) : Bool :=
  match lex with
  | .LexSpecial "}" => true
  | .LexInsRCurly => true
  | _ => false

def isOpenBrace (lex : Lex) : Bool :=
  match lex with
  | .LexSpecial "{" => true
  | .LexInsLCurly => true
  | _ => false

def unLexeme (l : Lexeme) : Lex := l.lex

partial def brace (layout : Layout) (layouts : List Layout) (prev : Lexeme) (lexemes : List Lexeme) : List Lexeme :=
  match lexemes with
  | [] =>
    match layouts with
    | [] => []
    | ly :: lys =>
      let rcurly := insertRCurly layout prev
      insertSemi prev ++ rcurly ++ brace ly lys (rcurly.getLast!) []
  | lexeme@⟨rng, lex⟩ :: ls =>
    if let .LexError _ := lex then
      lexeme :: brace layout layouts prev ls
    else
      let newline := endLine prev.range < startLine rng
      let indent := startCol rng
      let nextIndent := match ls with
        | ⟨r, _⟩ :: _ => startCol r
        | _ => 1
      let layoutCol := layout.column

      if newline && indent > layoutCol && not (isExprContinuation (unLexeme prev) lex) then
        brace layout layouts prev (insertLCurly prev ++ lexemes)
      else if newline && indent < layoutCol && not (isCloseBrace lex && unLexeme layout.openLexeme == .LexSpecial "{") then
        brace layout layouts prev (insertRCurly layout prev ++ lexemes)
      else if isOpenBrace lex then
        let err := if nextIndent > layoutCol then [] else [⟨rng, .LexError ("layout: line must be indented more than the enclosing layout context (column " ++ toString layoutCol ++ ")")⟩]
        [lexeme] ++ err ++ brace (Layout.mk lexeme nextIndent) (layout :: layouts) lexeme ls
      else if isCloseBrace lex then
        insertSemi prev ++ [lexeme] ++
        match layouts with
        | ly :: lys => brace ly lys lexeme ls
        | [] => ⟨before rng, .LexError "unmatched closing brace '}'"⟩ :: brace layout [] lexeme ls
      else if newline && indent == layoutCol && not (isExprContinuation (unLexeme prev) lex) then
        insertSemi prev ++ [lexeme] ++ brace layout layouts lexeme ls
      else
        [lexeme] ++ brace layout layouts lexeme ls

def indentLayout (lexemes : List Lexeme) : List Lexeme :=
  match lexemes with
  | [] => [⟨rangeNull, .LexInsSemi⟩]
  | l :: ls =>
    let start := ⟨before (l.range), .LexWhite ""⟩
    brace (Layout.mk start 1) [] start (l :: ls)

def layout (allowAt : Bool) (semiInsertFlag : Bool) (lexemes : List Lexeme) : List Lexeme :=
  let semi (f : List Lexeme → List Lexeme) := if semiInsertFlag then f else id
  let ls := semi indentLayout <|
            (if allowAt then id else checkIds) <|
            removeWhite <|
            associateComments <|
            removeWhiteSpace <|
            combineLineComments <|
            semi checkComments <|
            lexemes
  ls

def replaceModules (replaceName : Name → Bool) (lexemes : List Lexeme) : List Lexeme :=
  lexemes.map fun lexeme =>
    match lexeme with
    | ⟨rng, .LexId id⟩ =>
      if replaceName id then ⟨rng, .LexModule id id⟩
      else lexeme
    | _ => lexeme

mutual
  partial def scanImports (count : Nat) (modules : List Name) (lexemes : List Lex) : List Name × Nat :=
    match lexemes with
    | [] => (modules, count)
    | .LexKeyword "import" _ :: lexs => scanImport (count + 1) modules lexs
    | lex :: lexs =>
      let inImportSection : Bool :=
        match lex with
        | .LexKeyword kw _ => kw ∈ ["module","import","as","public","private","."]
        | .LexSpecial s => s ∈ [";","(",")","{","}"]
        | .LexInsRCurly => true
        | .LexInsLCurly => true
        | .LexId _ => true
        | _ => false
      if inImportSection then scanImports (count + 1) modules lexs
      else (modules, count)

  partial def scanImport (count : Nat) (modules : List Name) (lexemes : List Lex) : List Name × Nat :=
    match lexemes with
    | .LexId _ :: .LexKeyword "." _ :: lexs => scanImport (count + 2) modules lexs
    | .LexId _ :: .LexKeyword "as" _ :: .LexId id :: lexs => scanImports (count + 3) (id :: modules) lexs
    | .LexId id :: lexs => scanImports (count + 1) (id :: modules) lexs
    | _ :: _ => scanImports count modules lexemes -- just ignore
    | [] => scanImports count modules []
end

def identifyModules (lexemes : List Lexeme) : List Lexeme :=
  let (names, headerCount) := scanImports 0 [] (lexemes.map unLexeme)
  replaceModules (fun _ => true) (lexemes.take headerCount) ++
  replaceModules (fun n => names.contains n) (lexemes.drop headerCount)

def lineLayout (lexemes : List Lexeme) : List Lexeme :=
  layout false false lexemes

def semiInsert (lexemes : List Lexeme) : List Lexeme :=
  layout false true lexemes


end Koka.Syntax.Layout
