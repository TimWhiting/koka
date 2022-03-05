import std/text/parse
import std/text/regex
import std/text/unicode
import common/name
import common/range

pub fun isTypeVar(n: name): bool
  !"[a-z][0-9]*".regex().exec(n.nameId).is-empty

pub struct lexeme ( pub range: range, pub lex: lex )

pub type lex
  LexInt(i: int, s: string)
  LexFloat(f: float64, s: string)
  LexChar(c: char)
  LexString(s: string)
  LexId(n: name)
  LexCons(n: name)
  LexOp(n: name)
  LexPrefix(n: name)
  LexIdOp(n: name)
  LexWildCard(n: name)
  LexKeyword(s: string, k: string)
  LexSpecial(s: string)
  LexComment(s: string)
  LexWhite(s: string)
  // Special for highlighting
  LexModule(alias_: name, full: name)
  LexTypeId(n: name, s: string)
  LexInsLCurly
  LexInsRCurly
  LexInsSemi
  LexError(s: string)

pub fun lexemeIsWhite(l: lexeme): <> bool
  l.lex.lexIsWhite

pub fun lexIsWhite(l: lex): <> bool
  match l
    LexWhite(_) -> True
    _ -> False

pub fun sameLexeme(l1: lexeme, l2: lexeme): <> bool
  match (l1.lex, l2.lex)
    (LexKeyword(n1, _), LexKeyword(n2, _)) -> n1 == n2 
    (LexSpecial(n1), LexSpecial(n2)) -> n1 == n2
    (_, _) -> l1.lex.fromEnum == l2.lex.fromEnum

pub fun fromEnum(l: lex): <> int
  match l
    LexInt(_, __) -> 0
    LexFloat(_, __) -> 1
    LexChar(_) -> 2
    LexString(_) -> 3
    LexId(_) -> 4
    LexOp(_) -> 5
    LexPrefix(_) -> 19
    LexIdOp(_) -> 20
    LexWildCard(_) -> 6
    LexModule(_, _) -> 7
    LexKeyword(_, _) -> 8
    LexSpecial(_) -> 9
    LexComment(_) -> 10
    LexWhite(_) -> 11
    LexInsLCurly -> 13
    LexInsRCurly -> 14
    LexInsSemi -> 15
    LexError(_) -> 16
    LexCons(_) -> 17
    LexTypeId(_, _) -> 18

pub fun show(l: lexeme): <> string
  l.range.showFullRange ++ ": " ++ l.lex.show

pub fun show(l: lex): <> string
  match l
    LexInt(_, s) -> s
    LexFloat(_, s) -> s
    LexChar(c) -> c.show
    LexString(s) -> s
    LexId(n) -> "identifier \"" ++ n.show ++ "\""
    LexOp(n) -> "operator \"" ++ n.show ++ "\""
    LexPrefix(n) -> "prefix operator \"" ++ n.show ++ "\""
    LexIdOp(n) -> "identifier (operator) \"" ++ n.show ++ "\""
    LexWildCard(n) -> "wildcard \"" ++ n.show ++ "\""
    LexModule(n, _) -> "module \"" ++ n.show ++ "\""
    LexKeyword(k, d) -> "\"" ++ k ++ "\"" ++ (if d.is-empty then "" else " (" ++ d ++ ")")
    LexSpecial(s) -> "\"" ++ s ++ "\""
    LexComment(s) -> "comment \"" ++ s ++ "\""
    LexWhite(_) -> "white"
    LexInsLCurly -> "start of statements ('{')"
    LexInsRCurly -> "end of statements ('}')"
    LexInsSemi -> "end of statement (';')"
    LexError(s) -> "error: " ++ s ++ ""
    LexCons(n) -> "constructor \"" ++ n.show ++ "\""
    LexTypeId(n, s) -> "typedid " ++ n.show ++ ":" ++ s
