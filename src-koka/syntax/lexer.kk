import std/text/parse
import std/text/regex
import std/text/unicode
import std/os/path
import common/name
import common/range
import std/num/float64
import syntax/lexeme


// Character sets

fun dot()
  char-is("dot", fn(c) -> c == '.').string

fun question()
  char-is("question", fn(c) -> c == '?').string

fun forward-slash()
  char-is("forward-slash", fn(c) -> c == '/').string

fun open-paren()
  char-is("open-paren", fn(c) -> c == '(').string

fun close-paren()
  char-is("close-paren", fn(c) -> c == ')').string

fun underscore()
  char-is("underscore", fn(c) -> c == '_').string

fun dash()
  char-is("dash", fn(c) -> c == '-').string

fun digit()
  char-is("digit", fn(c) -> c >= '0' && c <= '9').string

fun hexdigit()
  char-is("hex-digit", fn(c) -> c.is-hex-digit).string

fun lower()
  char-is("lower-case", fn(c) -> c.is-lower).string

fun upper()
  char-is("upper-case", fn(c) -> c.is-upper).string

fun letter()
  char-is("letter", fn(c) -> c.is-upper || c.is-lower).string

fun space()
  char-is("space", fn(c) -> c == ' ').string

fun tab()
  char-is("tab", fn(c) -> c == '\t').string

fun ret()
  char-is("return", fn(c) -> c == '\r').string

fun line-feed()
  char-is("line-feed", fn(c) -> c == '\n').string

fun graphic()
  char-is("graphic", fn(c) -> c >= '\x21' && c <= '\x7E').string

fun cont()
  char-is("cont", fn(c) -> c >= '\x80' && c <= '\xBF').string

fun symbol()
  char-is("symbol", fn(c) -> c == '$' || c == '%' || c == '&' || c == '*' || c == '+' || c == '~' || c == '!' || c == '\\' || c == '^' || c == '#' || c == '=' || c == '.' || c == ':' || c == '-' || c == '?' || c == '|' || c == '<' || c == '>').string

fun special()
  char-is("special", fn(c) -> c == '(' || c == ')' || c == '[' || c == ']' || c == '{' || c == '}' || c == ';' || c == ',').string

fun anglebar()
  char-is("anglebar", fn(c) -> c == '<' || c == '>').string

fun finalid()
  char-is("finalid", fn(c) -> c == '\'').string

fun char-esc()
  char-is("escape", fn(c) -> c == '\\' || c == '\'' || c == '"').string

// Regular expressions

fun newline()
  optional("", ret) ++ line-feed()

fun utf8valid1()
  char-is("utf8valid1", fn(c) -> c >= '\xC2' && c <= '\xDF').string ++
  cont()

fun utf8valid2()
  char-is("utf8valid2", fn(c) -> c == '\xE0').string ++
  char-is("utf8valid2.1", fn(c) -> c >= '\xA0' && c <= '\xBF').string ++
  cont()

fun utf8valid3()
  char-is("utf8valid3", fn(c) -> c >= '\xE1' && c <= '\xEC').string ++
  cont() ++
  cont()

// More utf8
fun utf8valid()
  [utf8valid1, utf8valid2, utf8valid3].choose

fun utf8()
  utf8valid()

fun linechar()
  [graphic, space, tab, utf8].choose

fun graphic-comment()
  char-is("graphic-comment", fn(c) -> c != '/' && c != '*' && c >= '\x21' && c <= '\x7E').string

fun commentchar()
  [graphic-comment, space, tab, newline, utf8].choose

fun hexdigit2()
  hexdigit() ++ hexdigit()

fun hexdigit4()
  hexdigit() ++ hexdigit() ++ hexdigit() ++ hexdigit()

fun hexesc1()
  char-is("hex-prefix", fn(c) -> c == 'x').string ++ hexdigit2()

fun hexesc2()
  char-is("hex-prefix", fn(c) -> c == 'u').string ++ hexdigit4()

fun hexesc3()
  char-is("hex-prefix", fn(c) -> c == 'U').string ++ hexdigit4() ++ hexdigit2()

fun hex-esc()
  [hexesc1, hexesc2, hexesc3].choose

fun escape()
  char-is("escape", fn(c) -> c == '\\').string ++ [hex-esc, char-esc].choose

fun graphic-string()
  char-is("graphic-string", fn(c) -> c != '"' && c != '\\' && c >= '\x21' && c <= '\x7E').string

fun stringchar()
  [graphic-string, space, utf8].choose

fun graphic-char()
  char-is("graphic-char", fn(c) -> c != '\'' && c != '\\' && c >= '\x21' && c <= '\x7E').string

fun charchar()
  [graphic-char, space, utf8].choose

fun graphic-stringraw()
  char-is("graphic-stringraw", fn(c) -> c != '"' && c >= '\x21' && c <= '\x7E').string

fun stringraw()
  [graphic-stringraw, space, tab, newline, utf8].choose

fun idchar()
  [letter, digit, underscore, dash].choose

fun lowerid()
  lower() ++ many(idchar).join ++ many(finalid).join

fun upperid()
  upper() ++ many(idchar).join ++ many(finalid).join

fun conid()
  upperid()

fun modulepath()
  many1({lowerid(); forward-slash()}).join

fun qvarid()
  modulepath() ++ lowerid()

fun qconid()
  modulepath() ++ upperid()

fun psymbols()
  [{many1(symbol).join}, forward-slash].choose

fun qidop()
  modulepath() ++ open-paren() ++ psymbols() ++ close-paren()

fun idop()
  open-paren() ++ psymbols() ++ close-paren()

fun digitsep()
  underscore() ++ many1(syntax/lexer/digit).join

fun hexdigitsep()
  underscore() ++ many1(hexdigit).join

fun kdigits()
  many1(syntax/lexer/digit).join ++ many(digitsep).join

fun hexdigits()
  many1(hexdigit).join ++ many(hexdigitsep).join

fun zero()
  char-is("zero", fn(c) -> c == '0').string

fun non-zero()
  char-is("1-9", fn(c) -> c >= '1' && c < '9').string ++
  optional("")
    underscore() ++ kdigits()

fun decimal()
  [zero, non-zero].choose

fun hexadecimal()
  char-is("hex-prefix", fn(c) -> c == '0').string ++
  char-is("hex-prefix", fn(c) -> c == 'x' || c == 'X').string ++
  hexdigits()

fun integer()
  one-of-or("+-", '+').string ++
  [decimal, hexadecimal].choose

fun exp()
  val x = optional("")
    char-is("prefix", fn(c) -> c == '+' || c == '-').string
  x ++ many1(syntax/lexer/digit).join

fun kexp10()
  char-is("exp10", fn(c) -> c == 'e' || c == 'E').string ++
  exp()

fun kexp2()
  char-is("exp2", fn(c) -> c == 'p' || c == 'P').string ++
  exp()

fun decfloat()
  one-of-or("+-", '+').string ++ decimal() ++ 
  [{dot(); kdigits(); optional("", kexp10)}, kexp10].choose

fun hexfloat()
  one-of-or("+-", '+').string ++ hexadecimal() ++
  [{dot(); hexdigits(); optional("", kexp2)}, kexp2].choose

// Start on tokenizing

linear effect lexE
  fun set-lex(s: lex-part) : lex
  fun push-lex(s: lex-part) : lex
  fun pop-lex() : lex

type lex-part
  Default
  StringLit
  StringRaw
  Comment
  LineComment
  LineDirective

fun lex-space()
  LexWhite(many1(space).join)

fun lex-newline()
  newline()
  LexWhite("\n")

fun lex-start-comment()
  pstring("/*")
  val x = many(symbol).join
  set-lex(Comment)

fun lex-start-line-comment()
  pstring("//")
  val x = many(symbol).join
  set-lex(LineComment)

fun lex-linedirective()
  newline()
  pstring("#")
  val x = many(symbol).join
  set-lex(LineDirective)

fun lex-qconid()
  LexCons(qconid().newQName)

fun lex-qvarid()
  LexId(qvarid().newQName)

fun lex-qidop()
  LexOp(qidop().stripParens.newQName)

fun lex-lowerid()
  val s = lowerid()
  if s.isReserved then
    LexKeyword(s, "")
  else if s.list.isMalformed then
    LexError(messageMalformed)
  else
    LexId(s.newName)

fun lex-conid()
  LexCons(conid().newName)

fun lex-idchars()
  pstring("_")
  LexWildCard(many(idchar).join.newName)

fun lex-special()
  LexSpecial(special())

fun lex-decfloat()
  val d = decfloat().list.filter(fn(c) { c != '_' }).string
  LexFloat(d.parse-float64.default(-1.0), d)

fun lex-hexfloat()
  val d = hexfloat().list.filter(fn(c) { c != '_' }).string
  LexFloat(d.parse-float64.default(-1.0), d)

fun lex-integer()
  val d = integer().list.filter(fn(c) { c != '_' }).string
  LexInt(d.parse-int.default(-1), d)

fun lex-or()
  LexOp(pstring("||").newName)

fun lex-anglebar()
  // TODO:
  LexKeyword("", "")

fun lex-idop()
  LexIdOp(idop().stripParens.newName)

fun lex-symbols()
  val s = psymbols()
  if s.isReserved then
    LexKeyword(s, "")
  else if s.isPrefixOp then
    LexPrefix(s.newName)
  else
    LexOp(s.newName)

fun lex-stringbegin()
  pstring("\"")
  set-lex(StringLit)

fun lex-rstringbegin()
  pstring("r\"") // TODO: r#""
  set-lex(StringRaw)

fun lex-charesc()
  pstring("\'\\")
  val c = char-esc()
  pstring("'")
  LexChar(c.list.drop(2).head('*').fromCharEsc)

fun lex-hexesc()
  pstring("\'\\")
  val c = hex-esc()
  pstring("'")
  LexChar(c.list.drop(3).head('*').fromCharEsc)

fun lex-char()
  pstring("\'")
  val c = charchar().head-char.default(' ')
  pstring("\'")
  LexChar(c)

fun lex-emptychar()
  pstring("\'")
  val c = char-is("any", fn(_) -> True)
  pstring("\'")
  LexError("Illegal character literal: " ++ c.string)
  
fun lex-tab()
  val t = many1(tab).join
  LexError("Illegal tab character: configure your editor to use spaces instead")

fun lex-unknown()
  val c = char-is("any", fn(_) -> True)
  LexError("Illegal character: " ++ c.string)

fun lex-default()
  [lex-space, lex-newline, lex-start-comment].choose

fun stringlit-utf8unsafe()
  // TODO
  LexError("TODO")

fun stringlit-stringchar()
  stringchar() // TODO: Lexer transition helpers

fun stripParens(s: string)
  match s.list.reverse
    Cons(')', cs) -> 
      match cs.span(fn(c) { c != '(' })
        (op, Cons('(', qual)) -> (op ++ qual).reverse.string
        _ -> s
    _ -> s

fun newQName(s: string) 
  val (rname, rsmod) = s.list.reverse.span(fn(c) { c != '/' })
  match rsmod // TODO: First case needs condition on rname == Nil
    Cons('/', Cons('/', rmod)) -> newQualified(rmod.reverse.string, "/")
    Cons('/', rmod) -> newQualified(rmod.reverse.string, rname.reverse.string)
    _ -> s.newName

fun fromCharEsc(c)
  match c
    'n' -> '\n'
    'r' -> '\r'
    't' -> '\t'
    _ -> c

fun unsafeChar(k: string, s: string): lex
  LexError("Unsafe character in " ++ k ++ ": " ++ s) //TODO: ++ showHex(4, s.list.head))

// Reserved

val specialNames = [ "{", "}"
    , "(", ")"
    , "<", ">"
    , "[", "]"
    , ";", ","
]

val reservedNames =  ["infix", "infixr", "infixl", "prefix", "postfix"
    , "type", "alias"
    , "struct", "enum", "con"
    , "val", "fun", "fn", "extern", "var"
    , "ctl", "final", "raw"
    , "if", "then", "else", "elif"
    , "return", "match", "with", "in"
    , "forall", "exists", "some"
    , "pub", "abstract"
    , "module", "import", "as"

    // effect handlers
    , "handler", "handle"
    , "effect", "receffect"
    , "named"
    , "mask"
    , "override"   

    // deprecated
    , "private", "public"  // use pub
    , "rawctl", "brk"      // use raw ctl, and final ctl

    // alternative names for backwards paper compatability
    , "control", "rcontrol", "except"
    , "ambient", "context" // use effcet
    , "inject"       // use mask
    , "use", "using" // use with instead
    , "function"     // use fun
    , "instance"     // use named

    // future reserved
    , "interface"
    , "unsafe"

    // operators
    , "="
    , "."
    , ":"
    , "->"
    , "<-"
    , ":="
    , "|"]

val symbols = "$%&*+~!/\\^~=.:-?<>|".list

fun isReserved(name: string)
  reservedNames.any(fn(n) -> n == name) // TODO: Set

fun isPrefixOp(name: string)
  name == "!" || name == "~"

fun isMalformed(name: list<char>)
  match name
    Cons('-', Cons(c, cs)) -> !c.is-alpha || cs.isMalformed
    Cons(c, Cons('-', cs)) -> !c.is-alpha || c.is-digit || cs.isMalformed
    Cons(_, cs) -> cs.isMalformed
    Nil -> False

val messageMalformed
  = "malformed identifier: a dash must be preceded by a letter or digit, and followed by a letter"

// Lexer state and actions
struct lex-state
  pos: pos
  startPos: pos
  states: list<int>
  retained: list<list<char>>
  previous: char
  current: list<char>
  previousLex: lex
  rawEnd: list<char>

alias action = (list<char>, lex-state, lex-state) -> (maybe<lex>, lex-state)
// Action helpers

fun token(f: list<char> -> lex): action
  fn(cs, st0, st1)
    (Just(f(cs)), st1)

fun string(f: string -> lex): action
  token(fn(cs) -> f(cs.string))

fun keyword(): action
  string(fn(s) -> LexKeyword(s, ""))

fun next(state: int, action: action): action
  fn(cs, st0, st1)
    val (x, st2) = action(cs, st0, st1)
    (x, st2(states = Cons(state, st1.states)))

fun push(a: action): action
  fn(cs, st0, st1)
    next(st1.states.head.default(-1), a)(cs, st0, st1)

fun pop(a: (int) -> action): action
  fn(cs, st0, st1)
    val sts = st1.states.tail
    val sts_ = match sts
      Nil -> [0]
      _ -> sts
    val (x, st2) = a(sts_.head.default(-1))(cs, st0, st1)
    (x, st2(states = sts_))

fun more(f: list<char> -> list<char>): action
  fn(cs, st0, st1)
    (Nothing, st1(retained = Cons(f(cs), st1.retained)))

fun less(n: int, a: action): action
  fn(cs, st0, st1)
    val cs2 = st0.current.take(n)
    val pos2 = st0.pos.posMoves8(cs2)
    val st2 = st1(pos = pos2, current = st0.current.drop(n))
    a(cs2, st0, st2)

fun withmore(a: action): action
  fn(cs, st0, st1)
    a(Cons(cs, st1.retained).reverse.concat, st0, st1(retained=[]))

fun rawdelim(a: action): action
  fn(cs, st0, st1)
    a(cs, st0, st1(rawEnd = Cons('\"', replicate('#', cs.length - 2))))

fun withRawDelim(f: (list<char>, list<char>) -> action): action
  fn(cs, st0, st1)
    f(cs, st1.rawEnd)(cs, st0, st1)

fun constant(x)
  token(fn(cs) -> x)



fun lexer(sourceName: string, line: int, input: string)
  lexing(Source(sourceName, input) lineNo, input.list)

fun lexing(source: source, lineNo: int, input: string)
  with parse(s.slice)
  var initPos := Pos(source, 0, lineNo, 1)
  var initSt := Lex-State(initPos, initPos, [0], [], '\n', input, LexWhite(""), "\"")
  () // TODO: Start scanner



// fun main(): <io> ()
//   val x = do-parse("-0x1a.1a")
//   match x
//     ParseOk(r, _) -> r.println
//     ParseError(msg, _) -> msg.println
