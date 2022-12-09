import std/text/parse
import std/text/regex
import std/text/unicode
import std/os/path
import std/os/file
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

fun digitChar()
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
  char-is("escape", fn(c) -> c != '\\' || c != '\'' || c != '"').string

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
  [letter, digitChar, underscore, dash].choose

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
  underscore() ++ many1(digitChar).join

fun hexdigitsep()
  underscore() ++ many1(hexdigit).join

fun kdigits()
  many1(digitChar).join ++ many(digitsep).join

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
  x ++ many1(digitChar).join

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


fun lex-space()
  LexWhite(many1(space).join)

fun lex-newline()
  newline()
  LexWhite("\n")

fun lex-start-comment()
  pstring("/*")
  val x = many(symbol).join
  LexError("TODO")

fun lex-start-line-comment()
  pstring("//")
  val x = many(symbol).join
  LexError("TODO")

fun lex-linedirective()
  newline()
  pstring("#")
  val x = many(symbol).join
  LexError("TODO")

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
  val inner = many({[stringchar, {pstring("\\") ++ char-esc()}, {pstring("\\") ++ hex-esc()}, newline].choose}).join()
  val err = illegal-str.many()
  pstring("\"")
  match err
    Cons(e, _) -> e
    Nil -> LexString(inner)

fun illegal-str()
  val res = many1({char-is("Illegal string character", fn(c) -> c != '"')}).string
  LexError(res)

fun lex-rstringbegin()
  pstring("r") ++ many({char-is("Raw Comment", fn(c) -> c == '#')}).string ++ pstring("\"")
  val inner = many({[stringraw].choose}).join()
  val err = illegal-str.many()
  pstring("\"") ++ many({char-is("Raw Comment", fn(c) -> c == '#')}).string
  match err
    Cons(e, _) -> e
    Nil -> LexString(inner)

fun lex-linecomment()
  val start = pstring("//") ++ many(symbol).join
  val inner = many({[linechar].choose}).join()
  val err = many({char-is("Anything", fn(c) -> c != '\n')}).string
  newline()
  match err.list
    Cons(_, __) -> LexError(err)
    _ -> LexComment(start ++ inner)

fun lex-charesc()
  pstring("\'\\")
  val c = char-esc().head-char.default(' ')
  pstring("'")
  LexChar(c)

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
  [lex-space,lex-newline,lex-linecomment,lex-qconid,lex-qvarid,lex-qidop,lex-lowerid,lex-conid,lex-idchars,lex-special,lex-decfloat,lex-hexfloat,lex-integer,lex-or,lex-idop,lex-symbols,lex-stringbegin,lex-rstringbegin,lex-charesc,lex-hexesc,lex-char].choose

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
  retained: list<list<char>>
  previous: char
  current: list<char>
  previousLex: lex
  rawEnd: list<char>

linear effect lexE
  fun curr-state(): lex-state

type lex-part
  Default
  StringLit
  StringRaw
  Comment
  LineComment
  LineDirective

fun lexer(sourceName: string, lineNo: int, input: string)
  lexing(Source(sourceName, input), lineNo, input)

fun lex(source: source, lineNo: int, input: string): div list<lexeme>
  match lexing(source, lineNo, input)
    ParseOk(u, _) -> u.map(fn(x) Lexeme(rangeNull, x))
    _ -> Cons(Lexeme(rangeNull, LexError("Unexpected end of input")), Nil)

fun lexEHandler(initialState:lex-state, action: () -> <lexE| e> a): e a
  var state := initialState
  with handler
    fun curr-state()
      state
  action()

fun lexing(source: source, lineNo: int, input: string): <div> parse-error<list<lex>>
  // with parse(input.slice)
  with parseGreedy(input.slice)
  var initPos := Pos(source, 0, lineNo, 1)
  with lexEHandler(Lex-state(initPos, initPos, [], '\n', input.list, LexWhite(""), "\"".list))
  var result := Nil
  while { ! current-input().is-empty() }
    result := Cons(lex-default(), result)
  result.reverse

fun main()
  // Make sure to set $ulimit -s unlimited$ to allow more stack space
  val r = read-text-file("src-koka/syntax/lexer.kk".path)
  val x = lexer("test", 0, r)
  match x
    ParseOk(u, _) -> u.map(show).join(",").println
    ParseError(msg, _) -> msg.println

pub fun parseGreedy(input0 : sslice, action : () -> <parse|e> a ) : e parse-error<a> 
  var input := input0
  with handler
    return (x)
      ParseOk(x, input)
    fun current-input()
      input
    brk fail(msg)
      ParseError(msg, input)
    fun satisfy(pred)
      val inp = input
      val m   = fn() : total _ { pred(inp) }
      match m() 
        Just((x,cap)) -> { input := cap; Just(x) }
        Nothing       -> Nothing
    ctl pick()
      val save = input;
      match resume(True)
        ParseOk(x1, rest1) -> ParseOk(x1, rest1)
        ParseError(msg, restErr1) -> 
          input := save
          match resume(False)   // todo: limit lookahead?
            ParseOk(x2, rest2) -> 
              if restErr1.count < rest2.count then ParseError(msg, restErr1) else ParseOk(x2, rest2) 
            ParseError(msg2, restErr2) -> 
              if restErr2.count < restErr1.count then ParseError(msg2, restErr2) else ParseError(msg, restErr1)
  action()