import std/num/ddouble
import std/num/float64
import std/core/undiv
import std/text/regex
import std/text/regexparser

type json
  JNull
  JBool(b: bool)
  JString(string: string)
  JNum(double: float64)
  JInt(int: int)
  JList(list: list<json>)
  JObj(dict: list<(string,json)>)

fun json/show(j: json): string
  match j
    JNull -> "null"
    JBool(b) -> if b then "true" else "false"
    JString(s) -> "\"" ++ s ++ "\""
    JNum(s) -> s.show
    JInt(i) -> i.show
    JList(l) -> l.show(?show=fn(s) s.pretend-decreasing.show)
    JObj(dict) -> "{" ++ dict.map(fn((k, v)) "\"" ++ k ++ "\":" ++ v.pretend-decreasing.show).join(",") ++ "}"

// TODO: - collapse short arrays / objects onto a line
fun json/pretty(j: json, indent: int=0): string
  match j
    JNull -> "null"
    JBool(b) -> if b then "true" else "false"
    JString(s) -> "\"" ++ s ++ "\""
    JNum(s) -> s.show
    JInt(i) -> i.show
    JList(l) -> 
      val current-indent = " ".repeat(indent) 
      val next-indent = " ".repeat(indent + 2)
      "[\n" ++ next-indent ++ 
        l.map(fn(s) s.pretend-decreasing.pretty(indent + 2)).join(",\n" ++ next-indent) 
        ++ "\n" ++ current-indent ++ "]"
    JObj(dict) -> 
      val current-indent =  " ".repeat(indent)
      val next-indent = " ".repeat(indent + 2)
      val sep = ",\n" ++ next-indent
      "{\n" 
        ++ next-indent ++ 
          dict.map(fn((k, v)) 
            "\"" ++ k ++ "\": " ++ v.pretend-decreasing.pretty(indent + 2)
          ).join(sep) ++
       "\n" ++ current-indent ++ "}"

fun list/to-json(l: list<v>, ?to-json: v -> e json): e json
  JList(l.map(to-json))

fun maybe/to-json(m: maybe<v>, ?to-json: v -> e json): e json
  match m
    Nothing -> JNull
    Just(v) -> v.to-json 

fun string/to-json(s: string): json
  JString(s)

fun num/to-json(d: ddouble): json
  JNum(d.float64)

fun int/to-json(i: int): json
  JInt(i)

fun bool/to-json(b: bool): json
  JBool(b)

fun float64/to-json(f: float64): json
  JNum(f)

fun id/to-json(j: json): json
  j

fun either/to-json(e: either<a,b>, key1: string, key2: string, ?a/to-json: a -> e json, ?b/to-json: b -> e json): e (string,json)
  match e
    Left(a) -> (key1, a.to-json)
    Right(b) -> (key2, b.to-json)

fun dict/to-json(d: list<(string, v)>, ?to-json: v -> e json): e json
  JObj(d.map(fn((k, v)) (k, v.to-json)))

pub extend type exception-info
  JsonDeserializationException(d: json, path: string)

fun string/from-json(j: json, path: string): pure string
  match j
    JString(s) -> s
    _ -> throw("Expecting string, got " ++ j.show, info=JsonDeserializationException(j, path))

fun bool/from-json(j: json, path: string): pure bool
  match j
    JBool(b) -> b
    _ -> throw("Expecting bool, got " ++ j.show, info=JsonDeserializationException(j, path))

fun int/from-json(j: json, path: string): pure int
  match j
    JNum(n) -> n.int
    JInt(i) -> i
    _ -> throw("Expecting num (int or ddouble coerced to int), got " ++ j.show, info=JsonDeserializationException(j, path))

fun double/from-json(j: json, path: string): pure ddouble
  match j
    JNum(d) -> d.ddouble
    JInt(i) -> i.ddouble
    _ -> throw("Expecting ddouble, got " ++ j.show, info=JsonDeserializationException(j, path))

fun float64/from-json(j: json, path: string): pure float64
  match j
    JNum(d) -> d
    JInt(i) -> i.float64
    _ -> throw("Expecting float64, got " ++ j.show, info=JsonDeserializationException(j, path))

fun dict/from-json(l: list<(string, json)>, key: string, path: string, ?from-json: (j: json, path: string) -> pure a): pure a
  match l.lookup(fn(k) k == key)
    Nothing -> throw("Expecting " ++ key ++ " in " ++ JObj(l).show, info=JsonDeserializationException(JObj(l), path))
    Just(s) -> from-json(s, path=path ++ "->" ++ key)

fun either/from-json(l: list<(string, json)>, key1: string, key2: string, path: string, ?a/from-json: (j: json, path: string) -> pure a, ?b/from-json: (j: json, path: string) -> pure b): pure either<a,b> 
  match l.lookup(fn(k) k == key1)
    Just(s) -> Left(a/from-json(s, path=path ++ "->" ++ key1))
    Nothing -> match l.lookup(fn(k) k == key2)
      Just(s) -> Right(b/from-json(s, path=path ++ "->" ++ key2))
      Nothing -> throw("Expecting " ++ key1 ++ " or " ++ key2 ++ " in " ++ JObj(l).show, info=JsonDeserializationException(JObj(l), path))

fun to-dict/as-object(j: json, path: string): pure list<(string, json)>
  match j
    JObj(d) -> d
    _ -> throw("Expecting object, got " ++ j.show, info=JsonDeserializationException(j, path))

fun list/from-json(j: json, path: string, ?from-json: (j: json, path: string) -> pure a): pure list<a>
  match j
    JList(l) -> 
      l.map-indexed fn(i, j1)
        from-json(j1, path=path ++ "[" ++ i.show ++ "]")
    _ -> throw("Expecting list, got " ++ j.show, info=JsonDeserializationException(j, path))

fun maybe/from-json(j: json, path: string, ?from-json: (j: json, path: string) -> pure a): pure maybe<a>
  match j
    JNull -> Nothing
    _ -> Just(from-json(j, path))

fun id/from-json(j: json, path: string): pure json
  j

fun parse(j: json, from-json: (j: json, path: string) -> <exn,exn|e> a): <exn|e> a
  match try({from-json(j, "root")})
    Ok(a) -> a
    Error(e) -> throw("Error parsing json\n\t" ++ e.message ++ " in path \"" ++ e.info.path ++ "\"")

fun path(e: exception-info): string
  match e
    JsonDeserializationException(_, path) -> path
    _ -> ""

val leadingHexDotRegex = r"[+-]?0[xX]\.[0-9a-fA-F_]+([eEpP][+-]?[0-9a-fA-F_]+)?".regex() 
val wholeHexFloatRegex = r"[+-]?0[xX][0-9a-fA-F_]+(\.[0-9a-fA-F_]+)?([eEpP][+-]?[0-9a-fA-F_]+)?".regex() 
val integerRegex = r"[+-]?[0-9]+".regex() 
fun integer()
  takePattern(integerRegex)

fun exp()
  integer()

fun decfloat()
  (fn() takePattern(wholeFloatRegex)).or({takePattern(leadingDotRegex)})

fun hexfloat()
  (fn() takePattern(wholeHexFloatRegex)).or({takePattern(leadingHexDotRegex)})

fun pLit()
  val x = ors([{text("true"); JBool(True)},{text("false"); JBool(False)},{text("null"); JNull}])
  optional(pWhitespace)
  x

fun pFloat()
  val d = or({decfloat().string.split("_").join}, {hexfloat().string.split("_").join})
  optional(pWhitespace)
  // trace(d)
  JNum(d.parse-float64.unjust)

fun pInteger()
  val d = integer().string.split("_").join
  optional(pWhitespace)
  // trace(d)
  JInt(d.parse-int.unjust)

val stringRegex = r#""[^\\\"]*(?:\\.[^"\\]*)*""#.regex()

inline fun takeString()
  val s = takePattern(stringRegex)
  s.advance(1).extend(-2).string

fun pString()
  val s = takeString()
  optional(pWhitespace)
  JString(s)

fun pArray()
  pToken("[")
  with scope("parray")
  val xs = separatedTrailing(pValue,{pToken(",")})
  pToken("]")
  JList(xs)

fun pMember(): <div,exn,parse<string>> (string,json)
  val k = takeString()
  with scope("pmember")
  optional(pWhitespace)
  pToken(":")
  val v = pValue()
  (k, v)

fun pObject() 
  pToken("{")
  with scope("pobject")
  val members = separatedTrailing(pMember, {pToken(",")})
  val o = JObj(members)
  pToken("}")
  o

fun pValue(): <div,exn,parse<string>> json
  ors([pArray,pObject,pString,pFloat,pInteger,pLit])

val spacesRegex = r"([ \n\t\r]|\/\/[^\n]+)+".regex()
fun pWhitespace()
  spacesRegex.takePattern()

fun pToken(s: string)
  text(s)
  optional(pWhitespace)

fun str/parse(s: string)
  match s.run(pValue)
    Right(e) -> e
    Left(err) -> throw("Error:\n" ++ err.show(s))