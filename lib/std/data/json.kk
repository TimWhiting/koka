import std/num/ddouble
import std/num/float64
import std/core/undiv

type json
  JSNull
  JSBool(b: bool)
  JSString(string: string)
  JSNum(double: float64)
  JSInt(int: int)
  JSList(list: list<json>)
  JSObj(dict: list<(string,json)>)

fun json/show(j: json): string
  match j
    JSNull -> "null"
    JSBool(b) -> if b then "true" else "false"
    JSString(s) -> "\"" ++ s ++ "\""
    JSNum(s) -> s.show
    JSInt(i) -> i.show
    JSList(l) -> l.show(?show=fn(s) s.pretend-decreasing.show)
    JSObj(dict) -> "{" ++ dict.map(fn((k, v)) "\"" ++ k ++ "\":" ++ v.pretend-decreasing.show).join(",") ++ "}"

// TODO: - collapse short arrays / objects onto a line
fun json/pretty(j: json, indent: int=0): string
  match j
    JSNull -> "null"
    JSBool(b) -> if b then "true" else "false"
    JSString(s) -> "\"" ++ s ++ "\""
    JSNum(s) -> s.show
    JSInt(i) -> i.show
    JSList(l) -> 
      val current-indent = " ".repeat(indent) 
      val next-indent = " ".repeat(indent + 2)
      "[\n" ++ next-indent ++ 
        l.map(fn(s) s.pretend-decreasing.pretty(indent + 2)).join(",\n" ++ next-indent) 
        ++ "\n" ++ current-indent ++ "]"
    JSObj(dict) -> 
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
  JSList(l.map(to-json))

fun maybe/to-json(m: maybe<v>, ?to-json: v -> e json): e json
  match m
    Nothing -> JSNull
    Just(v) -> v.to-json 

fun string/to-json(s: string): json
  JSString(s)

fun num/to-json(d: ddouble): json
  JSNum(d.float64)

fun int/to-json(i: int): json
  JSInt(i)

fun bool/to-json(b: bool): json
  JSBool(b)

fun float64/to-json(f: float64): json
  JSNum(f)

fun id/to-json(j: json): json
  j

fun either/to-json(e: either<a,b>, key1: string, key2: string, ?a/to-json: a -> e json, ?b/to-json: b -> e json): e (string,json)
  match e
    Left(a) -> (key1, a.to-json)
    Right(b) -> (key2, b.to-json)

fun dict/to-json(d: list<(string, v)>, ?to-json: v -> e json): e json
  JSObj(d.map(fn((k, v)) (k, v.to-json)))

pub extend type exception-info
  JsonDeserializationException(d: json, path: string)

fun string/from-json(j: json, path: string): pure string
  match j
    JSString(s) -> s
    _ -> throw("Expecting string, got " ++ j.show, info=JsonDeserializationException(j, path))

fun bool/from-json(j: json, path: string): pure bool
  match j
    JSBool(b) -> b
    _ -> throw("Expecting bool, got " ++ j.show, info=JsonDeserializationException(j, path))

fun int/from-json(j: json, path: string): pure int
  match j
    JSNum(n) -> n.int
    JSInt(i) -> i
    _ -> throw("Expecting num (int or ddouble coerced to int), got " ++ j.show, info=JsonDeserializationException(j, path))

fun double/from-json(j: json, path: string): pure ddouble
  match j
    JSNum(d) -> d.ddouble
    JSInt(i) -> i.ddouble
    _ -> throw("Expecting ddouble, got " ++ j.show, info=JsonDeserializationException(j, path))

fun float64/from-json(j: json, path: string): pure float64
  match j
    JSNum(d) -> d
    JSInt(i) -> i.float64
    _ -> throw("Expecting float64, got " ++ j.show, info=JsonDeserializationException(j, path))

fun dict/from-json(l: list<(string, json)>, key: string, path: string, ?from-json: (j: json, path: string) -> pure a): pure a
  match l.lookup(fn(k) k == key)
    Nothing -> throw("Expecting " ++ key ++ " in " ++ JSObj(l).show, info=JsonDeserializationException(JSObj(l), path))
    Just(s) -> from-json(s, path=path ++ "->" ++ key)

fun either/from-json(l: list<(string, json)>, key1: string, key2: string, path: string, ?a/from-json: (j: json, path: string) -> pure a, ?b/from-json: (j: json, path: string) -> pure b): pure either<a,b> 
  match l.lookup(fn(k) k == key1)
    Just(s) -> Left(a/from-json(s, path=path ++ "->" ++ key1))
    Nothing -> match l.lookup(fn(k) k == key2)
      Just(s) -> Right(b/from-json(s, path=path ++ "->" ++ key2))
      Nothing -> throw("Expecting " ++ key1 ++ " or " ++ key2 ++ " in " ++ JSObj(l).show, info=JsonDeserializationException(JSObj(l), path))

fun to-dict/as-object(j: json, path: string): pure list<(string, json)>
  match j
    JSObj(d) -> d
    _ -> throw("Expecting object, got " ++ j.show, info=JsonDeserializationException(j, path))

fun list/from-json(j: json, path: string, ?from-json: (j: json, path: string) -> pure a): pure list<a>
  match j
    JSList(l) -> 
      l.map-indexed fn(i, j1)
        from-json(j1, path=path ++ "[" ++ i.show ++ "]")
    _ -> throw("Expecting list, got " ++ j.show, info=JsonDeserializationException(j, path))

fun maybe/from-json(j: json, path: string, ?from-json: (j: json, path: string) -> pure a): pure maybe<a>
  match j
    JSNull -> Nothing
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
