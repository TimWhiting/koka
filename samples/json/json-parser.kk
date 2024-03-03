import std/data/json-parse
import std/data/json

fun show(j: jslex): string
  match j
    JSStr(str) -> str.string
    json-parse/JSNum(num) -> num.string
    JSTrue -> "true"
    JSFalse -> "false"
    json-parse/JSNull -> "null"
    JSObjOpen -> "{"
    JSObjColon -> ":"
    JSObjClose -> "}"
    JSArrayOpen -> "["
    JSArrayClose -> "]"
    JSValueSep -> ","
    JSWhite -> " "

fun main()
  match r#"{"name":"Gpa142749579","age":365380512,"children":[{"name":"another child219059342"}],"adult-children":[]}"#.slice.alexScan(0)
    AlexToken(s,_,p) -> p(s).show.println
    AlexEOF -> "EOF".println
    AlexSkip -> "skip".println
    AlexError -> "error".println