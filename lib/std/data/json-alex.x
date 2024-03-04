{
import std/data/json
import std/num/float64

type jslex
  JSStr(str: sslice)
  JSNum(num: sslice)
  JSTrue
  JSFalse
  JSNull
  JSObjOpen
  JSObjColon
  JSObjClose
  JSArrayOpen
  JSArrayClose
  JSValueSep
  JSWhite

alias action = sslice -> pure jslex
alias alexInput = sslice
fun alexGetByte(s: alexInput): maybe<(char, alexInput)>
  s.next()

fun alexInputPrevChar(s: alexInput): char
  '_'

}

%encoding "utf8"

-----------------------------------------------------------
-- Character sets
-----------------------------------------------------------
$exp          = [eE]
$digit        = [0-9]
$onenine      = [1-9]
$sign         = [\+\-]
$ws           = [\ \t\n\r]
$hex          = [0-9a-fA-F]

-----------------------------------------------------------
-- Regular expressions
-----------------------------------------------------------
@digits       = $digit+
@exponent     = $exp $sign? @digits
@fraction     = '.' @digits
@integer      = $digit
              | $onenine @digits
              | '-' digit
              | '-' $onenine @digits

@number       = @integer @fraction? @exponent?
@escape       = \" | '\\' | '\/' | 'b' | 'f' | 'n' | 'r' | 't' | 'u' $hex $hex $hex $hex
@character    = [\x0020 - \x10FFFF] # [\"\\] | '\\' @escape
@string       = \" @character* \"
@whitespace   = $ws

-----------------------------------------------------------
-- Main tokenizer
-----------------------------------------------------------
program :-
-- white space
<0> @whitespace           { fn(s) JSWhite }
<0> @number               { fn(s) JSNum(s) }
<0> "true"                 { fn(s) JSTrue }
<0> "false"                { fn(s) JSFalse }
<0> "null"                 { fn(s) JSNull }
<0> ","               { fn(s) JSValueSep }
<0> "{"           { fn(s) JSObjOpen }
<0> "}"          { fn(s) JSObjClose }
<0> ":"            { fn(s) JSObjColon }
<0> "["            { fn(s) JSArrayOpen }
<0> "]"           { fn(s) JSArrayClose }
<0> @string               { fn(s) JSStr(s) }

{
}