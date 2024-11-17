import std/core/string
import std/core/types
import std/core/lazy
import std/core/undiv
import std/core/int

pub infixr 60  (|.|)
pub infixr 60  (|-|)
pub infixr 60  (\)
pub infixr 60  (\-)

// A string builder allows processing a concatenated string one piece at a time
//    without waiting for the rest to be appended / generated.
// As such it is like a list of strings but: 
//   1. Will convert polymorphic values to strings
//     - only when / as needed
//     - only converting once (for non-unique references to the builder)
//     - ensuring a short lifetime for the converted string values (for unique references to the builder, and immediate usage)
//   2. Will concat two string builders incrementally
// 
// For example this datastructure is useful for writing to a file
//   where we can start writing the first part of the string (?async) while the rest is still being processed. 
// Also it is useful in places like debug output / assert strings
//   where we can specify how to build the debug string, without taking up processing to build it eagerly (in case the assertion is not triggered)
// 
// The string builder has some pretty-printing ability as well with newlines and indentation handled specially
// Additionally spaces are handled specially so that they don't need to be materialized as values until the string is demanded.
type stringb
  SDone 
  // Denotes a partially built string with the first part ready
  SStep( str: string, acc: stringb)
  SIndent( acc: stringb )
  SNewline( acc : stringb )
  SSpace( acc : stringb )
  SUnindent( acc : stringb )
  
  lazy fip SBuilderString(a: string, b : stringb) -> 
    match b
      SDone -> SStep(a, SDone)
      // TODO: Optimize so we allocate the right buffer for the strings, and then just do a low level copy of the data
      SStep(s1, acc) -> SStep(a, SStep(s1, acc))
      SIndent(acc) -> SStep(a, SIndent(acc))
      SUnindent(acc) -> SStep(a, SUnindent(acc))
      SNewline(acc) -> SStep(a, SNewline(acc))
      SSpace(acc) -> SStep(a, SSpace(acc))

  // Delays conversion until the string is actually needed
  lazy fip SBuilderAny<a>( a: a, b: stringb, show: (a) -> string) ->
    match b  // TODO: Split strings on newlines?
      SDone -> SStep(show(a), SDone)
      SStep(s1, acc) -> SStep(show(a), SStep(s1, acc))
      SIndent(acc) -> SStep(show(a), SIndent(acc))
      SUnindent(acc) -> SStep(show(a), SUnindent(acc))
      SNewline(acc) -> SStep(show(a), SNewline(acc))
      SSpace(acc) -> SStep(show(a), SSpace(acc))
  
  // Delays the concatenation 
  lazy SBuilderConcat(str : stringb, str2: stringb) ->
    match str
      SDone -> str2
      SIndent(acc) -> SIndent(SBuilderConcat(acc, str2))
      SUnindent(acc) -> SUnindent(SBuilderConcat(acc, str2))
      SNewline(acc) -> SNewline(SBuilderConcat(acc, str2))
      SSpace(acc) -> SSpace(SBuilderConcat(acc, str2))
      SStep(s1, acc) -> SStep(s1, SBuilderConcat(acc, str2))

// Concatenates two string builders with no space between
inline fun builder/(|.|)(a: stringb, b: stringb) : stringb
  SBuilderConcat(a, b)

// Concatenates two string builders with a space between
inline fun builder/(|-|)(a: stringb, b: stringb) : stringb
  SBuilderConcat(a, SSpace(b))

// Concatenates two string builders with a newline between
inline fun builder/(\)(a: stringb, b: stringb) : stringb
  SBuilderConcat(a, SNewline(b))

// Concatenates two string builders with a newline and indented block
inline fun builder/(\-)(a: stringb, b: stringb) : stringb
  SBuilderConcat(a, SIndent(SNewline(b)))

// Concatenates a string and a string builder with no space between
inline fun string/(|.|)(a: string, b: stringb) : stringb
  SBuilderString(a, b)

// Concatenates a string and a string builder with a space between
inline fun stringb/(|-|)(a: string, b: stringb) : stringb
  SBuilderString(a, SSpace(b))

// Concatenates a string and a string builder with a newline between
inline fun stringb/(\)(a: string, b: stringb) : stringb
  SBuilderString(a, SNewline(b))

// Concatenates a string and a string builder with a newline and indented block
inline fun stringb/(\-)(a: string, b: stringb) : stringb
  SBuilderString(a, SIndent(SNewline(b)))

// Concatenates any value and a string builder with no space between
inline fun any/(|.|)(a: a, s: stringb, ?show: (a) -> string) : stringb
  SBuilderAny(a, s, ?show)

// Concatenates any value and a string builder with a space between
inline fun any/(|-|)(a: a, s: stringb, ?show: (a) -> string) : stringb
  SBuilderAny(a, SSpace(s), ?show)

// Concatenates any value and a string builder with a newline between
inline fun any/(\)(a: a, s: stringb, ?show: (a) -> string) : stringb
  SBuilderAny(a, SNewline(s), ?show)

// Concatenates any value and a string builder with a newline and indented block
inline fun any/(\-)(a: a, s: stringb, ?show: (a) -> string) : stringb
  SBuilderAny(a, SIndent(SNewline(s)), ?show)

// Creates an indented block starting and ending with a newline
inline fun indented(s: stringb): stringb
  SBuilderConcat(SIndent(SNewline(s)), SUnindent(SNewline(SDone)))

// Ends a string builder with a string
inline fun string/build(a: string): stringb
  SStep(a, SDone)

// Ends a string builder with a value
inline fun any/build(a: a, ?show: (a) -> string): stringb
  SBuilderAny(a, SDone, ?show)

// Ends a string builder with an empty value
inline fun empty/build(): stringb
  SDone

// Show the string builder as a string
fun stringb/show(s: stringb, indent: int = 0): string
  match s
    SDone -> ""
    SIndent(acc) -> acc.pretend-decreasing.show(indent = indent + 2)
    SNewline(acc) -> "\n" ++ " ".repeat(indent) ++ acc.pretend-decreasing.show(indent = indent)
    SSpace(acc) -> " " ++ acc.pretend-decreasing.show(indent = indent)
    SStep(str, acc) -> str ++ acc.pretend-decreasing.show(indent = indent)
    SUnindent(acc) -> acc.pretend-decreasing.show(indent = max(0, indent - 2))

// Print the string builder to the console
fun stringb/println(s: stringb, indent: int = 0): console ()
  match s
    SDone -> "".println
    SIndent(acc) -> 
      acc.pretend-decreasing.println(indent = indent + 2)
    SNewline(acc) -> 
      "\n".print
      " ".repeat(indent).print
      acc.pretend-decreasing.println(indent = indent)
    SSpace(acc) -> 
      " ".print
      acc.pretend-decreasing.println(indent = indent)
    SStep(str, acc) -> 
      str.print
      acc.pretend-decreasing.println(indent = indent)
    SUnindent(acc) -> 
      acc.pretend-decreasing.println(indent = max(0, indent - 2))

// Print the string builder to the console with no ending newline
fun stringb/print(s: stringb, indent: int = 0): console ()
  match s
    SDone -> "".print
    SIndent(acc) -> 
      acc.pretend-decreasing.print(indent = indent + 2)
    SNewline(acc) ->
      "\n".print
      " ".repeat(indent).print
      acc.pretend-decreasing.print(indent = indent)
    SSpace(acc) ->
      " ".print
      acc.pretend-decreasing.print(indent = indent)
    SStep(str, acc) -> 
      str.print
      acc.pretend-decreasing.print(indent = indent)
    SUnindent(acc) -> 
      acc.pretend-decreasing.print(indent = max(0, indent - 2))