import samples/basic/debug
// type hello
//   Hello

// fun debug(h: hello): string
//   "Hello"
// fun debug(o: other): string
//   match o
//     Int(i) -> "Int: " ++ i.debug
//     Bool(b) -> "Bool: " ++ b.debug
//     Char(c) -> "Char: " ++ c.debug
//     Other(f) -> "Other: "

type other
  Int(i: int)
  Bool(b: bool)
  Char(c: char, b: bool)
  Other(f: () -> int)

fun main() 
  // Hello.debug.println
  Char('c', True).debug.println
  // 0.show.println