type hello
  Hello

type other<t>
  Int(i: int, t: t)
  Bool(b: bool, t: t)
  Char(c: char, b: bool, t: t)
  Other(f: () -> int)
  Other2(o1: other<t>, o2: other<t>)

fun main() 
  Hello.show.println
  Int(0, "").show(show).println
  Other(fn () 0).show(fn(s: string) show(s)).println
  val x = Other2(Int(0, ""), Int(1, "hi"))
  val y = Other2(Int(1, ""), Int(2, "hi"))
  (==)(x,y,(==)).show.println
  (==)(x,x,(==)).show.println
  x.show(show).println
