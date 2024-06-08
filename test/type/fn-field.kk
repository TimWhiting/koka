struct fn-field
  xrun: (string) -> io ()

fun main()
  val f = Fn-field(fn(s) println(s))
  f.xrun("Hello, World!")
