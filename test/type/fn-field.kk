struct fn-field
  xrun: (string) -> io ()
  funx: (?name: string) -> io ()
  noarg: () -> io ()

fun main()
  val f = Fn-field(fn(s) println(s), fn(?name) println("Hello, " ++ name), fn() println("No arg"))
  f.xrun("Hello, World!")
  val name = "John"
  f.funx()
  f.call/noarg()
