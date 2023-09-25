effect printer
  val width: int

fun main()
  with val width = 10
  pprint("Hello World!")
  do-something()

fun do-something()
  with override val width = width - 5
  pprint("Hello World!")

fun pprint(s: string)
  println(" ".repeat(width) ++ s)

