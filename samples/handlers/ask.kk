effect fun ask() : string

fun hello()
  val name = ask()
  println("Hello " ++ name ++ ", " ++ ask())  // "Hello <ask>, <ask>"


fun main()
  with fun ask() ""
  hello()