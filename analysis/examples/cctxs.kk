fun main()
  val h = ctx hole 
  val r1 = h ++ ctx Cons(10, hole)
  val r2 = r1 ++ ctx Cons(20, Cons(30, hole))
  println(r1 ++. Nil)
  println(r2 ++. Nil)
  r2 ++. Nil

fun analyze-main()
  main()
fun result-main()
  [10, 20, 30]