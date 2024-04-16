fun id2(x)
  x

fun f(n)
  if n <= 1 then 1 else n * f(n - 1)

fun g(n)
  if n <= 1 then 1 else n * g(n - 1)

fun main()
  val x = id2(f)(3)
  val y = id2(g)(4)
  val z = x + y
  println(z.show)