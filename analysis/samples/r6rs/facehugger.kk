fun id1(x)
  x

fun f(n)
  if n <= 1 then 1 else n * f(n - 1)

fun g(n)
  if n <= 1 then 1 else n * g(n - 1)

fun main()
  val x = id(f)(3) + id(g)(4)
  println(x)