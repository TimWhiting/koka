fun h(b)
  fun g(z) z
  fun f(k)
    if b then k(1) else k(2)
  val y = f(fn(x) x)
  g(y)

fun main()
  val x = h(True)
  val y = h(False)
  y.println