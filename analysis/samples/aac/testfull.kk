fun main()
  val f = fn(y) y
  val g = fn(z) z
  fun do(x)
    if x then f(1) else g(2)
  do(True)