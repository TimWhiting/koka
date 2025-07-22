fun main()
  val f = fn(y) y
  val g = fn(z) z
  val do = fn(k) if k then f(1) else g(2)
  do(True)