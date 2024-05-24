fun fact(n)
  if n == 0 then 1 else n * fact(n - 1)

fun main()
  val res = fact(3)
  res.println