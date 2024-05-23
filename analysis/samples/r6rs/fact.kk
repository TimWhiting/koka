fun fact(n)
  if n == 0 then 1 else n * fact(n - 1)

fun main()
  fact(3).println