fun lp1(i, x)
  if i == 0 then x
  else
    fun lp2(j, f, y)
      if j == 0 then lp1(i - 1, y)
      else lp2(j - 1, f, f(y))
    lp2(10, fn(n) n + i, x)

fun analyze()
  lp1(10, 0)
  

fun main()
  val res = lp1(10, 0)
  res.println