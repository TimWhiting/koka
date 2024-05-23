fun id1(x) x
fun blur(y) y
fun lp(a: bool, n)
  if n <= 1 then id1(a)
  else
    val r = blur(id)(True)
    val s = blur(id)(False)
    !blur(lp)(s, n - 1)

fun main()
  lp(False, 2).println
