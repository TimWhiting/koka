fun id1(x) x
fun blur(y) y
fun lp(a: bool, n)
  if n <= 1 then id1(a)
  else
    val r = blur(id1)(True)
    val s = blur(id1)(False)
    !blur(lp)(s, n - 1)

fun main()
  val res = lp(False, 2)
  res.println

fun analyze()
  lp(False, 2)