fun id1(x) x
fun blur(y) y
fun lp(a: bool, n)
  if n <= 1 then id1(a)
  else
    // val r = blur(id1)(True)
    val s = blur(id1)(False)
    // !blur(lp)(s, n - 1)
    blur(lp)(s, n)

fun main()
  val res = lp(False, 2)
  res.println

fun analyze()
  fact(10)

fun fact(n)
  if n == 0 then 1
  else n * fact(n - 1)