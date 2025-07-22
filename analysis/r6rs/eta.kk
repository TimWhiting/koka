// https://github.com/ilyasergey/reachability/blob/master/benchmarks/gcfa2/eta.scm
fun do-something()
  10

fun id1(y)
  do-something()
  y

fun analyze()
  val a = id1(fn(a) a)(True)
  id1(fn(b) b)(False)

fun main()
  val a = id1(fn(a) a)(True)
  val b = id1(fn(b) b)(False)
  a.println
  b.println