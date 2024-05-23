// https://github.com/ilyasergey/reachability/blob/master/benchmarks/gcfa2/eta.scm
fun do-something()
  10

fun id1(y)
  do-something()
  y

fun main()
  id1(fn(a) a)(True)
  id1(fn(b) b)(False).println