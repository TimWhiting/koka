// Improvement from OCFA to 1CFA to 2CFA

// TODO: Improve visualization of environment & callers
fun lp(a: bool, n)
  if n <= 1 then id(a)
  else
    val r = id(id)(True)
    val s = id(id)(False)
    !id(lp)(s, n - 1)

fun test1()
  val res = lp(False, 2)
  res.println





// Sample k-cfa vs m-cfa
// Also higher order environments leaving some details unspecified
fun phi(x1: bool, x2: bool, x3: bool, x4: bool)
  val res = (x1 || !x2 || !x3) && (!x2 || !x3) && (x4 || x2)
  res

fun try(f: (bool) -> bool)
  trace("Trying")
  f(True) || f(False)

fun sat-solve4(p)
  try(fn(n1) try(fn(n2) try(fn(n3) try(fn(n4) p(n1, n2, n3, n4)))))

fun test2()
  val res = sat-solve4(phi)
  res.println

