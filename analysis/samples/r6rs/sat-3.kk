fun phi(x1: bool, x2: bool, x3: bool, x4: bool, x5: bool, x6: bool, x7: bool)
  val res = (x1 || x2) && (x1 || !x2 || !x3) && (x3 || x4) && (!x4 || x1) && (!x2 || !x3) && (x4 || x2)
  res

fun try(f: bool -> console bool)
  println("trying")
  f(True) || f(False)

fun sat-solve7(p)
  try(fn(n1) try(fn(n2) try(fn(n3) try(fn(n4) try(fn(n5) try(fn(n6) try(fn(n7) p(n1, n2, n3, n4, n5, n6, n7))))))))

fun analyze()
  sat-solve7(phi)

fun main()
  val res = sat-solve7(phi)
  res.println
