fun phi(x1: bool, x2: bool, x3: bool, x4: bool)
  (x1 || !x2 || !x3) && (!x2 || !x3) && (x4 || x2)

fun try(f: (bool) -> bool)
  f(True) || f(False)

fun sat-solve4(p)
  try(fn(n1) try(fn(n2) try(fn(n3) try(fn(n4) p(n1, n2, n3, n4)))))

fun main()
  sat-solve4(phi).println