// https://github.com/ilyasergey/reachability/blob/master/benchmarks/kcfa/sat-brute.scm
fun phi(x1: bool)
  fn(x2: bool)
    fn(x3: bool)
      fn(x4: bool)
        fn(x5: bool)
          fn(x6: bool)
            fn(x7: bool)
              val res = (x1 || x2) && (x1 || !x2 || !x3) && (x3 || x4) && (!x4 || x1) && (!x2 || !x3) || (x4 || x2)
              res     
fun try(f: bool -> bool)
  f(True) || f(False)

fun sat-solve7(p)
  try(fn(n1) try(fn(n2) try(fn(n3) try(fn(n4) try(fn(n5) try(fn(n6) try(fn(n7) p(n1)(n2)(n3)(n4)(n5)(n6)(n7))))))))

fun main()
  val res = sat-solve7(phi)
  res.println