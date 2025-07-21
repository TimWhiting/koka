
effect ex1
  ctl ex1(i: int): int 

fun example-e1(): int
  trace("Example 1 - exceptions")
  with final ctl ex1(a) a
  ex1(1)

fun example-e10(): int
  trace("Example 10 - simple")
  with ctl ex1(a) resume(a + 1)
  ex1(0)

fun example-e11(): int
  trace("Example 121 - simple cont")
  with ctl ex1(a) resume(a + 1)
  ex1(0) + 1 

fun example-e12(): int
  trace("Example 122 - simple cont")
  with ctl ex1(a) resume(a + 1) + 1
  ex1(0)

fun example-e13(): int
  trace("Example 123 - simple cont2")
  with ctl ex1(a) resume(a + 1) + 1
  ex1(0) + 1

effect ex2
  ctl ex2(a: (int, int)): int

fun example-e2(): int
  trace("Example 20 - nondeterminism")
  with handler
    ctl ex2(a) resume(a.fst) + resume(a.snd)
    return(x: int) x
  ex2((1,2))

fun example-ex201(): int
  trace("Example 20-1 - nondeterminism")
  with handler
    ctl ex1(a) resume(2) + resume(3)
    return(x: int) x
  ex1(1) + 1

fun example-ex21(): int
  trace("Example 21 - nondeterminism")
  with handler 
    ctl ex2(a) resume(a.fst) + resume(a.snd)
    return(x: int) x
  ex2((1,2)) + 1

fun example-ex22(): int
  trace("Example 22 - nondeterminism twice")
  with handler
    ctl ex2(a) resume(a.fst) + resume(a.snd)
    return(x: int) x
  ex2((1,2)) + ex2((1,2))

fun example-ex23(): int
  trace("Example 23 - nondeterminism twice")
  with handler
    ctl ex1(a) resume(3) + resume(4)
    return(x: int) x
  ex1(1) + ex1(2)


effect ex31
  ctl ex31(a: int): int

effect ex32
  ctl ex32(a: int): int

effect ex33
  ctl ex33(a: (int,int)): int


fun example-ex3(): int
  trace("Example 3 nested effects")
  with ctl ex31(z) resume(z) + 1
  with ctl ex32(y) resume(ex31(y))
  ex32(1)

fun example-ex30(): int
  trace("Example 30 nested effects")
  with ctl ex31(z) resume(z) + 1
  with ctl ex32(y) resume(ex31(y))
  ex31(1)

fun example-ex31(): int
  trace("Example 31 - mixed effects op in handler after resume")
  with ctl ex31(z) resume(z) + 1
  with ctl ex33(a) resume(a.fst) + ex31(a.snd) // op after resume
  1 + ex33((1,2))

fun example-ex32(): int
  trace("Example 32 - mixed effects op in handler before resume")
  with ctl ex31(z) resume(z) + 1
  with ctl ex33(a) ex31(a.fst) + resume(a.snd) // op before resume
  1 + ex33((1,2))

fun example-ex33(): int
  trace("Example 33 - mixed effects under both handlers - inner first")
  with ctl ex31(z) resume(z) + 1
  with ctl ex33(a) resume(a.fst) 
  1 + ex33((1,2)) + ex31(0) // inner first

fun example-ex34(): int
  trace("Example 34 - mixed effects under both handlers - outer first")
  with ctl ex31(z) resume(z) + 1
  with ctl ex33(a) resume(a.fst) 
  ex31(0) + 1 + ex33((1,2)) // outer first


effect ex41
  ctl ex41(a: int): int

effect ex42
  ctl ex42(a: int): int

effect ex43
  ctl ex43(a: (int,int)): int

fun example-ex4(): int
  trace("Example 4 nested effects (tail resume outer)")
  with ctl ex41(z) resume(z + 1)
  with ctl ex42(y) resume(ex41(y))
  ex42(1)

fun example-ex41(): int
  trace("Example 41 - mixed effects op in handler after resume (tail resume outer)")
  with ctl ex41(z) resume(z + 1)
  with ctl ex43(a) resume(a.fst) + ex41(a.snd) // op after resume
  1 + ex43((1, 2))

fun example-ex42(): int
  trace("Example 42 - mixed effects op in handler before resume (tail resume outer)")
  with ctl ex41(z) resume(z + 1)
  with ctl ex43(a) ex41(a.fst) + resume(a.snd) // op before resume
  1 + ex43((1, 2))

fun example-ex43(): int
  trace("Example 43 - mixed effects under both handlers - inner first (tail resume outer)")
  with ctl ex41(z) resume(z + 1)
  with ctl ex43(a) resume(a.fst)
  1 + ex43((1, 2)) + ex41(0) // inner first

fun example-ex44(): int
  trace("Example 44 - mixed effects under both handlers - outer first (tail resume outer)")
  with ctl ex41(z) resume(z + 1)
  with ctl ex43(a) resume(a.fst)
  ex41(0) + 1 + ex43((1, 2)) // outer first

effect ex51
  ctl ex51(a: int): int

effect ex52
  ctl ex52(a: (int,int)): int

effect ex53
  ctl ex53(a: int): int


fun example-ex5(): int
  trace("Example 50 - whole lot of effects")
  with ctl ex51(z) resume(z) + 1
  with ctl ex52(a) resume(a.fst) + ex51(a.snd)
  with ctl ex53(b) resume(b) + b
  1 + ex52((1, 2)) + ex53(1)

fun example-ex51(): int
  trace("Example 51 - whole lot of effects inner first")
  with ctl ex51(z) resume(z) + 1
  with ctl ex52(a) resume(a.fst) + ex51(a.snd)
  with ctl ex53(b) resume(b) + b
  ex53(1) + ex52((1, 2)) + 1

fun example-ex52(): int
  trace("Example 52 - whole lot of effects two outer calls")
  with ctl ex51(z) resume(z) + 1
  with ctl ex52(a) resume(a.fst) + ex51(a.snd)
  with ctl ex53(b) resume(b) + b
  ex52((1, 2)) + ex53(1)

effect get
  ctl get(i: int): int
effect set
  ctl set(i: int): ()

fun example-get-set(): div int
  trace("Example get/set")
  fun countdown(_)
    val i = get(0)
    if i == 0 then 0 else 
      set(i - 1)
      countdown(0)
  val x = 2
  with ctl get(_) resume(x)
  with ctl set(a)
    with override ctl get(b) resume(b)
    resume(())
  countdown(0)

effect iter 
  ctl it(i: int): int

fun iterxx(n: int): <div,iter> int
  if n == 0 then 0 
  else 
    val n0 = iterxx(n - 1)
    it(n)
    n0

fun iterx(n: int): <div,iter> int
  if n == 0 then -1
  else 
    it(n)
    iterx(n - 1)

fun iter(n: int): <div,iter> int
  if n == 0 then 0
  else 
    it(n)
    iter(n - 1)

fun example-sum1()
  trace("Example x_suma")
  with ctl it(a) a + resume(a)
  iter(1)

fun example-sum1x()
  trace("Example x_suma")
  with handler
    return(x) 0
    ctl it(a) a + resume(a)
  iter(1)

fun example-sum2()
  trace("Example x_sum2a")
  with ctl it(a) a + resume(a)
  iter(2)

fun example-sum1b()
  trace("Example x_sum1b")
  with ctl it(a) resume(a) + a
  iter(1)

fun example-sum2b()
  trace("Example x_sum2b")
  with ctl it(a) resume(a) + a
  iter(2)

fun example-sum1c()
  trace("Example x_sumc")
  with ctl it(a) a + resume(a)
  iterxx(1)

fun example-sum2c()
  trace("Example x_sum2c")
  with ctl it(a) a + resume(a)
  iterxx(2)

fun example-sum1d()
  trace("Example x_sum1d")
  with ctl it(a) resume(a) + a
  iterxx(1)

fun example-sum2d()
  trace("Example x_sum2d")
  with ctl it(a) resume(a) + a
  iterxx(2)

fun analyze()
  trace-show(example-e1() == 1)
  // trace-show(example-e10() == 1)
  // trace-show(example-e11() == 2)
  // trace-show(example-e12() == 2)
  // trace-show(example-e13() == 3)
  // trace-show(example-e2() == 3)
  // trace-show(example-ex201() == 7)
  // trace-show(example-ex21() == 5)
  // trace-show(example-ex22() == 12)
  // trace-show(example-ex23() == 28)
  // trace-show(example-ex3() == 2)
  // trace-show(example-ex30() == 2)
  // trace-show(example-ex31() == 5)
  // trace-show(example-ex32() == 5)
  // trace-show(example-ex33() == 3)
  // trace-show(example-ex34() == 3)
  // trace-show(example-ex4() == 2)
  // trace-show(example-ex41() == 5)
  // trace-show(example-ex42() == 5)
  // trace-show(example-ex43() == 3)
  // trace-show(example-ex44() == 3)
  // trace-show(example-ex5() == 7)
  // trace-show(example-ex51() == 7)
  // trace-show(example-ex52() == 7)
  // trace-show(example-sum1() == 1)
  // trace-show(example-sum1x() == 1)
  // trace-show(example-sum2() == 3)
  // trace-show(example-sum1b() == 1)
  // trace-show(example-sum2b() == 3)
  // trace-show(example-sum1c() == 1)
  // trace-show(example-sum2c() == 3)
  // trace-show(example-sum1d() == 1)
  // trace-show(example-sum2d() == 3)
  // trace-show(example-get-set() == 0)
