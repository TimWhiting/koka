
effect ex1
  ctl ex1(i: int): int 

fun analyze-ex1(): int
  trace("Example 1 - exceptions")
  with ctl ex1(a) a
  ex1(1)
fun result-ex1() 1

fun analyze-ex10(): int
  trace("Example 10 - simple")
  with ctl ex1(a) resume(a + 1)
  ex1(0)
fun result-ex10() 1

fun analyze-ex11(): int
  trace("Example 121 - simple cont")
  with ctl ex1(a) resume(a + 1)
  ex1(0) + 1 
fun result-ex11() 2

fun analyze-ex12(): int
  trace("Example 122 - simple cont")
  with ctl ex1(a) resume(a + 1) + 1
  ex1(0)
fun result-ex12() 2

fun analyze-ex13(): int
  trace("Example 123 - simple cont2")
  with ctl ex1(a) resume(a + 1) + 1
  ex1(0) + 1
fun result-ex13() 3

effect ex2
  ctl ex2(a: (int, int)): int

fun analyze-ex2(): int
  trace("Example 20 - nondeterminism")
  with handler
    ctl ex2(a) resume(a.fst) + resume(a.snd)
    return(x: int) x
  ex2((1,2))
fun result-ex2() 3

fun analyze-ex201(): int
  trace("Example 20-1 - nondeterminism")
  with handler
    ctl ex1(a) resume(2) + resume(3)
    return(x: int) x
  ex1(1) + 1
fun result-ex201() 7

fun analyze-ex21(): int
  trace("Example 21 - nondeterminism")
  with handler 
    ctl ex2(a) resume(a.fst) + resume(a.snd)
    return(x: int) x
  ex2((1,2)) + 1
fun result-ex21() 5

fun analyze-ex22(): int
  trace("Example 22 - nondeterminism twice")
  with handler
    ctl ex2(a) resume(a.fst) + resume(a.snd)
    return(x: int) x
  ex2((1,2)) + ex2((1,2))
fun result-ex22() 12

fun analyze-ex23(): int
  trace("Example 23 - nondeterminism twice")
  with handler
    ctl ex1(a) resume(3) + resume(4)
    return(x: int) x
  ex1(1) + ex1(2)
fun result-ex23() 28

effect ex31
  ctl ex31(a: int): int

effect ex32
  ctl ex32(a: int): int

effect ex33
  ctl ex33(a: (int,int)): int


fun analyze-ex3(): int
  trace("Example 3 nested effects")
  with ctl ex31(z) resume(z) + 1
  with ctl ex32(y) resume(ex31(y))
  ex32(1)
fun result-ex3() 2

fun analyze-ex30(): int
  trace("Example 30 nested effects")
  with ctl ex31(z) resume(z) + 1
  with ctl ex32(y) resume(ex31(y))
  ex31(1)
fun result-ex30() 2

fun analyze-ex31(): int
  trace("Example 31 - mixed effects op in handler after resume")
  with ctl ex31(z) resume(z) + 1
  with ctl ex33(a) resume(a.fst) + ex31(a.snd) // op after resume
  1 + ex33((1,2))
fun result-ex31() 5

fun analyze-ex32(): int
  trace("Example 32 - mixed effects op in handler before resume")
  with ctl ex31(z) resume(z) + 1
  with ctl ex33(a) ex31(a.fst) + resume(a.snd) // op before resume
  1 + ex33((1,2))
fun result-ex32() 5

fun analyze-ex33(): int
  trace("Example 33 - mixed effects under both handlers - inner first")
  with ctl ex31(z) resume(z) + 1
  with ctl ex33(a) resume(a.fst) 
  1 + ex33((1,2)) + ex31(0) // inner first
fun result-ex33() 3

fun analyze-ex34(): int
  trace("Example 34 - mixed effects under both handlers - outer first")
  with ctl ex31(z) resume(z) + 1
  with ctl ex33(a) resume(a.fst) 
  ex31(0) + 1 + ex33((1,2)) // outer first
fun result-ex34() 3


effect ex41
  ctl ex41(a: int): int

effect ex42
  ctl ex42(a: int): int

effect ex43
  ctl ex43(a: (int,int)): int

fun analyze-ex4(): int
  trace("Example 4 nested effects (tail resume outer)")
  with ctl ex41(z) resume(z + 1)
  with ctl ex42(y) resume(ex41(y))
  ex42(1)
fun result-ex4() 2

fun analyze-ex41(): int
  trace("Example 41 - mixed effects op in handler after resume (tail resume outer)")
  with ctl ex41(z) resume(z + 1)
  with ctl ex43(a) resume(a.fst) + ex41(a.snd) // op after resume
  1 + ex43((1, 2))
fun result-ex41() 5

fun analyze-ex42(): int
  trace("Example 42 - mixed effects op in handler before resume (tail resume outer)")
  with ctl ex41(z) resume(z + 1)
  with ctl ex43(a) ex41(a.fst) + resume(a.snd) // op before resume
  1 + ex43((1, 2))
fun result-ex42() 5

fun analyze-ex43(): int
  trace("Example 43 - mixed effects under both handlers - inner first (tail resume outer)")
  with ctl ex41(z) resume(z + 1)
  with ctl ex43(a) resume(a.fst)
  1 + ex43((1, 2)) + ex41(0) // inner first
fun result-ex43() 3

fun analyze-ex44(): int
  trace("Example 44 - mixed effects under both handlers - outer first (tail resume outer)")
  with ctl ex41(z) resume(z + 1)
  with ctl ex43(a) resume(a.fst)
  ex41(0) + 1 + ex43((1, 2)) // outer first
fun result-ex44() 3

effect ex51
  ctl ex51(a: int): int

effect ex52
  ctl ex52(a: (int,int)): int

effect ex53
  ctl ex53(a: int): int


fun analyze-ex5(): int
  trace("Example 50 - whole lot of effects")
  with ctl ex51(z) resume(z) + 1
  with ctl ex52(a) resume(a.fst) + ex51(a.snd)
  with ctl ex53(b) resume(b) + b
  1 + ex52((1, 2)) + ex53(1)
fun result-ex5() 7

fun analyze-ex51(): int
  trace("Example 51 - whole lot of effects inner first")
  with ctl ex51(z) resume(z) + 1
  with ctl ex52(a) resume(a.fst) + ex51(a.snd)
  with ctl ex53(b) resume(b) + b
  ex53(1) + ex52((1, 2)) + 1
fun result-ex51() 7

fun analyze-ex52(): int
  trace("Example 52 - whole lot of effects two outer calls")
  with ctl ex51(z) resume(z + 1)
  with ctl ex52(a) resume(a.fst) + ex51(a.snd)
  with ctl ex53(b) resume(b) + ex51(b)
  ex52((1, 2)) + ex53(1)
fun result-ex52() 7


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

fun analyze-sum1()
  trace("Example x_suma")
  with ctl it(a) a + resume(a)
  iter(1)
fun result-sum1() 1

fun analyze-sum1x()
  trace("Example x_suma")
  with handler
    return(x) 0
    ctl it(a) a + resume(a)
  iter(1)
fun result-sum1x() 1

fun analyze-sum2()
  trace("Example x_sum2a")
  with ctl it(a) a + resume(a)
  iter(2)
fun result-sum2() 3

fun analyze-sum1b()
  trace("Example x_sum1b")
  with ctl it(a) resume(a) + a
  iter(1)
fun result-sum1b() 1

fun analyze-sum2b()
  trace("Example x_sum2b")
  with ctl it(a) resume(a) + a
  iter(2)
fun result-sum2b() 3

fun analyze-sum1c()
  trace("Example x_sumc")
  with ctl it(a) a + resume(a)
  iterxx(1)
fun result-sum1c() 1

fun analyze-sum2c()
  trace("Example x_sum2c")
  with ctl it(a) a + resume(a)
  iterxx(2)
fun result-sum2c() 3

fun analyze-sum1d()
  trace("Example x_sum1d")
  with ctl it(a) resume(a) + a
  iterxx(1)
fun result-sum1d() 1

fun analyze-sum2d()
  trace("Example x_sum2d")
  with ctl it(a) resume(a) + a
  iterxx(2)
fun result-sum2d() 3

effect get
  ctl get(i: int): int
effect set
  ctl set(i: int): ()

fun countdown(_)
  val i = get(0)
  if i == 0 then 0 else 
    set(i - 1)
    countdown(0)

fun analyze-get-set(): div int
  trace("Example get/set")
  val x = 2
  with ctl get(_) resume(x)
  with ctl set(a)
    with override ctl get(b) resume(b)
    resume(())
  countdown(0)
fun result-get-set() 0
