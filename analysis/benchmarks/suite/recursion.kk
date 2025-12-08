module recursion

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

fun analyze-iter-sum(): div int
  trace("Example x_suma")
  with ctl it(a) a + resume(a)
  iter(1)
fun result-iter-sum() 1

fun analyze-iter-sum-handler(): div int
  trace("Example x_suma")
  with handler
    return(x) 0
    ctl it(a) a + resume(a)
  iter(1)
fun result-iter-sum-handler() 1

fun analyze-iter-sum-two(): div int
  trace("Example x_sum2a")
  with ctl it(a) a + resume(a)
  iter(2)
fun result-iter-sum-two() 3

fun analyze-iter-sum-b(): div int
  trace("Example x_sum1b")
  with ctl it(a) resume(a) + a
  iter(1)
fun result-iter-sum-b() 1

fun analyze-iter-sum-two-b(): div int
  trace("Example x_sum2b")
  with ctl it(a) resume(a) + a
  iter(2)
fun result-iter-sum-two-b() 3

fun analyze-iter-sum-c(): div int
  trace("Example x_sumc")
  with ctl it(a) a + resume(a)
  iterxx(1)
fun result-iter-sum-c() 1

fun analyze-iter-sum-two-c(): div int
  trace("Example x_sum2c")
  with ctl it(a) a + resume(a)
  iterxx(2)
fun result-iter-sum-two-c() 3

fun analyze-iter-sum-d(): div int
  trace("Example x_sum1d")
  with ctl it(a) resume(a) + a
  iterxx(1)
fun result-iter-sum-d() 1

fun analyze-iter-sum-two-d(): div int
  trace("Example x_sum2d")
  with ctl it(a) resume(a) + a
  iterxx(2)
fun result-iter-sum-two-d() 3

fun test-iter-sum()
  val result = analyze-iter-sum()
  if result == result-iter-sum() then println("✓ test-iter-sum passed")
  else println("✗ test-iter-sum FAILED: expected " ++ result-iter-sum().show ++ ", got " ++ result.show)

fun test-iter-sum-handler()
  val result = analyze-iter-sum-handler()
  if result == result-iter-sum-handler() then println("✓ test-iter-sum-handler passed")
  else println("✗ test-iter-sum-handler FAILED: expected " ++ result-iter-sum-handler().show ++ ", got " ++ result.show)

fun test-iter-sum-two()
  val result = analyze-iter-sum-two()
  if result == result-iter-sum-two() then println("✓ test-iter-sum-two passed")
  else println("✗ test-iter-sum-two FAILED: expected " ++ result-iter-sum-two().show ++ ", got " ++ result.show)

fun test-iter-sum-b()
  val result = analyze-iter-sum-b()
  if result == result-iter-sum-b() then println("✓ test-iter-sum-b passed")
  else println("✗ test-iter-sum-b FAILED: expected " ++ result-iter-sum-b().show ++ ", got " ++ result.show)

fun test-iter-sum-two-b()
  val result = analyze-iter-sum-two-b()
  if result == result-iter-sum-two-b() then println("✓ test-iter-sum-two-b passed")
  else println("✗ test-iter-sum-two-b FAILED: expected " ++ result-iter-sum-two-b().show ++ ", got " ++ result.show)

fun test-iter-sum-c()
  val result = analyze-iter-sum-c()
  if result == result-iter-sum-c() then println("✓ test-iter-sum-c passed")
  else println("✗ test-iter-sum-c FAILED: expected " ++ result-iter-sum-c().show ++ ", got " ++ result.show)

fun test-iter-sum-two-c()
  val result = analyze-iter-sum-two-c()
  if result == result-iter-sum-two-c() then println("✓ test-iter-sum-two-c passed")
  else println("✗ test-iter-sum-two-c FAILED: expected " ++ result-iter-sum-two-c().show ++ ", got " ++ result.show)

fun test-iter-sum-d()
  val result = analyze-iter-sum-d()
  if result == result-iter-sum-d() then println("✓ test-iter-sum-d passed")
  else println("✗ test-iter-sum-d FAILED: expected " ++ result-iter-sum-d().show ++ ", got " ++ result.show)

fun test-iter-sum-two-d()
  val result = analyze-iter-sum-two-d()
  if result == result-iter-sum-two-d() then println("✓ test-iter-sum-two-d passed")
  else println("✗ test-iter-sum-two-d FAILED: expected " ++ result-iter-sum-two-d().show ++ ", got " ++ result.show)

fun main()
  println("Running recursion tests...")
  test-iter-sum()
  test-iter-sum-handler()
  test-iter-sum-two()
  test-iter-sum-b()
  test-iter-sum-two-b()
  test-iter-sum-c()
  test-iter-sum-two-c()
  test-iter-sum-d()
  test-iter-sum-two-d()
  println("recursion tests complete")

