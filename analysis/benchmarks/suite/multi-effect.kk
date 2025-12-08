module multi-effect

effect ex51
  ctl ex51(a: int): int

effect ex52
  ctl ex52(a: (int,int)): int

effect ex53
  ctl ex53(a: int): int


fun analyze-multi-simple(): int
  trace("Example 50 - whole lot of effects")
  with ctl ex51(z) resume(z) + 1
  with ctl ex52(a) resume(a.fst) + ex51(a.snd)
  with ctl ex53(b) resume(b) + b
  1 + ex52((1, 2)) + ex53(1)
fun result-multi-simple() 7

fun analyze-multi-inner-first(): int
  trace("Example 51 - whole lot of effects inner first")
  with ctl ex51(z) resume(z) + 1
  with ctl ex52(a) resume(a.fst) + ex51(a.snd)
  with ctl ex53(b) resume(b) + b
  ex53(1) + ex52((1, 2)) + 1
fun result-multi-inner-first() 7

fun analyze-multi-two-outer(): int
  trace("Example 52 - whole lot of effects two outer calls")
  with ctl ex51(z) resume(z + 1)
  with ctl ex52(a) resume(a.fst) + ex51(a.snd)
  with ctl ex53(b) resume(b) + ex51(b)
  ex52((1, 2)) + ex53(1)
fun result-multi-two-outer() 7

fun test-multi-simple()
  val result = analyze-multi-simple()
  if result == result-multi-simple() then println("✓ test-multi-simple passed")
  else println("✗ test-multi-simple FAILED: expected " ++ result-multi-simple().show ++ ", got " ++ result.show)

fun test-multi-inner-first()
  val result = analyze-multi-inner-first()
  if result == result-multi-inner-first() then println("✓ test-multi-inner-first passed")
  else println("✗ test-multi-inner-first FAILED: expected " ++ result-multi-inner-first().show ++ ", got " ++ result.show)

fun test-multi-two-outer()
  val result = analyze-multi-two-outer()
  if result == result-multi-two-outer() then println("✓ test-multi-two-outer passed")
  else println("✗ test-multi-two-outer FAILED: expected " ++ result-multi-two-outer().show ++ ", got " ++ result.show)

fun main()
  println("Running multi-effect tests...")
  test-multi-simple()
  test-multi-inner-first()
  test-multi-two-outer()
  println("multi-effect tests complete")

