module nested

// --- Non-tail resumption effects ---
effect ex31
  ctl ex31(a: int): int

effect ex32
  ctl ex32(a: int): int

effect ex33
  ctl ex33(a: (int,int)): int

// --- Tail resumption effects ---
effect ex41
  ctl ex41(a: int): int

effect ex42
  ctl ex42(a: int): int

effect ex43
  ctl ex43(a: (int,int)): int

// --- New effects for extended coverage ---
effect ex51
  ctl ex51(a: int): int

effect ex52
  ctl ex52(a: int): int

// ----------------------------------------------------------------------------
// Non-tail resumption examples (Context capturing)
// ----------------------------------------------------------------------------

fun analyze-nested-simple(): int
  trace("Example 3 nested effects")
  with ctl ex31(z) resume(z) + 1
  with ctl ex32(y) resume(ex31(y))
  ex32(1)
fun result-nested-simple() 2

fun analyze-nested-simple-two(): int
  trace("Example 30 nested effects")
  with ctl ex31(z) resume(z) + 1
  with ctl ex32(y) resume(ex31(y))
  ex31(1)
fun result-nested-simple-two() 2

fun analyze-nested-op-after(): int
  trace("Example 31 - mixed effects op in handler after resume")
  with ctl ex31(z) resume(z) + 1
  with ctl ex33(a) resume(a.fst) + ex31(a.snd) // op after resume
  1 + ex33((1,2))
fun result-nested-op-after() 5

fun analyze-nested-op-before(): int
  trace("Example 32 - mixed effects op in handler before resume")
  with ctl ex31(z) resume(z) + 1
  with ctl ex33(a) ex31(a.fst) + resume(a.snd) // op before resume
  1 + ex33((1,2))
fun result-nested-op-before() 5

fun analyze-nested-inner-first(): int
  trace("Example 33 - mixed effects under both handlers - inner first")
  with ctl ex31(z) resume(z) + 1
  with ctl ex33(a) resume(a.fst) 
  1 + ex33((1,2)) + ex31(0) // inner first
fun result-nested-inner-first() 3

fun analyze-nested-outer-first(): int
  trace("Example 34 - mixed effects under both handlers - outer first")
  with ctl ex31(z) resume(z) + 1
  with ctl ex33(a) resume(a.fst) 
  ex31(0) + 1 + ex33((1,2)) // outer first
fun result-nested-outer-first() 3

// ----------------------------------------------------------------------------
// Tail resumption examples (Optimization potential)
// ----------------------------------------------------------------------------

fun analyze-nested-tail-simple(): int
  trace("Example 4 nested effects (tail resume outer)")
  with ctl ex41(z) resume(z + 1)
  with ctl ex42(y) resume(ex41(y))
  ex42(1)
fun result-nested-tail-simple() 2

fun analyze-nested-tail-op-after(): int
  trace("Example 41 - mixed effects op in handler after resume (tail resume outer)")
  with ctl ex41(z) resume(z + 1)
  with ctl ex43(a) resume(a.fst) + ex41(a.snd) // op after resume
  1 + ex43((1, 2))
fun result-nested-tail-op-after() 5

fun analyze-nested-tail-op-before(): int
  trace("Example 42 - mixed effects op in handler before resume (tail resume outer)")
  with ctl ex41(z) resume(z + 1)
  with ctl ex43(a) ex41(a.fst) + resume(a.snd) // op before resume
  1 + ex43((1, 2))
fun result-nested-tail-op-before() 5

fun analyze-nested-tail-inner-first(): int
  trace("Example 43 - mixed effects under both handlers - inner first (tail resume outer)")
  with ctl ex41(z) resume(z + 1)
  with ctl ex43(a) resume(a.fst)
  1 + ex43((1, 2)) + ex41(0) // inner first
fun result-nested-tail-inner-first() 3

fun analyze-nested-tail-outer-first(): int
  trace("Example 44 - mixed effects under both handlers - outer first (tail resume outer)")
  with ctl ex41(z) resume(z + 1)
  with ctl ex43(a) resume(a.fst)
  ex41(0) + 1 + ex43((1, 2)) // outer first
fun result-nested-tail-outer-first() 3

// Extended coverage: 3-level deep nesting
fun analyze-nested-three-levels(): int
  trace("Example 50 - three levels")
  with ctl ex31(x) resume(x + 10)
  with ctl ex32(x) resume(ex31(x) * 2)
  with ctl ex33(a) resume(ex32(a.fst) + a.snd)
  ex33((1, 5))
fun result-nested-three-levels() 27 // ex31(1) = 1 + 10 = 11, ex32(1) = 11 * 2 = 22, ex33((1,5)) = 22 + 5 = 27



// Extended coverage: Exception-like (no resume) in middle handler
fun analyze-nested-absorb(): int
  trace("Example 51 - absorb effect")
  with ctl ex31(x) resume(x)
  with ctl ex32(x) 100 // Absorb: doesn't resume
  with ctl ex33(a) resume(a.fst) + ex32(a.snd) // Calls the absorbing handler
  ex33((1, 2))
fun result-nested-absorb() 100 // ex33((1,2)): resume(1) = 1, ex32(2) = 100 (no resume), result discarded in handler
// The handler for ex33 computes resume(1) + ex32(2), but since ex32 doesn't resume,
// it returns 100 directly and that's the final result from the handler




fun test-nested-simple()
  val result = analyze-nested-simple()
  if result == result-nested-simple() then println("✓ test-nested-simple passed")
  else println("✗ test-nested-simple FAILED: expected " ++ result-nested-simple().show ++ ", got " ++ result.show)

fun test-nested-simple-two()
  val result = analyze-nested-simple-two()
  if result == result-nested-simple-two() then println("✓ test-nested-simple-two passed")
  else println("✗ test-nested-simple-two FAILED: expected " ++ result-nested-simple-two().show ++ ", got " ++ result.show)

fun test-nested-op-after()
  val result = analyze-nested-op-after()
  if result == result-nested-op-after() then println("✓ test-nested-op-after passed")
  else println("✗ test-nested-op-after FAILED: expected " ++ result-nested-op-after().show ++ ", got " ++ result.show)

fun test-nested-op-before()
  val result = analyze-nested-op-before()
  if result == result-nested-op-before() then println("✓ test-nested-op-before passed")
  else println("✗ test-nested-op-before FAILED: expected " ++ result-nested-op-before().show ++ ", got " ++ result.show)

fun test-nested-inner-first()
  val result = analyze-nested-inner-first()
  if result == result-nested-inner-first() then println("✓ test-nested-inner-first passed")
  else println("✗ test-nested-inner-first FAILED: expected " ++ result-nested-inner-first().show ++ ", got " ++ result.show)

fun test-nested-outer-first()
  val result = analyze-nested-outer-first()
  if result == result-nested-outer-first() then println("✓ test-nested-outer-first passed")
  else println("✗ test-nested-outer-first FAILED: expected " ++ result-nested-outer-first().show ++ ", got " ++ result.show)

fun test-nested-tail-simple()
  val result = analyze-nested-tail-simple()
  if result == result-nested-tail-simple() then println("✓ test-nested-tail-simple passed")
  else println("✗ test-nested-tail-simple FAILED: expected " ++ result-nested-tail-simple().show ++ ", got " ++ result.show)

fun test-nested-tail-op-after()
  val result = analyze-nested-tail-op-after()
  if result == result-nested-tail-op-after() then println("✓ test-nested-tail-op-after passed")
  else println("✗ test-nested-tail-op-after FAILED: expected " ++ result-nested-tail-op-after().show ++ ", got " ++ result.show)

fun test-nested-tail-op-before()
  val result = analyze-nested-tail-op-before()
  if result == result-nested-tail-op-before() then println("✓ test-nested-tail-op-before passed")
  else println("✗ test-nested-tail-op-before FAILED: expected " ++ result-nested-tail-op-before().show ++ ", got " ++ result.show)

fun test-nested-tail-inner-first()
  val result = analyze-nested-tail-inner-first()
  if result == result-nested-tail-inner-first() then println("✓ test-nested-tail-inner-first passed")
  else println("✗ test-nested-tail-inner-first FAILED: expected " ++ result-nested-tail-inner-first().show ++ ", got " ++ result.show)

fun test-nested-tail-outer-first()
  val result = analyze-nested-tail-outer-first()
  if result == result-nested-tail-outer-first() then println("✓ test-nested-tail-outer-first passed")
  else println("✗ test-nested-tail-outer-first FAILED: expected " ++ result-nested-tail-outer-first().show ++ ", got " ++ result.show)

fun test-nested-three-levels()
  val result = analyze-nested-three-levels()
  if result == result-nested-three-levels() then println("✓ test-nested-three-levels passed")
  else println("✗ test-nested-three-levels FAILED: expected " ++ result-nested-three-levels().show ++ ", got " ++ result.show)

fun test-nested-absorb()
  val result = analyze-nested-absorb()
  if result == result-nested-absorb() then println("✓ test-nested-absorb passed")
  else println("✗ test-nested-absorb FAILED: expected " ++ result-nested-absorb().show ++ ", got " ++ result.show)

fun main()
  println("Running nested tests...")
  test-nested-simple()
  test-nested-simple-two()
  test-nested-op-after()
  test-nested-op-before()
  test-nested-inner-first()
  test-nested-outer-first()
  test-nested-tail-simple()
  test-nested-tail-op-after()
  test-nested-tail-op-before()
  test-nested-tail-inner-first()
  test-nested-tail-outer-first()
  test-nested-three-levels()
  test-nested-absorb()
  println("nested tests complete")

