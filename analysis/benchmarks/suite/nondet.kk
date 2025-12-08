module nondet

effect ex2
  ctl ex2(a: (int, int)): int

fun analyze-nondet-simple(): int
  trace("Example 20 - nondeterminism")
  with handler
    ctl ex2(a) resume(a.fst) + resume(a.snd)
    return(x: int) x
  ex2((1,2))
fun result-nondet-simple() 3

fun analyze-nondet-context(): int
  trace("Example 21 - nondeterminism")
  with handler 
    ctl ex2(a) resume(a.fst) + resume(a.snd)
    return(x: int) x
  ex2((1,2)) + 1
fun result-nondet-context() 5

fun analyze-nondet-nested(): int
  trace("Example 22 - nondeterminism twice")
  with handler
    ctl ex2(a) resume(a.fst) + resume(a.snd)
    return(x: int) x
  ex2((1,2)) + ex2((1,2))
fun result-nondet-nested() 12

// Nondeterminism with continuation discarded: resumption result unused
fun analyze-nondet-discard(): int
  trace("Example 23 - resumption result discarded")
  with handler
    ctl ex2(a) 
      val _ = resume(a.fst)
      resume(a.snd)
    return(x: int) x
  ex2((10, 20))
fun result-nondet-discard() 20
// First resume with 10 is discarded, only second resume with 20 returns

fun test-nondet-simple()
  val result = analyze-nondet-simple()
  if result == result-nondet-simple() then println("✓ test-nondet-simple passed")
  else println("✗ test-nondet-simple FAILED: expected " ++ result-nondet-simple().show ++ ", got " ++ result.show)

fun test-nondet-context()
  val result = analyze-nondet-context()
  if result == result-nondet-context() then println("✓ test-nondet-context passed")
  else println("✗ test-nondet-context FAILED: expected " ++ result-nondet-context().show ++ ", got " ++ result.show)

fun test-nondet-nested()
  val result = analyze-nondet-nested()
  if result == result-nondet-nested() then println("✓ test-nondet-nested passed")
  else println("✗ test-nondet-nested FAILED: expected " ++ result-nondet-nested().show ++ ", got " ++ result.show)

fun test-nondet-discard()
  val result = analyze-nondet-discard()
  if result == result-nondet-discard() then println("✓ test-nondet-discard passed")
  else println("✗ test-nondet-discard FAILED: expected " ++ result-nondet-discard().show ++ ", got " ++ result.show)

fun main()
  println("Running nondet tests...")
  test-nondet-simple()
  test-nondet-context()
  test-nondet-nested()
  test-nondet-discard()
  println("nondet tests complete")

