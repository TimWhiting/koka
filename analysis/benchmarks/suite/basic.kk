module basic

effect ex1
  ctl ex1(i: int): int 

fun analyze-basic-exception(): int
  trace("Example 1 - exceptions")
  with ctl ex1(a) a
  ex1(1)
fun result-basic-exception() 1

fun analyze-basic-resume(): int
  trace("Example 10 - simple")
  with ctl ex1(a) resume(a + 1)
  ex1(0)
fun result-basic-resume() 1

fun analyze-basic-resume-context(): int
  trace("Example 121 - simple cont")
  with ctl ex1(a) resume(a + 1)
  ex1(0) + 1 
fun result-basic-resume-context() 2

fun analyze-basic-resume-op(): int
  trace("Example 122 - simple cont")
  with ctl ex1(a) resume(a + 1) + 1
  ex1(0)
fun result-basic-resume-op() 2

fun analyze-basic-resume-op-context(): int
  trace("Example 123 - simple cont2")
  with ctl ex1(a) resume(a + 1) + 1
  ex1(0) + 1
fun result-basic-resume-op-context() 3

fun test-basic-exception()
  val result = analyze-basic-exception()
  if result == result-basic-exception() then println("✓ test-basic-exception passed") 
  else println("✗ test-basic-exception FAILED: expected " ++ result-basic-exception().show ++ ", got " ++ result.show)

fun test-basic-resume()
  val result = analyze-basic-resume()
  if result == result-basic-resume() then println("✓ test-basic-resume passed") 
  else println("✗ test-basic-resume FAILED: expected " ++ result-basic-resume().show ++ ", got " ++ result.show)

fun test-basic-resume-context()
  val result = analyze-basic-resume-context()
  if result == result-basic-resume-context() then println("✓ test-basic-resume-context passed") 
  else println("✗ test-basic-resume-context FAILED: expected " ++ result-basic-resume-context().show ++ ", got " ++ result.show)

fun test-basic-resume-op()
  val result = analyze-basic-resume-op()
  if result == result-basic-resume-op() then println("✓ test-basic-resume-op passed") 
  else println("✗ test-basic-resume-op FAILED: expected " ++ result-basic-resume-op().show ++ ", got " ++ result.show)

fun test-basic-resume-op-context()
  val result = analyze-basic-resume-op-context()
  if result == result-basic-resume-op-context() then println("✓ test-basic-resume-op-context passed") 
  else println("✗ test-basic-resume-op-context FAILED: expected " ++ result-basic-resume-op-context().show ++ ", got " ++ result.show)

fun main()
  println("Running basic tests...")
  test-basic-exception()
  test-basic-resume()
  test-basic-resume-context()
  test-basic-resume-op()
  test-basic-resume-op-context()
  println("basic tests complete")

