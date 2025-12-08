module complex-flow

effect ask
  ctl ask(): int

effect tell
  ctl tell(msg: int): ()

fun normal-inc(x: int): int
  x + 1

fun normal-double(x: int): int
  x * 2

// Tail call of normal function in handler
fun analyze-complex-tail-call(): int
  trace("Complex 1 - tail call normal function")
  with ctl ask() normal-inc(resume(1))
  ask()
fun result-complex-tail-call() 2

// Non-tail call of normal function in handler
fun analyze-complex-non-tail-call(): int
  trace("Complex 2 - non-tail call normal function")
  with ctl ask() 
    val x = resume(1)
    normal-inc(x) + 1
  ask()
fun result-complex-non-tail-call() 3

// Tail call of continuation in normal function (not possible directly, but via effect)
// Normal function calling effect in tail position
fun tail-ask(): <ask> int
  ask()

fun analyze-complex-tail-effect(): int
  trace("Complex 3 - tail call effect in normal function")
  with ctl ask() resume(42)
  tail-ask()
fun result-complex-tail-effect() 42

// Nested handlers with normal functions interleaving
fun analyze-complex-nested-interleave(): int
  trace("Complex 4 - nested handlers with normal functions")
  with ctl ask() resume(10)
  with ctl tell(x) 
    val y = ask()
    resume(())
    y + x
  
  tell(5)
  ask()
fun result-complex-nested-interleave() 15 

// Complex 5: Deeply nested with recursion
fun fib-eff(n: int): <ask,div> int
  if n <= 1 then ask()
  else fib-eff(n - 1) + fib-eff(n - 2)

fun analyze-complex-recursive(): div int
  trace("Complex 5 - recursive function with effect")
  with ctl ask() resume(1)
  fib-eff(4)
fun result-complex-recursive() 5 

// Complex 6: 3 layers of handlers with mutable state
effect choice
  ctl flip(): bool

effect fail
  ctl fail(): a

fun analyze-complex-layers(): int
  trace("Complex 6 - 3 layers: state, choice, fail")
  var s := 0
  with handler
    ctl flip() 
      s := s + 1
      val r1 : int = resume(True)
      val r2 : int = resume(False)
      r1 + r2
    return(x: int) x
  
  with ctl fail() 0
  
  if flip() then
    if flip() then
      s := s + 10
      1
    else
      fail()
  else
    2
fun result-complex-layers() 3

fun apply-cont(f: int -> int, x: int): int
  f(x)

fun analyze-complex-resume-func(): int
  trace("Complex 7 - resume passed as function")
  with ctl ask() apply-cont(resume, 10)
  ask() + 1
fun result-complex-resume-func() 11

fun test-complex-tail-call()
  val result = analyze-complex-tail-call()
  if result == result-complex-tail-call() then println("✓ test-complex-tail-call passed")
  else println("✗ test-complex-tail-call FAILED: expected " ++ result-complex-tail-call().show ++ ", got " ++ result.show)

fun test-complex-non-tail-call()
  val result = analyze-complex-non-tail-call()
  if result == result-complex-non-tail-call() then println("✓ test-complex-non-tail-call passed")
  else println("✗ test-complex-non-tail-call FAILED: expected " ++ result-complex-non-tail-call().show ++ ", got " ++ result.show)

fun test-complex-tail-effect()
  val result = analyze-complex-tail-effect()
  if result == result-complex-tail-effect() then println("✓ test-complex-tail-effect passed")
  else println("✗ test-complex-tail-effect FAILED: expected " ++ result-complex-tail-effect().show ++ ", got " ++ result.show)

fun test-complex-nested-interleave()
  val result = analyze-complex-nested-interleave()
  if result == result-complex-nested-interleave() then println("✓ test-complex-nested-interleave passed")
  else println("✗ test-complex-nested-interleave FAILED: expected " ++ result-complex-nested-interleave().show ++ ", got " ++ result.show)

fun test-complex-recursive()
  val result = analyze-complex-recursive()
  if result == result-complex-recursive() then println("✓ test-complex-recursive passed")
  else println("✗ test-complex-recursive FAILED: expected " ++ result-complex-recursive().show ++ ", got " ++ result.show)

fun test-complex-layers()
  val result = analyze-complex-layers()
  if result == result-complex-layers() then println("✓ test-complex-layers passed")
  else println("✗ test-complex-layers FAILED: expected " ++ result-complex-layers().show ++ ", got " ++ result.show)

fun test-complex-resume-func()
  val result = analyze-complex-resume-func()
  if result == result-complex-resume-func() then println("✓ test-complex-resume-func passed")
  else println("✗ test-complex-resume-func FAILED: expected " ++ result-complex-resume-func().show ++ ", got " ++ result.show)

fun main()
  println("Running complex-flow tests...")
  test-complex-tail-call()
  test-complex-non-tail-call()
  test-complex-tail-effect()
  test-complex-nested-interleave()
  test-complex-recursive()
  test-complex-layers()
  test-complex-resume-func()
  println("complex-flow tests complete")

