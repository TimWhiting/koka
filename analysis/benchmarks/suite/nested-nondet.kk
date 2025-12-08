module nested-nondet

// Nondeterminism effects
effect choice1
  ctl choice1(a: (int, int)): int

effect choice2
  ctl choice2(a: (int, int)): int

effect choice3
  ctl choice3(a: (int, int)): int

// Tail-resumptive effect for comparison
effect tail1
  ctl tail1(a: int): int

// Failure effect
effect fail
  ctl fail(): a

// Simple nondeterminism: fork on two values
fun analyze-nondet-nested-simple(): int
  trace("Nested nondet 1 - simple forking")
  with ctl choice1(a) 
    val r1 : int = resume(a.fst)
    val r2 : int = resume(a.snd)
    r1 + r2
  with ctl choice2(a) 
    val r1 : int = resume(a.fst)
    val r2 : int = resume(a.snd)
    r1 + r2
  choice2((choice1((1, 2)), choice1((3, 4))))
fun result-nondet-nested-simple() 20
// choice1((1,2)) branches: continue with 1, then with 2
// For first branch (1): choice2((1, choice1((3,4))))
//   choice1((3,4)) branches: choice2((1,3)) + choice2((1,4)) = 4 + 5 = 9
// For second branch (2): choice2((2, choice1((3,4))))
//   choice1((3,4)) branches: choice2((2,3)) + choice2((2,4)) = 5 + 6 = 11
// Total: 9 + 11 = 20

// Nested nondeterminism with tail-resumptive handler
fun analyze-nondet-nested-tail(): int
  trace("Nested nondet 2 - nondet with tail-resumptive")
  with ctl choice1(a) 
    val r1 : int = resume(a.fst)
    val r2 : int = resume(a.snd)
    r1 + r2
  with ctl tail1(x) resume(x * 2)
  
  tail1(choice1((1, 2)))
fun result-nondet-nested-tail() 6
// choice1((1,2)) branches: continue with 1, then with 2
// For first branch: tail1(1) -> 1 * 2 = 2
// For second branch: tail1(2) -> 2 * 2 = 4
// Total: 2 + 4 = 6

// Three levels of nondeterminism
fun analyze-nondet-three-levels(): int
  trace("Nested nondet 3 - three levels")
  with ctl choice1(a) 
    val r1 : int = resume(a.fst)
    val r2 : int = resume(a.snd)
    r1 + r2
  with ctl choice2(a) 
    val r1 : int = resume(a.fst)
    val r2 : int = resume(a.snd)
    r1 + r2
  with ctl choice3(a) 
    val r1 : int = resume(a.fst)
    val r2 : int = resume(a.snd)
    r1 + r2
  
  choice3((choice2((1, 2)), choice1((3, 4))))
fun result-nondet-three-levels() 40
// Three levels of branching multiplies the branches
// choice2((1,2)) creates 2 branches: 1, 2
// choice1((3,4)) creates 2 branches: 3, 4
// So we have 2*2 = 4 combinations
// choice3 then resumes twice for each, multiplying by 2 again = 8 paths
// choice3((1,3))=4, choice3((1,4))=5, choice3((2,3))=5, choice3((2,4))=6
// Each appears twice: 4+4+5+5+5+5+6+6 = 40


// Alternating nondeterminism and tail-resumptive
fun analyze-nondet-alternating(): int
  trace("Nested nondet 4 - alternating nondet/tail-resumptive")
  with ctl choice1(a) 
    val r1 : int = resume(a.fst)
    val r2 : int = resume(a.snd)
    r1 + r2
  with ctl tail1(x) resume(x * 2)
  with ctl choice2(a) 
    val r1 : int = resume(a.fst)
    val r2 : int = resume(a.snd)
    r1 + r2
  
  choice2((choice1((tail1(1), tail1(2))), 10))
fun result-nondet-alternating() 26
// First: tail1(1) -> 2, tail1(2) -> 4
// choice1((2, 4)) branches to 2 and 4
// For first branch: choice2((2, 10)) = 2 + 10 = 12
// For second branch: choice2((4, 10)) = 4 + 10 = 14
// Total: 12 + 14 = 26

// Nondeterminism in both inner and outer context
fun analyze-nondet-both-contexts(): int
  trace("Nested nondet 5 - nondet in inner and outer context")
  with ctl choice1(a) 
    val r1 : int = resume(a.fst)
    val r2 : int = resume(a.snd)
    r1 + r2
  with ctl choice2(a) 
    val r1 : int = resume(a.fst)
    val r2 : int = resume(a.snd)
    r1 * 2 + r2 * 3
  
  choice2((choice1((1, 2)), choice1((10, 20))))
fun result-nondet-both-contexts() 192
// choice1((1,2)) branches to 1 and 2
// For branch 1: choice2((1, choice1((10,20))))
//   choice1((10,20)) branches: choice2((1,10)) + choice2((1,20))
//   = (1*2 + 10*3) + (1*2 + 20*3) = 32 + 62 = 94
// For branch 2: choice2((2, choice1((10,20))))
//   choice1((10,20)) branches: choice2((2,10)) + choice2((2,20))
//   = (2*2 + 10*3) + (2*2 + 20*3) = 34 + 64 = 98
// Total: 94 + 98 = 192

// Guarded nondeterminism: choice depends on value
fun analyze-nondet-guarded(): int
  trace("Nested nondet 6 - guarded choice")
  with ctl choice1(a) 
    if a.fst > 0 then 
      val r1 : int = resume(a.fst)
      val r2 : int = resume(a.snd)
      r1 + r2
    else
      resume(0)
  
  choice1((1, 2)) + choice1((0, 5))
fun result-nondet-guarded() 3

// Nondeterminism with failure: some branches fail
fun analyze-nondet-with-failure(): int
  trace("Nested nondet 7 - nondet with failure")
  with ctl choice1(a) 
    val r1 : int = resume(a.fst)
    val r2 : int = resume(a.snd)
    r1 + r2
  with ctl fail() 0 // Catch failure, return 0
  
  // Choice creates branches; second branch fails
  choice1((10, fail()))
fun result-nondet-with-failure() 0
// The fail() effect is caught by the fail handler which returns 0
// This causes the entire choice1 effect to fail and return 0


// Conditional resume count: variable branching factor
fun analyze-nondet-variable-branches(): int
  trace("Nested nondet 8 - variable branches")
  with ctl choice1(a) 
    if a.fst == 0 then resume(a.snd)
    else if a.fst == 1 then 
      val x : int = resume(a.snd)
      val y : int = resume(a.fst)
      x + y
    else 
      val r1 : int = resume(a.fst)
      val r2 : int = resume(a.snd)
      val r3 : int = resume(a.snd)
      r1 + r2 + r3
  
  choice1((2, 5))
fun result-nondet-variable-branches() 12
// choice1((2, 5)): fst=2 (not 0 or 1)
// So: resume(2) + resume(5) + resume(5) = 2 + 5 + 5 = 12

fun test-nondet-nested-simple()
  val result = analyze-nondet-nested-simple()
  if result == result-nondet-nested-simple() then println("✓ test-nondet-nested-simple passed")
  else println("✗ test-nondet-nested-simple FAILED: expected " ++ result-nondet-nested-simple().show ++ ", got " ++ result.show)

fun test-nondet-nested-tail()
  val result = analyze-nondet-nested-tail()
  if result == result-nondet-nested-tail() then println("✓ test-nondet-nested-tail passed")
  else println("✗ test-nondet-nested-tail FAILED: expected " ++ result-nondet-nested-tail().show ++ ", got " ++ result.show)

fun test-nondet-three-levels()
  val result = analyze-nondet-three-levels()
  if result == result-nondet-three-levels() then println("✓ test-nondet-three-levels passed")
  else println("✗ test-nondet-three-levels FAILED: expected " ++ result-nondet-three-levels().show ++ ", got " ++ result.show)

fun test-nondet-alternating()
  val result = analyze-nondet-alternating()
  if result == result-nondet-alternating() then println("✓ test-nondet-alternating passed")
  else println("✗ test-nondet-alternating FAILED: expected " ++ result-nondet-alternating().show ++ ", got " ++ result.show)

fun test-nondet-both-contexts()
  val result = analyze-nondet-both-contexts()
  if result == result-nondet-both-contexts() then println("✓ test-nondet-both-contexts passed")
  else println("✗ test-nondet-both-contexts FAILED: expected " ++ result-nondet-both-contexts().show ++ ", got " ++ result.show)

fun test-nondet-guarded()
  val result = analyze-nondet-guarded()
  if result == result-nondet-guarded() then println("✓ test-nondet-guarded passed")
  else println("✗ test-nondet-guarded FAILED: expected " ++ result-nondet-guarded().show ++ ", got " ++ result.show)

fun test-nondet-with-failure()
  val result = analyze-nondet-with-failure()
  if result == result-nondet-with-failure() then println("✓ test-nondet-with-failure passed")
  else println("✗ test-nondet-with-failure FAILED: expected " ++ result-nondet-with-failure().show ++ ", got " ++ result.show)

fun test-nondet-variable-branches()
  val result = analyze-nondet-variable-branches()
  if result == result-nondet-variable-branches() then println("✓ test-nondet-variable-branches passed")
  else println("✗ test-nondet-variable-branches FAILED: expected " ++ result-nondet-variable-branches().show ++ ", got " ++ result.show)

fun main()
  println("Running nested-nondet tests...")
  test-nondet-nested-simple()
  test-nondet-nested-tail()
  test-nondet-three-levels()
  test-nondet-alternating()
  test-nondet-both-contexts()
  test-nondet-guarded()
  test-nondet-with-failure()
  test-nondet-variable-branches()
  println("nested-nondet tests complete")

