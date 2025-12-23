
// Nondeterminism effects
effect choice1
  ctl choice1(a: int): int

effect choice2
  ctl choice2(a: int): int

// Three levels of nondeterminism
fun analyze-nondet-three-levels(): int
  trace("Nested nondet 3 - three levels")
  with handler
    return(x0) x0
    ctl choice1(a) 
      val r1 : int = resume(a + 1) 
      val r2 : int = resume(a - 1)
      r1 + r2 // (21+19)=40
  with handler
    return (x1) x1
    ctl choice2(a) 
      val r1' : int = resume(a + 1)
      val r2' : int = resume(a - 1)
      r1' + r2'
  val r1'' = choice2(1) // 1, 2, 2
  val r2'' = choice1(4) // 3, 4, 4, 3, 4
  r1'' + r2''
fun result-nondet-three-levels() 40
fun main()
  analyze-nondet-three-levels()