
// Nondeterminism effects
effect choice1
  ctl choice1(a: (int, int)): int

effect choice2
  ctl choice2(a: (int, int)): int

effect choice3
  ctl choice3(a: (int, int)): int

fun (+*)(x: int, y: int): int
  trace("Adding " ++ x.show ++ " and " ++ y.show)
  x + y

// Three levels of nondeterminism
fun analyze-nondet-three-levels(): int
  trace("Nested nondet 3 - three levels")
  with ctl choice1(a) 
    val r1 : int = resume(a.fst)
    val r2 : int = resume(a.snd)
    r1 +* r2
  with ctl choice2(a) 
    val r1' : int = resume(a.fst)
    val r2' : int = resume(a.snd)
    r1' +* r2'
  with ctl choice3(a) 
    val r1'' : int = resume(a.fst)
    val r2'' : int = resume(a.snd)
    r1'' +* r2''
  
  choice3((choice2((1, 2)), choice1((3, 4))))
fun result-nondet-three-levels() 40
fun main()
  analyze-nondet-three-levels()