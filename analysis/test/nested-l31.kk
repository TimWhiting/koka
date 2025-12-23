
// Nondeterminism effects
effect choice1
  ctl choice1(a: (int, int)): int

effect choice2
  ctl choice2(a: (int, int)): int

fun (+*)(x: int, y: int, ?kk-file-line): int
  trace("Adding " ++ x.show ++ " and " ++ y.show ++ " from " ++ kk-file-line)
  x + y

// Three levels of nondeterminism
fun analyze-nondet-three-levels(): int
  trace("Nested nondet 3 - three levels")
  with ctl choice1(a) 
    // trace("Choice1 between " ++ a.fst.show ++ " and " ++ a.snd.show)
    trace("Calling resume1 from choice1")
    val r1 : int = resume(a.fst) 
    trace("r1 " ++ r1.show) // (4+5)9, (9+10)19, (5+5)10
    trace("Calling resume2 from choice1")
    val r2 : int = resume(a.snd)
    trace("r2 " ++ r2.show) // (4+6)10, (5+6)11, (10+11)21
    r1 +* r2 // (21+19)=40
  with ctl choice2(a) 
    // trace("Choice2 between " ++ a.fst.show ++ " and " ++ a.snd.show)
    trace("Calling resume1 from choice2")
    val r1' : int = resume(a.fst)
    trace("r1' " ++ r1'.show) // (1+3)4, (1+4)5
    trace("Calling resume2 from choice2")
    val r2' : int = resume(a.snd)
    trace("r2' " ++ r2'.show) // (2+3)5, (2+4)6, (2+3)5, (2+4)6
    r1' +* r2'
  val r1'' = choice1((1, 2)) // 1, 2, 2
  trace("r1'' = " ++ r1''.show)
  val r2'' = choice2((3, 4)) // 3, 4, 4, 3, 4
  trace("r2'' = " ++ r2''.show)
  r1'' +* r2''
fun main()
  analyze-nondet-three-levels()