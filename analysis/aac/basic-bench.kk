
effect ex1
  ctl ex1(i: int): int 

// fun analyze-ex1(): int
//   trace("Example 1 - exceptions")
//   with ctl ex1(a) a
//   ex1(1)
// fun result-ex1() 1

// fun analyze-ex10(): int
//   trace("Example 10 - simple")
//   with ctl ex1(a) resume(a + 1)
//   ex1(0)
// fun result-ex10() 1

// fun analyze-ex11(): int
//   trace("Example 121 - simple cont")
//   with ctl ex1(a) resume(a + 1)
//   ex1(0) + 1 
// fun result-ex11() 2

// fun analyze-ex12(): int
//   trace("Example 122 - simple cont")
//   with ctl ex1(a) resume(a + 1) + 1
//   ex1(0)
// fun result-ex12() 2

// fun analyze-ex13(): int
//   trace("Example 123 - simple cont2")
//   with ctl ex1(a) resume(a + 1) + 1
//   ex1(0) + 1
// fun result-ex13() 3

effect ex2
  ctl ex2(a: (int, int)): int


fun analyze-ex22(): int
  trace("Example 22 - nondeterminism twice")
  with handler
    ctl ex2(a) resume(a.fst) + resume(a.snd)
    return(x: int) x
  ex2((1,2)) + ex2((1,2))
fun result-ex22() 12

// fun analyze-ex23(): int
//   trace("Example 23 - nondeterminism twice")
//   with handler
//     ctl ex1(a) resume(3) + resume(4)
//     return(x: int) x
//   ex1(1) + ex1(2)
// fun result-ex23() 28
