
effect ex1
  final ctl ex1(i: int): a 

fun analyze-ex1(): int
  trace("Example 1 - exceptions")
  with final ctl ex1(a) a
  ex1(1)
fun result-ex1() 1

effect ex2
  fun ex2(a: int): int
fun analyze-ex2(): int
  trace("Example 2 - simple")
  with fun ex2(a) a + 1
  ex2(0)
fun result-ex2() 1

