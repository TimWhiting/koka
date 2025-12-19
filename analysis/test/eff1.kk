
effect ex1
  ctl ex1(i: int): int 

fun analyze-basic-resume(): int
  with ctl ex1(a) resume(a + 1)
  ex1(0)
fun result-basic-resume() 1