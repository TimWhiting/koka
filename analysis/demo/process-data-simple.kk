








fun process-data(input, process: (int, int) -> int)
  val x = input * 5
  val y = process(input, x)
  y.println

fun example1()
  process-data(1, fn(a, b) a + 3)
  process-data(2, fn(c, d) c + d)