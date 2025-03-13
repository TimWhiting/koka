fun process-data(input, process)
  val x = input * 5
  val y = process(input, x)
  y

fun example1()
  process-data(1, fn(a, b) a + 3)