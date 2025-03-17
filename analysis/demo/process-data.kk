fun process-data(input, process)
  val x = input * 5
  val y = process(input, x)
  // y will result in an error with 0CFA
  y

fun example1()
  // When evaluating + we will lose the context of which call to "+" was demanded with 0CFA.
  // We have to represent all values that flow out of +
  // Resolving some of those paths might cause the analysis to fail
  process-data(1, fn(a, b) a + 3)
  process-data(2, fn(c, d) c + d)