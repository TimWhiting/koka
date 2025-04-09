fun process-data(input, process)
  val x = input * 5
  val y = process(input, x)
  // y will result in an error with 0CFA
  y

fun main()
  val _ = example1(2)
  example1(3)

fun example1(z : int)
  // When evaluating + we will lose the context of which call to "+" was demanded with 0CFA.
  // We have to represent all values that flow out of +
  // Resolving some of those paths might cause the analysis to fail
  val _ = process-data(1, fn(a, b) a + 3)
  val y = process-data(2, fn(c, d) c + d)
  y