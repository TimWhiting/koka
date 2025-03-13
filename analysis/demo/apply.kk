fun apply(f)
  fn(x)
    f(x)

fun example()
  apply(add1)(42) + apply(sub1)(35)


fun add1(x)
  x + 1

fun sub1(x)
  x - 1