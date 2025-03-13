fun apply(f: int -> int): (int -> int)
  fn(x: int): int
    val res = f(x)
    res

fun example()
  val res = apply(add1)(42) + apply(sub1)(35)
  res


fun add1(a: int): int
  a + 1

fun sub1(s: int): int
  s - 1