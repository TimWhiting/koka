effect val hi: int

effect fun op1(i: int): string
effect ctl op2(i: int): string
effect ctl op3(i: int): int

fun x0()
  with val hi = 0
  hi

fun x1()
  with fun op1(i) i.show
  op1(0)

fun x2()
  with ctl op2(i) resume(i.show)
  op2(0)

fun x3()
  with ctl op2(i) i.show
  op2(0)

fun x4()
  with ctl op2(i) i.show
  with ctl op2(i) "2"
  op2(0)

fun x5()
  fn()
    with ctl op2(i) i.show
    op2(1)
  with ctl op2(i) "2"
  op2(0)

fun x6()
  with fun op1(i) i.show
  with ctl op2(i) "error"
  op1(0)

fun x7()
  with ctl op2(i) "error"
  with fun op1(i) i.show
  op1(0)

fun x8()
  with ctl op2(i) i.show
  with fun op1(i) "error"
  op2(0)

fun x9()
  with fun op1(i) "error"
  with ctl op2(i) i.show
  op2(0)

fun x10()
  val z = x9()
  val y = x8()
  y ++ z

fun x11()
  with ctl op2(i) "2" ++ i.show
  op2(0)

fun x12()
  with ctl op2(i) "4" ++ resume("2" ++ i.show)
  op2(0)

fun x13()
  with ctl op2(i) resume("2" ++ i.show)
  op2(0)

fun x14()
  with ctl op3(i) 4 - resume(i + 1)
  op3(1)

fun x15()
  with ctl op3(i) 4 + resume(i + 1)
  op3(1)

fun analyze()
  // x0()
  // x1()
  // x2()
  // x3()
  // x4()
  // x5()
  // x6()
  // x7()
  // x8()
  // x9()
  // x10()
  // x11()
  // x12()
  // x13()
  // x14()
  x15()

fun main()
  with val hi = 0
  hi