
effect ctl op1(i: int): string

fun x1()
  with ctl op1(i) i.show
  op1(0)

fun analyze()
  x1()