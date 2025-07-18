
effect op3
  final ctl op3(i: int, b: int): a

fun x14()
  with final ctl op3(i, b) i.show ++ b.show
  op3(1, 2)

fun analyze()
  x14()