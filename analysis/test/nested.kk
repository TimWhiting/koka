// --- Non-tail resumption effects ---
effect ex31
  ctl ex31(c: int): int

effect ex32
  ctl ex32(c: int): int

effect ex33
  ctl ex33(c: (int,int)): int

// --- Tail resumption effects ---
effect ex41
  ctl ex41(c: int): int

effect ex42
  ctl ex42(c: int): int

effect ex43
  ctl ex43(c: (int,int)): int

// --- New effects for extended coverage ---
effect ex51
  ctl ex51(c: int): int

effect ex52
  ctl ex52(c: int): int


fun analyze-nested-op-before(): int
  with ctl ex31(z) resume(z) + 1
  with ctl ex33(n) ex31(n.fst) + resume(n.snd) // op before resume
  ex33((1,2))
fun result-nested-op-before() 5