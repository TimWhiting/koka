module tail-outer

// --- Tail resumption effects ---
effect ex41
  ctl ex41(a: int): int

effect ex42
  ctl ex42(a: int): int

effect ex43
  ctl ex43(a: (int,int)): int

fun analyze-nested-tail-outer-first(): int
  trace("Example 44 - mixed effects under both handlers - outer first (tail resume outer)")
  with ctl ex41(z) resume(z + 1)
  with ctl ex43(a) resume(a.fst)
  ex41(0) + 1 + ex43((1, 2)) // outer first
fun result-nested-tail-outer-first() 3
