// --- Non-tail resumption effects ---
effect ex31
  ctl ex31(a: int): int

effect ex32
  ctl ex32(a: int): int

fun analyze-nested-outer-first(): int
  with ctl ex31(z) resume(z)
  with ctl ex32(a) resume(a) 
  ex31(0) + ex32(1) // outer first
fun result-nested-outer-first() 1