// ACK -- One of the Kernighan and Van Wyk benchmarks.

fun ack(m, n)
  if m == 0 then n + 1
  elif n == 0 then ack(m - 1, 1)
  else ack(m - 1, ack(m, n - 1))

fun main()
  val res = ack(3, 12)
  res.println