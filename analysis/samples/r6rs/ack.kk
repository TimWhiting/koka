// ACK -- One of the Kernighan and Van Wyk benchmarks.

fun ack(m, n)
  if m == 0 then n + 1
  elif n == 0 then ack(m - 1, 1)
  else ack(m - 1, ack(m, n - 1))

// fun analyze()
  // ack(3, 12)

fun analyze()
  fact(3, 2)

fun fact(n, acc)
  if n == 0 then acc
  else 1 - fact(acc - 1, acc)


fun main()
  val res = ack(3, 12)
  res.println