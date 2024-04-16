fun tail(n)
  if n == 0 then 0 else tail(n - 1)
fun main()
  val res = tail(1)
  res.println
  