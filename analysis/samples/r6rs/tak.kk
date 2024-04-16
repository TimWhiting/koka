// TAK -- A vanilla version of the TAKeuchi function.
fun tak(x: int, y, z)
  if !(y < x) then z
  else
    tak(tak(x - 1, y, z), tak(y - 1, z, x), tak(z - 1, x, y))

fun main()
  val res = tak(32, 15, 8)
  res.println
