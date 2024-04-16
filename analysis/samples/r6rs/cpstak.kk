// CPSTAK -- A continuation-passing version of the TAK benchmark.
// A good test of first class procedures and tail recursion.

fun tak(x: int, y, z, k)
    if !(y < x) then k(z)
    else tak(x - 1, y, z, fn(v1)
      tak(y - 1, z, x, fn(v2)
        tak(z - 1, x, y, fn(v3)
          tak(v1, v2, v3, k)
        )
      )
    )

fun cpstak(x1, y1, z1)  
  tak(x1, y1, z1, fn(a) a)

fun analyze()
  cpstak(32, 15, 8)

fun main()
  val res = cpstak(32, 15, 8)
  res.show.println