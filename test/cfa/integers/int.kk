import std/num/random
import std/num/int32

val c1 = 1
val c11 = 11
val c3 = 3
val c5 = 5
val top = 30000000
fun main()
  var i := 0
  var i2 := 10
  while { i < top }
    i := i + c1
    i2 := i2 * c3
    val x = c5
    i2 := (x + i2) / c5
  i2.show.println
    