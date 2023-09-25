import std/num/int32
import std/num/random

val c1 = 1.int32
val c11 = 11.int32
val c3 = 3.int32
val c5 = 5.int32
val top = 30000000.int32
val c10 = 10.int32
val c0 = 0.int32
val cm1 = -1.int32
fun main()
  var i := c0
  var i2 := c10
  while { i < top }
    i := i + c1
    i2 := i2 * c3
    val x = c5
    i2 := (x + i2).newDiv(c5)
  i2.int.show.println
    
// pub inline extern int16(i: int32): int16 
//   inline "(#1)"

pub fip fun newDiv( x : int32, y : int32 ) : int32
  if (y == c0).unlikely then return c0
  if ((y == cm1).unlikely && (x==min-int32).unlikely) return x
  val q = unsafe-cdiv(x,y)
  val r = unsafe-cmod(x,y)
  if (r >= c0).likely then q
  elif (y > c0) then q - c1
  else q + c1


// Euclidean-0 modulus. See `(/):(x : int32, y : int32) -> int32` division for more information.
pub fip fun newMod( x : int32, y : int32 ) : int32
  if (y == c0).unlikely then return x
  if ((y == cm1).unlikely && (x==min-int32).unlikely) return c0
  val r = unsafe-cmod(x,y)
  if (r >= c0).likely then r
  elif (y > c0) then (r+y)
  else (r - y)

pub inline extern likely(b: bool): bool
  c inline "kk_likely(#1)"

pub inline extern unlikely(b: bool): bool
  c inline "kk_unlikely(#1)"