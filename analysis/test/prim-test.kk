import std/num/int64
import std/num/int32
import std/num/float64
import std/core/string

fun prim-test() : string
  val i1 = 0x12345678.int32
  val i2 = 0x9ABCDEF0.int32
  val i64 = int64(i1, i2)
  
  if i64.hi.int32 != i1 then return "hi-fail"
  if i64.lo.int32 != i2 then return "lo-fail"
  
  val anded = and(i64, 0xFFFFFFFF00000000.int64)
  if anded != i1.int64.shl(32) then return "and-fail"
  
  val f = 1.23
  val bits = f.float64-to-bits
  if bits.float64-from-bits != f then return "float-bits-fail"
  
  val s = "Hello World"
  if !s.to-lower.contains("hello") then return "string-fail"
  
  "ok"

fun analyze-prim()
  prim-test()

fun result-prim()
  "ok"

fun main()
  println(prim-test())
