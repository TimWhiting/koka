import std/num/int32

extern import 
  c header-file "externstruct.h"

extern struct "silly" silly
  a1: int32
  b1: int32

extern foo( x : int32 , f: rawfun<silly,<>,int32>) : int32
  c "foo"

extern a1(x: silly) : int32
  c inline "#1.a1"

extern b1(x: silly) : int32
  c inline "#1.b1"

fun main() {
  foo(10.int32, fn(x: silly) x.a1 + x.b1).int.println
}
