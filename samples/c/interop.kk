extern import 
  c file "interop-c.h"

extern hello(name: string, age: int32, cb: rawfun<int32,e,()>): e int32
  c "some_function"

fun main()
  hello("world", 32.int32, fn(x) println(x.int.show))
  hello("world", 32.int32, xi)

fun xi(x:int32)
  println(x.int.show)