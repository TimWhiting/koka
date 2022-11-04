import std/time

pub fun main()
  timer(100.milli-seconds, fn(t) {"Hello From Timer".println; True}, True)