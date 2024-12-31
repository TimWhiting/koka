import std/num/int32
import std/time/duration

noinline fun wait(dur: duration): int32
  dur.milli-seconds.int32

fun main()
  wait(3.seconds)