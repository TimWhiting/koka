// interleave two timer strands
import std/async
import std/time/duration

fun dowait(name : string, s : duration)
  println("start " ++ name)
  wait(s)
  println("done " ++ name)
  name

fun main()
  println("main-start")
  val xs = interleaved([{ dowait("A", 50.milli-seconds) }, { dowait("B", 100.milli-seconds) }])
  println("result " ++ xs.join(","))
  println("main-end")
