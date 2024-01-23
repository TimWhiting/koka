import std/time
import std/async
import std/num/int64

fun main()
  val x = ref(0)
  local-time-now().show.println
  timer(1000.milli-seconds) fn(t)
    "Hello from repeating timer".println
    t.get-repeat.int.println
    x := !x + 1
    if (!x == 4) then
      t.set-repeat(100.milli-seconds)
    if !x == 10 then False else True
  "Start 1 second timer".println
  local-time-now().show.println
  wait(1.seconds)
  "End 1 second timer & start 10 second timer".println
  local-time-now().show.println
  wait(10.seconds)
  "End 10 seconds".println
  local-time-now().show.println