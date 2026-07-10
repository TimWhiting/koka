// forking interleaving: a main strand receiving from a channel, plus timer
// strands that emit into it -- the ui/app pattern in miniature.
import std/async
import std/async/interleave
import std/async/channel
import std/time/duration

fun main()
  println("main-start")
  val ch : channel<string> = channel()
  forking fn(fork)
    // producer strands: each waits then emits
    fork fn()
      wait(30.milli-seconds)
      ch.emit("first")
    fork fn()
      wait(60.milli-seconds)
      ch.emit("second")
    fork fn()
      wait(90.milli-seconds)
      ch.emit("third")
    // main strand: receive three messages then cancel everything
    var got := 0
    while { got < 3 }
      val m = ch.receive()
      got := got + 1
      println("got " ++ m)
    println("main-end")
    cancel-outstanding()
