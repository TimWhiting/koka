// Two strands ping-ponging through channels a large number of times, kicked
// off by a single timer. Each emit synchronously resumes the waiting peer, so
// the whole ping-pong runs within ONE host `dispatch` re-entry -- stresses
// synchronous strand-resume nesting.
import std/async
import std/async/interleave
import std/async/channel
import std/time/duration

fun main()
  val n = 5000
  val a2b : channel<int> = channel()
  val b2a : channel<int> = channel()
  forking fn(fork)
    fork fn()
      // strand B: echo back n times
      var i := 0
      while { i < n }
        val v = a2b.receive()
        b2a.emit(v + 1)
        i := i + 1
    fork fn()
      // strand A: initial kick after a timer, then ping-pong
      wait(10.milli-seconds)
      var i := 0
      a2b.emit(0)
      while { i < n }
        val v = b2a.receive()
        i := i + 1
        if i < n then a2b.emit(v + 1)
      println("pong-count " ++ i.show)
      cancel-outstanding()
