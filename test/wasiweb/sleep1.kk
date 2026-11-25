// Integration test for the wasi-web (wasm32-wasip1 core module, no JSPI) inverted event
// loop: a single timer-based `wait` must actually round-trip through the JS
// host (real setTimeout) and the wasm guest must still be reachable
// afterwards to print "b" and let the (real) node process exit.
import std/async
import std/time/duration

fun main()
  println("a")
  wait(100.milli-seconds)
  println("b")
