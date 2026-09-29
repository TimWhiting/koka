// Two OS threads running Koka code concurrently must not corrupt the heap. The
// memory both threads reach is the empty evidence vector (a stuck static), the
// string literals and toplevel constants in C statics (stuck at first use or
// module init), and values sent through an xchannel (marked thread-shared).
//
// Part 1 churns shared constants and literals from both threads (`duration.show`);
// part 2 streams boxed structs to main while the worker keeps allocating.
import std/async
import std/time/duration
import std/async/thread

struct model( ticks : int, result : maybe<int> )

fun churn( n : int, acc : int ) : ioc int
  if n <= 0 then acc else
    val s = (n.milli-seconds).show      // dup/drops shared decimal/duration constants + literals
    churn(n - 1, acc + s.count)

fun sender-loop( out : xsender<model>, n : int ) : <async,ioc,exn> ()
  if n >= 200 then () else
    wait(1.milli-seconds)               // concurrent allocation on the worker heap
    out.xemit(Model(n, if n > 3 then Just(n) else Nothing))
    sender-loop(out, n + 1)

fun main()
  // part 1: both threads churn the same shared constants/literals
  val c : xchannel<int> = xchannel()
  val csend = c.sender
  spawn-thread(fn()
    with handle/try fn(err) println("worker exn: " ++ err.show)
    csend.xemit(churn(10000, 0))
  )
  val m = churn(10000, 0)
  val w = c.xreceive
  println("churn: main=" ++ m.show ++ " worker=" ++ w.show ++ (if m == w then " ok" else " MISMATCH"))
  c.close
  // part 2: boxed structs cross while the worker keeps allocating
  val x : xchannel<model> = xchannel()
  val out = x.sender
  spawn-thread(fn()
    with handle/try fn(err) println("worker exn: " ++ err.show)
    sender-loop(out, 0)
  )
  val got = list(1, 200).map(fn(_) x.xreceive.ticks)
  println("stream: received " ++ got.length.show ++ ", sum=" ++ got.sum.show)
  x.close
