// `min-load` costs one floor for a whole batch, not one floor per item
// (task #56, re-homed by task #58).
//
// The property is about what a user sees: a row of images kicked in one build
// must appear TOGETHER after the anti-flicker floor, not trickle in one at a
// time, and input must not be frozen for the sum of their floors.
//
// It used to be a property of `web-image-settle`, which held the floor inside
// the web backend's SERIAL input pump and so had to compute it as a deadline
// from the kick to avoid serializing. That whole path is gone: web images are
// ordinary `future-boundary` runs now, and `async-pump` forks a strand per
// want, so the floors overlap by construction -- the same reason native never
// had the bug. This test moves down to `async-pump` to keep pinning it there:
// three wants kicked together, each with its own floor, must cost about ONE
// floor in total.
//
// If this ever fails, suspect the pump stopped forking per want (running each
// inline, or draining them one at a time) -- that is the shape that regresses.
module web-image-settle

import std/core/unsafe
import std/async
import std/num/float64
import std/time/duration
import std/time/timer
import ui/state
import ui/async

val passed : ref<global,int> = unsafe-total{ ref(0) }
val failed : ref<global,int> = unsafe-total{ ref(0) }

fun check( name : string, cond : bool ) : ioc ()
  if cond
    then passed := !passed + 1
    else
      failed := !failed + 1
      println("FAIL: " ++ name)

fun ms() : ndet float64
  ticks().milli-seconds.float64

val floor-ms = 200

// a run that resolves immediately: all the elapsed time is the floor
fun quick-run() : <async,ioc,exn> any
  erase("done")

fun is-done( id : int ) : <uistate,ioc> bool
  match async-phase(id)
    Just(Async-entry(_, RDone(_))) -> True
    _                              -> False

// kick `ids` as one batch and return how long until the LAST of them settles.
// Polled with a BOUNDED loop rather than a recursive one: a recursive poller
// is `div`, which does not unify with `forking`'s body row here.
fun batch-elapsed( ch : channel<async-want>, ids : list<int> ) : <async,uistate,ioc> float64
  ids.foreach fn(i)
    set-async(i, Async-entry(1, RPending))
  val t0 = ms()
  ids.foreach fn(i)
    ch.emit-io(Async-want(i, 1, quick-run, floor-ms.milli-seconds))
  val done-at : ref<global,float64> = ref(-1.0)
  list(1, floor-ms).foreach fn(_)          // up to 5*floor of 5ms steps
    if !done-at < 0.0 then
      if ids.all(is-done)
        then done-at := ms() - t0
        else wait(5.milli-seconds)
  if !done-at < 0.0 then ms() - t0 else !done-at

pub fun main()
  with-uistate
    val ch : channel<async-want> = channel()
    install-async-channel(ch)
    forking fn(fork)
      fork( fn() async-pump(fork) )
      wait(20.milli-seconds)   // let the pump strand reach its `receive`

      // (1) ONE want still gets its full anti-flicker floor -- batching must
      // not turn min-load off
      val one = batch-elapsed(ch, [1])
      check("a single want holds the min-load floor (" ++ one.int.show ++ "ms)",
            one >= (floor-ms - 40).float64)

      // (2) THREE kicked together cost ONE floor, not three. Serialized holds
      // took ~600ms (200 + 200 + 200) and settled the row one at a time. The
      // ceiling is well under two floors, so this can only pass by
      // overlapping -- not by being fast.
      val three = batch-elapsed(ch, [11, 12, 13])
      check("three wants kicked together cost one floor (" ++ three.int.show ++ "ms)",
            three < (floor-ms * 2 - 40).float64)

      // (3) all three really settled (the batch is not fast because it
      // dropped work)
      check("all three wants reached RDone", [11, 12, 13].all(is-done))

      println("WEB-IMAGE-SETTLE: " ++ (!passed).show ++ "/" ++ (!passed + !failed).show ++ " passed")
      if !failed > 0 then println("WEB-IMAGE-SETTLE: FAILED (" ++ (!failed).show ++ " failures)")
