/*---------------------------------------------------------------------------
  A deterministic, pure-Koka event-loop backend for `std/async`.

  A discrete-event simulator (virtual clock + sorted one-shot timer queue)
  implementing the same 4-function interface as the libuv (`api/uv/evloop`) and
  web (`api/web/evloop`) backends. Selected with `--buildcfg sim` via the
  conditional import in `std/async/async`; compiles to C under the normal libc
  target with no libuv dependency.

  Purpose: demonstrate that `std/async`'s scheduler is swappable under unchanged
  program code, and provide the substrate for deterministic testing / fault
  injection. The whole loop is plain Koka data in a `ref`, so it can later be
  snapshot/forked for multi-shot (bounded-model-checking) exploration.
---------------------------------------------------------------------------*/
module sim/evloop

import std/num/int64
import std/core/unsafe   // unsafe-total

// Stash the (typed) sim loop inside the opaque `any` that the async core threads
// around. Identity box-casts: a boxed `a` and `any` share the same runtime
// representation, so `#1` passes the box through unchanged. This is the only FFI
// here — the scheduler logic below is pure Koka.
extern to-any( x : a ) : any
  c inline "#1"
extern from-any( x : any ) : a
  c inline "#1"

// A one-shot timer: fire `cb` at virtual time `time` (ms); `id` allows cancel.
struct timer
  tid  : int
  time : int64
  cb   : () -> ioc ()

// The loop: pending timers (ascending by `time`), the virtual clock, id source.
struct sim
  pending : list<timer>
  now     : int64
  next-id : int

alias loopref = ref<global,sim>

// Insert keeping ascending time order; equal times preserve FIFO (stable).
fun insert( ts : list<timer>, t : timer ) : list<timer>
  match ts
    Cons(h, rest) -> if t.time < h.time then Cons(t, Cons(h, rest)) else Cons(h, insert(rest, t))
    Nil           -> [t]

// ---- the 4-function backend interface --------------------------------------

pub fun event-loop-init() : any
  unsafe-total
    val r : loopref = ref(Sim([], zero, 0))
    to-any(r)

pub fun timer-setup( evloop : any, millisecs : int64, cb : () -> ioc () ) : ioc error<() -> ioc ()>
  val r : loopref = from-any(evloop)
  val s   = !r
  val due = s.now + (if millisecs < zero then zero else millisecs)
  val id  = s.next-id
  r := s( pending = s.pending.insert(Timer(id, due, cb)), next-id = id + 1 )
  Ok( fn() cancel(r, id) )

pub fun immediate-setup( evloop : any, cb : () -> ioc () ) : ioc error<() -> ioc ()>
  timer-setup(evloop, zero, cb)

// Drive the loop deterministically: pop the earliest timer, advance the virtual
// clock to it, fire it (which may enqueue more), until nothing is pending.
pub fun event-loop-run( evloop : any ) : ()
  unsafe-total
    drain(from-any(evloop))

// ---- internals -------------------------------------------------------------

fun cancel( r : loopref, target : int ) : ioc ()
  val s = !r
  r := s( pending = s.pending.filter(fn(t) t.tid != target) )

fun drain( r : loopref ) : <ioc,div> ()
  val s = !r
  match s.pending
    Nil           -> ()
    Cons(t, rest) ->
      r := s( pending = rest, now = if t.time > s.now then t.time else s.now )
      (t.cb)()
      drain(r)
