/*---------------------------------------------------------------------------
  A Koka-native event-loop backend for `std/async` over macOS/BSD `kqueue`.

  Implements the same 4-function interface as the libuv (`api/uv/evloop`) and sim
  (`api/sim/evloop`) backends, but the *reactor itself* is Koka: the timer queue
  (and, later, the fd -> continuation table) are plain Koka data in a `ref`; only
  `kqueue`/`kevent` and a monotonic clock are FFI. Selected with `--buildcfg kq`.

  Milestone 1 (this file): timers, driven by real `kevent` waits (real wall-clock
  time, unlike the virtual-time sim backend). UDP readiness (EVFILT_READ +
  recvfrom) is the next milestone — the reactor state is already shaped to hold
  fd watchers alongside timers.

  Why this exists: it shrinks the non-forkable surface to exactly the kernel fd
  state (the reactor bookkeeping becomes forkable Koka data) and unifies the real
  and sim backends under one reactor. See PAPER.md.
---------------------------------------------------------------------------*/
module kq/evloop

import std/num/int32
import std/num/int64
import std/core/unsafe   // unsafe-total

extern import
  c file "kq-evloop.c"

// Stash the typed reactor in the opaque `any` (identity box-cast; see api/sim/evloop).
extern to-any( x : a ) : any
  c inline "#1"
extern from-any( x : any ) : a
  c inline "#1"

extern kq-create() : int32
  c "kk_kq_create"
// wait up to `millis` ms for a kqueue event; returns #ready (0 on timeout).
extern kq-wait( kq : int32, millis : int64 ) : int32
  c "kk_kq_wait"
// monotonic clock in ms.
extern now-ms() : int64
  c "kk_now_ms"

// A one-shot timer: fire `cb` at absolute monotonic time `time` (ms); `tid` cancels.
struct timer
  tid  : int
  time : int64
  cb   : () -> ioc ()

// The reactor: the kqueue fd, pending timers (ascending by `time`), an id source.
struct reactor
  kq      : int32
  pending : list<timer>
  next-id : int

alias rref = ref<global,reactor>

// Insert keeping ascending time order; equal times preserve FIFO (stable).
fun insert( ts : list<timer>, t : timer ) : list<timer>
  match ts
    Cons(h, rest) -> if t.time < h.time then Cons(t, Cons(h, rest)) else Cons(h, insert(rest, t))
    Nil           -> [t]

// ---- the 4-function backend interface --------------------------------------

pub fun event-loop-init() : any
  unsafe-total
    to-any( ref(Reactor(kq-create(), [], 0)) )

pub fun timer-setup( evloop : any, millisecs : int64, cb : () -> ioc () ) : ioc error<() -> ioc ()>
  val r : rref = from-any(evloop)
  val s   = !r
  val due = now-ms() + (if millisecs < int64/zero then int64/zero else millisecs)
  val id  = s.next-id
  r := s( pending = s.pending.insert(Timer(id, due, cb)), next-id = id + 1 )
  Ok( fn() cancel(r, id) )

pub fun immediate-setup( evloop : any, cb : () -> ioc () ) : ioc error<() -> ioc ()>
  timer-setup(evloop, zero, cb)

pub fun event-loop-run( evloop : any ) : ()
  unsafe-total
    drive(from-any(evloop))

// ---- internals -------------------------------------------------------------

fun cancel( r : rref, target : int ) : ioc ()
  val s = !r
  r := s( pending = s.pending.filter(fn(t) t.tid != target) )

// Fire due timers; otherwise block in `kevent` until the earliest is due (or an
// fd event arrives, once fd watchers exist). Milestone 1: empty queue = done.
fun drive( r : rref ) : <ioc,div> ()
  val s = !r
  match s.pending
    Nil           -> ()
    Cons(t0, rest) ->
      val now = now-ms()
      if t0.time <= now then
        r := s( pending = rest )
        (t0.cb)()
        drive(r)
      else
        val _ready = kq-wait(s.kq, t0.time - now)
        drive(r)
