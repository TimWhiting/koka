/*---------------------------------------------------------------------------
  Copyright 2026, Microsoft Research, Daan Leijen, Tim Whiting

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Event loop for bare-metal targets (KK_BAREMETAL): one core and no OS.
// Selected with `--buildcfg=baremetal`.
//
// Timers and immediates are kept here, in Koka. The board supplies only a
// clock, an idle instruction, and a poll hook for its own event sources
// (DMA, USB, ...), as C functions that override the weak defaults in
// evloop.c.
module baremetal/evloop

import std/num/int64
import std/core/unsafe

extern import
  c file "evloop.c"

// Microseconds from a monotonic clock.
extern now-us() : ndet int64
  c inline "kk_bm_now_us()"

// Let the board service its own event sources. Returns `True` while any
// request is outstanding (so the loop must keep running).
extern board-poll() : ioc bool
  c inline "kk_bm_board_poll(kk_context())"

// Sleep until the next interrupt, or until `until-us` at the latest.
extern board-idle( until-us : int64 ) : ioc ()
  c inline "kk_bm_board_idle(#1)"

extern null-loop() : any
  c inline "kk_box_null()"

struct timer
  tid : int
  due : int64
  cb  : () -> ioc ()

val timers  : ref<global,list<timer>> = unsafe-total { ref([]) }
val next-id : ref<global,int> = unsafe-total { ref(0) }

pub fun event-loop-init() : any
  null-loop()

// Keep timers sorted by due time; equal times run in the order they were set.
fun insert( t : timer, ts : list<timer> ) : list<timer>
  match ts
    Cons(t2, rest) | t2.due <= t.due -> Cons(t2, insert(t, rest))
    _ -> Cons(t, ts)

pub fun timer-setup( evloop : any, millisecs : int64, cb : () -> ioc () ) : ioc error<() -> ioc ()>
  val new-id = !next-id
  next-id := new-id + 1
  timers := insert(Timer(new-id, now-us() + millisecs * 1000.int64, cb), !timers)
  Ok(fn() timers := (!timers).filter(fn(t : timer) t.tid != new-id))

pub fun immediate-setup( evloop : any, cb : () -> ioc () ) : ioc error<() -> ioc ()>
  timer-setup(evloop, 0.int64, cb)

// Run until no timers are left and the board reports nothing outstanding.
pub fun event-loop-run( evloop : any ) : ioc ()
  fun step() : ioc bool
    val outstanding = board-poll()
    match !timers
      Cons(t, rest) ->
        if t.due <= now-us() then
          timers := rest
          (t.cb)()
        else board-idle(t.due)
        True
      Nil ->
        if outstanding then board-idle(now-us() + 1000.int64)
        outstanding
  while { step() } { () }
