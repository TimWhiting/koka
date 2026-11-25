/*---------------------------------------------------------------------------
  Copyright 2026, Microsoft Research, Daan Leijen, Tim Whiting

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// std/async event loop for `--target=wasi-web` (wasm32-wasip1 core module, no
// JSPI/asyncify). The wasm guest never blocks: `event-loop-run` just marks the
// kklib context as "keep alive" and returns; the JS host (see
// support/wasi-web/run.mjs and support/wasi-web/timers.js) later re-enters
// the same live wasm instance through the `koka:async/dispatch` /
// `koka:async/loop-done` wasm exports whenever a real `setTimeout` fires.
// Same Koka-level API as `api/web/evloop.kk` (emscripten) and
// `api/uv/evloop.kk` (libuv/node) so `std/async` is unchanged.
//
// C stays at the fringe (same discipline as the framework's dom.c): evloop.c
// stores exactly ONE `kk_function_t` -- the dispatcher registered once below
// -- plus the loop refcount (a plain counter, shared with other modules via
// `kk_wasiweb_loop_ref/_unref`, e.g. DOM listeners). The id -> (host handle,
// callback) table and the dispose logic are ordinary Koka in this module.
module wasiweb/evloop

import std/num/int64
import std/num/int32
import std/core/unsafe

extern import
  c file "evloop.c"

pub extern event-loop-init() : any
  c "kk_wasiweb_loop_init"

pub extern event-loop-run(evloop : any) : ()
  c "kk_wasiweb_loop_run"

// ----------------------------------------------------------------
// fringe externs (thin ABI forwarding; see evloop.c)

// host setTimeout: returns the host's timer handle (used to cancel)
extern set-timeout-raw( timer-id : int, millisecs : int64 ) : ioc int32
  c "kk_wasiweb_set_timeout"

extern clear-timeout-raw( hnd : int32 ) : ioc ()
  c "kk_wasiweb_clear_timeout"

// the single stored dispatcher (called once, at module init, below)
extern register-dispatcher( dispatch : (int) -> ioc () ) : ioc ()
  c "kk_wasiweb_register_dispatcher"

// loop refcount: pending-callback count consulted by the `loop-done` export
extern loop-ref() : ioc ()
  c "kk_wasiweb_loop_ref"

extern loop-unref() : ioc ()
  c "kk_wasiweb_loop_unref"

// ----------------------------------------------------------------
// the timer table, in Koka: id -> (host handle, callback). C never stores
// callbacks beyond the single dispatcher.

val timers : ref<global,list<(int, (int32, () -> ioc ()))>> = unsafe-total{ ref([]) }

// fresh ids for this module's timers (0 is never used)
val next-id : ref<global,int> = unsafe-total{ ref(1) }

fun fresh-id() : ioc int
  val id = !next-id
  next-id := id + 1
  id

// remove and return the entry for `id`, if present
fun take( id : int ) : ioc maybe<(int32, () -> ioc ())>
  match (!timers).lookup( fn(i) i == id )
    Nothing -> Nothing
    Just(entry) ->
      timers := (!timers).filter( fn(kv) kv.fst != id )
      Just(entry)

// every host timer firing routes through here (via the C dispatcher)
fun dispatch( id : int ) : ioc ()
  match take(id)
    Nothing -> ()          // already disposed/canceled -- stray fire, ignore
    Just((_, cb)) ->
      loop-unref()
      cb()

val register-dispatcher-once : () = unsafe-total{ register-dispatcher(dispatch) }

// ----------------------------------------------------------------
// the std/async evloop API

pub fun timer-setup( evloop : any, millisecs : int64, cb : () -> ioc () ) : ioc error<() -> ioc ()>
  val id = fresh-id()
  val hnd = set-timeout-raw(id, if millisecs < 0.int64 then 0.int64 else millisecs)
  timers := Cons((id, (hnd, cb)), !timers)
  loop-ref()
  val dispose = fn()
    match take(id)
      Nothing -> ()        // already fired (or disposed twice) -- nothing to cancel
      Just((h, _)) ->
        clear-timeout-raw(h)
        loop-unref()
  Ok(dispose)

pub fun immediate-setup( evloop : any, cb : () -> ioc () ) : ioc error<() -> ioc ()>
  timer-setup(evloop, 0.int64, cb)
