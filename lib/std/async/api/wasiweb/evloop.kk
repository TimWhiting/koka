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
// `koka:async/loop-done` wasm exports (plain `export_name` attributes on the
// C functions in evloop.c -- no wit-bindgen, no component model) whenever a
// real `setTimeout` fires. Same Koka-level API as `api/web/evloop.kk`
// (emscripten) and `api/uv/evloop.kk` (libuv/node) so `std/async` is unchanged.
module wasiweb/evloop

import std/num/int64

extern import
  c file "evloop.c"

pub extern event-loop-init() : any
  c "kk_wasiweb_loop_init"

pub extern event-loop-run(evloop : any) : ()
  c "kk_wasiweb_loop_run"

pub extern timer-setup( evloop : any, millisecs : int64, cb : () -> ioc () ) : ioc error<() -> ioc ()>
  c "kk_wasiweb_timer_setup"

pub extern immediate-setup( evloop : any, cb : () -> ioc () ) : ioc error<() -> ioc ()>
  c "kk_wasiweb_immediate_setup"
