/*---------------------------------------------------------------------------
  Copyright 2023 Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

module uv/event-loop

import std/core/cextern
import std/num/int32

import uv/generated
import uv/utils
pub import uv/timer

extern import
  c { conan="libuv[>=1.47.0]"; vcpkg="libuv"; library="uv" }
// TODO: wasm {}

extern import
  c file "inline/event-loop"
  cs file "inline/event-loop.cs"

// Handles a uv loop
pub fun default-event-loop(action)
  if host() == "libc" then
    handle-loop(action)
  else // TODO: Support event loop on other platforms
    action()

val @initialize = init-uv-alloc()

// Runs a UV loop
fun handle-loop(action)
  init-loop()
  val res = action() 
  run-loop()
  close-loop()
  res

extern run-loop(): io-event ()
  c "kk_uv_loop_run"
  wasm "kk_emscripten_loop_run"
  js inline ""
  cs inline ""

extern init-loop(): io-event ()
  c "kk_uv_loop_init"
  wasm inline "kk_Unit"
  js inline ""
  cs inline ""

// initializes only the allocators (not an event loop)
// needed for some file operations which alloc - kk_uv_fs_mkdtemp, kk_uv_fs_mkstemp
pub extern init-uv-alloc(): ()
  c "kk_uv_alloc_init"
  wasm inline "kk_Unit"
  cs inline ""
  js inline ""

extern close-loop(): io-event ()
  c "kk_uv_loop_close"
  wasm inline "kk_Unit"
  cs inline ""
  js inline ""

pub extern set-timeout( cb : () -> io-event (), ms : int32 ) : io-event any
  cs "_Async.SetTimeout"
  js "setTimeout"
  c "kk_set_timeout"

pub extern clear-timeout( tid : any) : io-event ()
  cs "_Async.ClearTimeout"
  js "clearTimeout"
  c "kk_clear_timeout" 

pub extern ptr/close(hnd: intptr_t, callback: () -> io-event ()): io-event ()
  c "kk_uv_close"
  wasm inline "kk_Unit"
  cs inline ""
  js inline ""