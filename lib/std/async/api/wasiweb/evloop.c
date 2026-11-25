/*---------------------------------------------------------------------------
  Copyright 2026, Microsoft Research, Daan Leijen, Tim Whiting

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// #include <kklib.h>  -- already included (this file is textually pasted into
// the module's own generated .c, which includes kklib.h at the top, same
// convention as api/web/evloop.c).

// The C fringe of the wasi-web event loop (see evloop.kk for the logic):
// plain wasm core-module imports/exports, the keep-alive flag, the loop
// refcount (a counter shared across modules -- DOM listeners bump it too),
// and storage for exactly ONE `kk_function_t`: the dispatcher evloop.kk
// registers at module init. The id -> (host handle, callback) timer table
// lives in Koka (evloop.kk), not here -- same discipline as the framework's
// dom.c: C never stores callbacks beyond the single dispatcher.

// The `koka:async/timers` host imports as plain import attributes; clang
// lowers these to wasm import sections read directly by the host's
// `importObject` in run.mjs/index.html: see support/wasi-web/timers.js.
__attribute__((import_module("koka:async/timers"), import_name("set-timeout")))
extern uint32_t koka_async_timers_set_timeout(uint64_t timer_id, uint64_t millisecs);
__attribute__((import_module("koka:async/timers"), import_name("clear-timeout")))
extern void     koka_async_timers_clear_timeout(uint32_t handle);


//----------------------------------------------
// keep-alive flag
//
// Keeps the runtime context (and its heap) alive past the generated `main`'s
// normal teardown/exit path. This is *only* meaningful for `--target=wasi-web`
// (wasm32-wasip1 core module, no JSPI): `event-loop-run`/`kk_wasiweb_loop_ref`
// set this flag and return synchronously to the JS host while async callbacks
// may still be dispatched later into the *same* wasm instance, so the context
// must not be freed. This used to live in kklib (as a config-specific
// `#if defined(__wasi__)` hook) but kklib must stay configuration-neutral --
// every other C target (host, js, emscripten, `--target=wasi`) has no use
// for it at all, so it lives here instead, in the one file that actually
// implements the wasi-web inverted event loop. The generated `main` (see
// `genMain` in src/Backend/C/FromCore.hs) declares `kk_main_keepalive` as a
// weak symbol and only calls it for `--target=wasi-web`; on that target,
// plain wasm-ld resolves the weak reference to this (non-weak) definition
// whenever this file's translation unit is linked in (i.e. the program
// transitively imports `std/async` on wasi-web), or to null (never called,
// since the guard also checks the symbol address) when it is not (e.g. a
// synchronous wasi-web program that never touches `std/async`).
//----------------------------------------------

static bool kk_wasiweb_keepalive; // = false

void kk_main_set_keepalive(bool enable, kk_context_t* ctx) {
  kk_unused(ctx);
  kk_wasiweb_keepalive = enable;
}

bool kk_main_keepalive(kk_context_t* ctx) {
  kk_unused(ctx);
  return kk_wasiweb_keepalive;
}


//----------------------------------------------
// loop refcount
//
// The number of outstanding host-driven callbacks (pending timers from
// evloop.kk, live DOM listeners from the framework's dom.c, ...), consulted
// by the `koka:async/loop-done` export the JS host polls. A plain counter --
// no callbacks, no table. Non-static so independently-compiled wasi-web
// modules (e.g. samples/wasi-web/framework/dom.c) can bump the same count.
//----------------------------------------------

static int64_t kk_wasiweb_refcount; // = 0

// lazily "initializes" (there is nothing left to allocate) and also marks the
// kklib context keep-alive: any module registering a host-driven callback
// needs both.
void kk_wasiweb_loop_ref(kk_context_t* ctx) {
  kk_wasiweb_refcount++;
  kk_main_set_keepalive(true, ctx);
}

void kk_wasiweb_loop_unref(kk_context_t* ctx) {
  kk_unused(ctx);
  if (kk_wasiweb_refcount > 0) kk_wasiweb_refcount--;
}

// The Koka-level `event-loop` handle is opaque and unused on this target
// (the loop state is the module-level counter above); hand back a unit box.
kk_box_t kk_wasiweb_loop_init(kk_context_t* ctx) {
  kk_unused(ctx);
  return kk_unit_box(kk_Unit);
}

void kk_wasiweb_loop_run(kk_box_t evloop, kk_context_t* ctx) {
  kk_main_set_keepalive(true, ctx);  // keep the context/heap alive past `main`'s normal teardown
  kk_box_drop(evloop,ctx);
  // returns immediately: the JS host drives further progress by calling the
  // `dispatch`/`loop-done` wasm exports from its own (real) event loop.
}


//----------------------------------------------
// the one stored dispatcher + thin timer forwarding (logic in evloop.kk)
//----------------------------------------------

static bool          kk_wasiweb_dispatcher_set; // = false
static kk_function_t kk_wasiweb_dispatcher;     // valid iff kk_wasiweb_dispatcher_set

void kk_wasiweb_register_dispatcher(kk_function_t dispatch, kk_context_t* ctx) {
  kk_unused(ctx);
  kk_wasiweb_dispatcher = dispatch;
  kk_wasiweb_dispatcher_set = true;
}

int32_t kk_wasiweb_set_timeout(kk_integer_t timer_id, int64_t millisecs, kk_context_t* ctx) {
  uint64_t id = (uint64_t)kk_integer_clamp64(timer_id, ctx);
  return (int32_t)koka_async_timers_set_timeout(id, (uint64_t)millisecs);
}

void kk_wasiweb_clear_timeout(int32_t handle, kk_context_t* ctx) {
  kk_unused(ctx);
  koka_async_timers_clear_timeout((uint32_t)handle);
}


//----------------------------------------------
// wasm core-module exports: the JS host (run.mjs / index.html) re-enters the
// guest through `dispatch` whenever a real host timer fires, and polls
// `loop-done` to decide whether pending work remains.
//----------------------------------------------

__attribute__((export_name("koka:async/dispatch")))
void kk_wasiweb_export_dispatch(uint64_t timer_id) {
  kk_context_t* ctx = kk_get_context();
  if (!kk_wasiweb_dispatcher_set) return;
  kk_function_t dispatch = kk_wasiweb_dispatcher;
  kk_function_dup(dispatch, ctx);  // fires repeatedly, never consumed
  kk_integer_t id = kk_integer_from_uint64(timer_id, ctx);
  kk_function_call(kk_unit_t, (kk_function_t, kk_integer_t, kk_context_t*), dispatch, (dispatch, id, ctx), ctx);
  // `dispatch` is a wasm core-module *export* called directly by the JS host,
  // after the guest's `_start` already returned (and already flushed stdio
  // via its normal `atexit` machinery). Any output the callback just produced
  // would otherwise sit unflushed until a process exit that never happens on
  // wasi-web -- so flush explicitly on every re-entry.
  fflush(NULL);
}

__attribute__((export_name("koka:async/loop-done")))
bool kk_wasiweb_export_loop_done(void) {
  return (kk_wasiweb_refcount == 0);
}
