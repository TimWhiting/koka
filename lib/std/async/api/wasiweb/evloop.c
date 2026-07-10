/*---------------------------------------------------------------------------
  Copyright 2026, Microsoft Research, Daan Leijen, Tim Whiting

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// #include <kklib.h>  -- already included (this file is textually pasted into
// the module's own generated .c, which includes kklib.h at the top, same
// convention as api/web/evloop.c).

// The `koka:async/timers` host imports, as plain wasm core-module import
// attributes (Rev 3: `--target=wasi-web` is a plain wasm32-wasip1 core
// module, not a wasip2 component -- no wit-bindgen, no jco; the module/name
// strings are kept identical to the old WIT interface so the JS glue
// (support/wasi-web/timers.js) reads the same either way). clang lowers
// these to wasm import sections read directly by the host's `importObject`
// in run.mjs/index.html: `importObject["koka:async/timers"]["set-timeout"]`
// etc. -- see support/wasi-web/run.mjs.
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
// dispose function closure (mirrors api/web/evloop.c)
//----------------------------------------------

typedef void (kk_wasiweb_dispose_fun_t)(void* p, void* arg, kk_context_t* ctx);

struct kk_wasiweb_dispose_fun_closure_s {
  struct kk_function_s _base;
  void* p;
  void* arg;
  kk_wasiweb_dispose_fun_t* dispose;
};

static kk_box_t kk_wasiweb_dispose_fun(kk_function_t _fself, kk_context_t* ctx) {
  struct kk_wasiweb_dispose_fun_closure_s* _self = kk_function_as(struct kk_wasiweb_dispose_fun_closure_s*, _fself, ctx);
  void* p = _self->p;
  void* arg = _self->arg;
  kk_wasiweb_dispose_fun_t* dispose = _self->dispose;
  kk_function_drop(_fself,ctx);
  dispose(p,arg,ctx);
  return kk_unit_box(kk_Unit);
}

static kk_function_t kk_wasiweb_dispose_fun_create(void* p, void* arg, kk_wasiweb_dispose_fun_t* dispose, kk_context_t* ctx) {
  struct kk_wasiweb_dispose_fun_closure_s* _self = kk_function_alloc_as(struct kk_wasiweb_dispose_fun_closure_s, 1, ctx);
  _self->_base.fun = kk_kkfun_ptr_box(&kk_wasiweb_dispose_fun, ctx);
  _self->p = p;
  _self->arg = arg;
  _self->dispose = dispose;
  return kk_datatype_from_base(&_self->_base, ctx);
}

static kk_std_core_exn__error kk_wasiweb_result_ok( kk_box_t val, kk_context_t* ctx ) {
  return kk_std_core_types__new_Ok(val,ctx);
}

static kk_std_core_exn__error kk_wasiweb_result_dispose( void* req, void* arg, kk_wasiweb_dispose_fun_t* dispose, kk_context_t* ctx ) {
  kk_function_t dispose_fun = kk_wasiweb_dispose_fun_create(req,arg,dispose,ctx);
  return kk_wasiweb_result_ok(kk_function_box(dispose_fun,ctx),ctx);
}


//----------------------------------------------
// event loop
//
// Single-context/single-threaded wasm: the loop is reachable from the wasm
// `dispatch`/`loop-done` exports (which carry no Koka-level handle at all --
// the WIT world only passes an opaque `u64 timer-id`) through one static
// pointer, `kk_wasiweb_loop`. Pending callbacks are kept in a growable array
// keyed by a `u64` id (never a raw pointer -- ids are the only thing that
// crosses the wasm<->JS boundary as `koka:async/timers` arguments).
//----------------------------------------------

typedef struct kk_wasiweb_cb_entry_s {
  uint64_t      id;           // 0 == free slot
  uint32_t      host_handle;  // handle returned by `set-timeout`, used to `clear-timeout` on dispose
  kk_function_t cb;
} kk_wasiweb_cb_entry_t;

typedef struct kk_wasiweb_loop_s {
  int64_t                 refcount;  // number of outstanding (not yet fired/disposed) callbacks
  uint64_t                next_id;   // id counter (starts at 1; 0 marks a free slot)
  kk_wasiweb_cb_entry_t*   entries;
  size_t                   count;
  size_t                   capacity;
} kk_wasiweb_loop_t;

typedef kk_box_t kk_wasiweb_loop_box_t;

// The event loop is a program-lifetime singleton on wasi-web (there is only
// ever one, allocated once by `event-loop-init` at program start); we never
// actually free it, matching the fact the whole kklib context/heap is kept
// alive for the life of the wasm instance on this target (see
// `kk_main_keepalive` above) -- freeing it would race with a `dispatch`
// re-entry after the Koka-level "evloop" value nominally goes out of scope.
static kk_wasiweb_loop_t* kk_wasiweb_loop = NULL;

static void kk_wasiweb_loop_noop_free(void* p, kk_block_t* block, kk_context_t* ctx) {
  kk_unused(p);
  kk_unused(block);
  kk_unused(ctx);
  // deliberately not freed, see comment on `kk_wasiweb_loop` above.
}

static void kk_wasiweb_loop_ensure(kk_context_t* ctx) {
  if (kk_wasiweb_loop == NULL) {
    kk_wasiweb_loop_t* loop = (kk_wasiweb_loop_t*)kk_zalloc(sizeof(kk_wasiweb_loop_t),ctx);
    loop->next_id = 1;
    kk_wasiweb_loop = loop;
  }
}

kk_wasiweb_loop_box_t kk_wasiweb_loop_init(kk_context_t* ctx) {
  kk_wasiweb_loop_ensure(ctx);
  return kk_cptr_raw_box(&kk_wasiweb_loop_noop_free, kk_wasiweb_loop, ctx);
}

// Non-static helpers so a second, independently wit-bindgen'd/compiled
// wasi-web module (e.g. samples/wasi-web/dom/dom.c) can hold the same evloop
// singleton alive without reaching into this file's static `kk_wasiweb_loop`
// -- there is only ever one evloop per program, and every wasi-web module
// that registers host-driven callbacks (timers, DOM listeners, ...) needs to
// bump the same refcount so `loop-done` (and node's `loopDone()` poll, see
// support/wasi-web/run.mjs) correctly reflects "any pending callback exists,
// from any module". `kk_wasiweb_loop_ref` lazily initializes the loop (a
// caller need not itself call `event-loop-init`/`std/async`) and also marks
// the kklib context "keep alive", mirroring what `kk_wasiweb_loop_run` does
// for the `std/async`-driven path.
void kk_wasiweb_loop_ref(kk_context_t* ctx) {
  kk_wasiweb_loop_ensure(ctx);
  kk_wasiweb_loop->refcount++;
  kk_main_set_keepalive(true, ctx);
}

void kk_wasiweb_loop_unref(kk_context_t* ctx) {
  if (kk_wasiweb_loop != NULL && kk_wasiweb_loop->refcount > 0) kk_wasiweb_loop->refcount--;
}

void kk_wasiweb_loop_run(kk_wasiweb_loop_box_t evloop, kk_context_t* ctx) {
  kk_main_set_keepalive(true, ctx);  // keep the context/heap alive past `main`'s normal teardown
  kk_box_drop(evloop,ctx);
  // returns immediately: the JS host drives further progress by calling the
  // `dispatch`/`loop-done` wasm exports from its own (real) event loop.
}


//----------------------------------------------
// callback table
//----------------------------------------------

static kk_wasiweb_cb_entry_t* kk_wasiweb_entry_alloc(uint64_t id, kk_context_t* ctx) {
  kk_wasiweb_loop_t* loop = kk_wasiweb_loop;
  for (size_t i = 0; i < loop->count; i++) {
    if (loop->entries[i].id == 0) {
      loop->entries[i].id = id;
      return &loop->entries[i];
    }
  }
  if (loop->count == loop->capacity) {
    size_t newcap = (loop->capacity == 0 ? 8 : loop->capacity * 2);
    loop->entries = (kk_wasiweb_cb_entry_t*)kk_realloc(loop->entries, newcap * sizeof(kk_wasiweb_cb_entry_t), ctx);
    loop->capacity = newcap;
  }
  kk_wasiweb_cb_entry_t* entry = &loop->entries[loop->count++];
  entry->id = id;
  return entry;
}

static kk_wasiweb_cb_entry_t* kk_wasiweb_entry_find(uint64_t id) {
  kk_wasiweb_loop_t* loop = kk_wasiweb_loop;
  if (loop == NULL) return NULL;
  for (size_t i = 0; i < loop->count; i++) {
    if (loop->entries[i].id == id) return &loop->entries[i];
  }
  return NULL;
}


//----------------------------------------------
// timer
//----------------------------------------------

static inline void kk_wasiweb_function_call0( kk_function_t f, kk_context_t* ctx ) {
  kk_function_call(kk_unit_t, (kk_function_t, kk_context_t*), f, (f, ctx), ctx);  // drops f
}

// Called by `kk_wasiweb_export_dispatch` (the `koka:async/dispatch` wasm
// export below, a plain `export_name` attribute -- no wit-bindgen/jco
// trampoline any more, see Rev 3) when the JS host's
// real `setTimeout` fires; the wasm export carries only the opaque `timer_id`.
void kk_wasiweb_dispatch(uint64_t timer_id) {
  kk_context_t* ctx = kk_get_context();
  kk_wasiweb_cb_entry_t* entry = kk_wasiweb_entry_find(timer_id);
  if (entry == NULL) return;  // already disposed/canceled
  kk_function_t cb = entry->cb;
  entry->id = 0;  // free the slot
  if (kk_wasiweb_loop->refcount > 0) kk_wasiweb_loop->refcount--;
  kk_wasiweb_function_call0(cb,ctx);  // drops cb
  // `dispatch` is a wasm core-module *export* called directly by the JS host
  // (run.mjs / index.html), not a re-entry through wasi-libc's `_start`/`exit`
  // path: it happens after the guest's `_start` already returned once (and
  // already flushed stdio via its normal `atexit` machinery). Any output the
  // callback just produced (`fputs`-buffered stdio, see kklib's `kk_println`)
  // would otherwise sit unflushed until *another* real process exit, which
  // never happens on wasi-web (the JS host just drops the instance once
  // `loop-done` reports true) -- so flush explicitly on every re-entry.
  fflush(NULL);
}

bool kk_wasiweb_loop_done(void) {
  return (kk_wasiweb_loop == NULL || kk_wasiweb_loop->refcount == 0);
}

typedef struct kk_wasiweb_timer_s {
  uint64_t id;
} kk_wasiweb_timer_t;

static void kk_wasiweb_timer_dispose(void* ptimer, void* arg, kk_context_t* ctx) {
  kk_unused(arg);
  kk_wasiweb_timer_t* t = (kk_wasiweb_timer_t*)ptimer;
  if (t==NULL) return;
  kk_wasiweb_cb_entry_t* entry = kk_wasiweb_entry_find(t->id);
  if (entry != NULL) {
    koka_async_timers_clear_timeout(entry->host_handle);
    kk_function_drop(entry->cb,ctx);
    entry->id = 0;
    if (kk_wasiweb_loop->refcount > 0) kk_wasiweb_loop->refcount--;
  }
  kk_free(t,ctx);
}

kk_std_core_exn__error kk_wasiweb_timer_setup(kk_wasiweb_loop_box_t evloop, int64_t millisecs, kk_function_t cb, kk_context_t* ctx) {
  kk_box_drop(evloop,ctx);  // the loop is reached through the static `kk_wasiweb_loop` singleton, not this handle
  if (millisecs < 0) millisecs = 0;
  uint64_t id = kk_wasiweb_loop->next_id++;
  kk_wasiweb_cb_entry_t* entry = kk_wasiweb_entry_alloc(id, ctx);
  entry->cb = cb;
  entry->host_handle = koka_async_timers_set_timeout(id, (uint64_t)millisecs);
  kk_wasiweb_loop->refcount++;

  kk_wasiweb_timer_t* t = (kk_wasiweb_timer_t*)kk_zalloc(sizeof(kk_wasiweb_timer_t),ctx);
  t->id = id;
  return kk_wasiweb_result_dispose((void*)t,NULL,&kk_wasiweb_timer_dispose,ctx);
}

kk_std_core_exn__error kk_wasiweb_immediate_setup(kk_wasiweb_loop_box_t loop, kk_function_t cb, kk_context_t* ctx) {
  return kk_wasiweb_timer_setup(loop,0,cb,ctx);
}


//----------------------------------------------
// wasm core-module exports: the JS host (run.mjs / index.html) re-enters the
// guest through `dispatch` whenever a real host timer fires, and polls
// `loop-done` to decide whether pending work remains. Plain export-name
// attributes replace the old wit-bindgen-generated trampolines (Rev 3).
//----------------------------------------------

__attribute__((export_name("koka:async/dispatch")))
void kk_wasiweb_export_dispatch(uint64_t timer_id) {
  kk_wasiweb_dispatch(timer_id);
}

__attribute__((export_name("koka:async/loop-done")))
bool kk_wasiweb_export_loop_done(void) {
  return kk_wasiweb_loop_done();
}
