/*---------------------------------------------------------------------------
  Copyright 2026, Microsoft Research, Daan Leijen, Tim Whiting

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// #include <kklib.h>  -- already included (this file is textually pasted into
// dom.kk's own generated .c via `extern import c file`, same convention as
// lib/std/async/api/wasiweb/evloop.c / evloop.kk).

// Rev 3 / Core Task 2: `koka:dom` is a plain wasm core-module import
// namespace (no wit-bindgen, no component model -- see
// lib/std/async/api/wasiweb/evloop.c for the identical pattern applied to
// `koka:async/timers`), and real DOM elements cross the wasm boundary as
// `__externref_t` values, not integer handles -- there is no JS-side handle
// `Map` any more (see index.html). C stays at the fringe here: canonical ABI
// string marshaling (kk_string_t -> ptr/len), the externref <-> table-slot
// conversion (via jsobj.c, a sibling sample-local module -- see jsobj.kk),
// storage of exactly one `kk_function_t` (the dispatcher registered once by
// dom.kk at module init), and the `dispatch-event` export trampoline that
// dups+calls it. There is no per-listener table in C -- the id-to-listener
// bookkeeping is a Koka `ref` (see dom.kk).

__attribute__((import_module("koka:dom"), import_name("get-element-by-id")))
extern __externref_t koka_dom_get_element_by_id(const uint8_t* ptr, size_t len);

__attribute__((import_module("koka:dom"), import_name("set-inner-text")))
extern void koka_dom_set_inner_text(__externref_t el, const uint8_t* ptr, size_t len);

__attribute__((import_module("koka:dom"), import_name("add-event-listener")))
extern void koka_dom_add_event_listener(__externref_t el, const uint8_t* ptr, size_t len, uint64_t listener_id);

// Non-static helpers from jsobj.c (a sibling module, see jsobj.kk):
// `kk_js_obj_alloc`/`kk_js_obj_get` convert between a raw `__externref_t` and
// the small `int32_t` "slot" number that can actually live inside a Koka
// value (wrapped in a Perceus-owned box by `kk_js_obj_box`, called from
// dom.kk right after `kk_wasiweb_dom_get_element_by_id` below).
// `kk_js_obj_slot_borrow` unwraps an `element`'s box back to its slot number
// without consuming a reference (this file still owns+drops the box itself,
// same convention as `kk_string_buf_borrow`/`kk_string_drop`).
extern int32_t       kk_js_obj_alloc(__externref_t ref, kk_context_t* ctx);
extern __externref_t kk_js_obj_get(int32_t slot);
extern int32_t       kk_js_obj_slot_borrow(kk_box_t box, kk_context_t* ctx);

// Non-static helpers exported from lib/std/async/api/wasiweb/evloop.c: let a
// second, independently-compiled wasi-web module (this one) hold the same
// evloop singleton alive without reaching into evloop.c's file-static
// `kk_wasiweb_loop` variable. Forwarded 1:1 to a Koka extern (`loop-ref`) in
// dom.kk -- this file does no keep-alive bookkeeping of its own, that logic
// (calling it once per registered listener) lives in Koka now.
extern void kk_wasiweb_loop_ref(kk_context_t* ctx);
extern void kk_wasiweb_loop_unref(kk_context_t* ctx);


//----------------------------------------------
// string ABI helper: borrow a kk_string_t's UTF-8 bytes as a (ptr,len) pair,
// the same shape the old component-model wit-bindgen output used, now passed
// straight through to the plain core-module imports above. Borrowed, not
// owned -- valid only for the duration of the (synchronous) import call.
//----------------------------------------------

static const uint8_t* kk_wasiweb_dom_string_borrow(kk_string_t s, size_t* len, kk_context_t* ctx) {
  kk_ssize_t l;
  const uint8_t* buf = kk_string_buf_borrow(s, &l, ctx);
  *len = (size_t)l;
  return buf;
}


//----------------------------------------------
// the one stored dispatcher -- registered exactly once, at dom.kk's module
// init, by a top-level `val` that calls `register-dispatcher`. Every DOM
// event (from any listener, on any element) is routed through this single
// Koka function; the Koka-side dispatcher does its own id -> action lookup
// in a Koka `ref` (see dom.kk).
//----------------------------------------------

static bool          kk_dom_dispatcher_set; // = false
static kk_function_t kk_dom_dispatcher;     // valid iff kk_dom_dispatcher_set

// Called once from dom.kk's module init (via a private extern); stores the
// dispatcher closure for the lifetime of the program.
void kk_dom_register_dispatcher(kk_function_t dispatch, kk_context_t* ctx) {
  kk_unused(ctx);
  kk_dom_dispatcher = dispatch;
  kk_dom_dispatcher_set = true;
}


//----------------------------------------------
// exposed operations (called from dom.kk's `extern import`)
//----------------------------------------------

// Returns 0 ("not found" -- slot 0 is reserved invalid, see jsobj.c) when the
// host's `get-element-by-id` yields a null externref; otherwise allocates a
// fresh table slot for the returned element and returns its (always > 0)
// slot number. Wrapped by dom.kk's public `get-element-by-id` into
// `maybe<element>`, boxing the slot via `jsobj/box` for the `Just` case.
int32_t kk_wasiweb_dom_get_element_by_id(kk_string_t id, kk_context_t* ctx) {
  size_t len;
  const uint8_t* buf = kk_wasiweb_dom_string_borrow(id, &len, ctx);
  __externref_t ref = koka_dom_get_element_by_id(buf, len);
  kk_string_drop(id, ctx);
  if (__builtin_wasm_ref_is_null_extern(ref)) return 0;
  return kk_js_obj_alloc(ref, ctx);
}

// `elem` is an `element`'s boxed slot (an `any` in Koka); this function owns
// (consumes) that reference, same convention as the `kk_string_t` it also
// consumes -- both are dropped at the end.
void kk_wasiweb_dom_set_inner_text(kk_box_t elem, kk_string_t text, kk_context_t* ctx) {
  int32_t slot = kk_js_obj_slot_borrow(elem, ctx);
  __externref_t el = kk_js_obj_get(slot);
  size_t len;
  const uint8_t* buf = kk_wasiweb_dom_string_borrow(text, &len, ctx);
  koka_dom_set_inner_text(el, buf, len);
  kk_string_drop(text, ctx);
  kk_box_drop(elem, ctx);
}

// Pure ABI forwarding: `listener_id` is picked by dom.kk (a Koka-side
// counter), not by this file -- no C-side listener storage at all any more.
void kk_wasiweb_dom_add_event_listener(kk_box_t elem, kk_string_t event, kk_integer_t listener_id, kk_context_t* ctx) {
  int32_t slot = kk_js_obj_slot_borrow(elem, ctx);
  __externref_t el = kk_js_obj_get(slot);
  size_t len;
  const uint8_t* buf = kk_wasiweb_dom_string_borrow(event, &len, ctx);
  uint64_t id = (uint64_t)kk_integer_clamp64(listener_id, ctx);
  koka_dom_add_event_listener(el, buf, len, id);
  kk_string_drop(event, ctx);
  kk_box_drop(elem, ctx);
}


//----------------------------------------------
// wasm core-module export: the JS host (index.html) re-enters the guest
// through `koka:dom/dispatch-event` whenever a real DOM event fires on any
// listener registered via `add-event-listener` above. Plain `export_name`
// attribute, mirrors `koka:async/dispatch` in evloop.c -- no wit-bindgen
// trampoline any more.
//----------------------------------------------

__attribute__((export_name("koka:dom/dispatch-event")))
void kk_dom_export_dispatch_event(uint64_t listener_id) {
  kk_context_t* ctx = kk_get_context();
  if (!kk_dom_dispatcher_set) return;  // no listener has been registered yet
  kk_function_t dispatch = kk_dom_dispatcher;
  kk_function_dup(dispatch, ctx);  // the single dispatcher fires repeatedly, never consumed
  kk_integer_t id = kk_integer_from_uint64(listener_id, ctx);
  kk_function_call(kk_unit_t, (kk_function_t, kk_integer_t, kk_context_t*), dispatch, (dispatch, id, ctx), ctx);
  // Same reasoning as evloop.c's `kk_wasiweb_dispatch`: this export is a
  // re-entry into an already-`_start`-returned instance, so stdio would
  // otherwise sit unflushed until a process exit that never happens on
  // wasi-web -- flush explicitly on every re-entry.
  fflush(NULL);
}
