/*---------------------------------------------------------------------------
  Copyright 2026, Microsoft Research, Daan Leijen, Tim Whiting

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Minimal DOM interop bindings for the `wasi-web` target. Rev 3 / Core Task
// 2: `koka:dom` is a plain wasm core-module import namespace (no
// wit-bindgen, no component model -- see dom.c and
// lib/std/async/api/wasiweb/evloop.c for the identical pattern applied to
// `koka:async/timers`), and real DOM elements cross the wasm boundary as
// `__externref_t` values held in a Perceus-owned table (jsobj.c/jsobj.kk),
// not integer handles looked up in a JS-side `Map`. This is a sample-local
// module (not `lib/std`), see build.sh and readme.md for how it links.
//
// C stays at the fringe: `dom.c` only does canonical-ABI string marshaling,
// the externref <-> table-slot conversion (via jsobj.c), and stores exactly
// one `kk_function_t` (this module's dispatcher, registered once below).
// The id -> listener mapping and the dispatch itself are ordinary Koka, kept
// in the `listeners` ref.
//
// The public surface has no raw callbacks: no `int`/`any` handles leak out
// of `element` (it wraps a Perceus-owned box, see below) and no `pub
// extern`/`pub fun` that takes a function -- `events` hands back a
// `channel<()>` instead (see std/async/channel.kk), the same shape as every
// other async source in std/async (timers, promises, ...).
module dom

// Not called directly (this module only wraps `koka:dom` DOM imports, no
// timers/futures), but importing it is what pulls in
// `std/async/api/wasiweb/evloop` on `--target=wasi-web` (see its conditional
// `[host=wasi-web]` import in `lib/std/async/async.kk`): that module defines
// `kk_wasiweb_loop_ref`/`_unref`, the evloop-singleton helpers `loop-ref`
// forwards to below to keep the loop (and thus node's `loopDone()`
// keep-alive poll, see support/wasi-web/run.mjs) alive for as long as any
// DOM listener is registered. Without this import the compiler's
// module-dependency-driven linker (`codeGenLinkC` in src/Compile/CodeGen.hs)
// would never compile/link `evloop.c`'s translation unit at all, and the
// link would fail with an undefined symbol. Also gives us `channel`,
// `emit-io`, and the `async-ioc` operation `events` uses below.
import std/async
import std/async/internal
import std/core/unsafe
import std/num/int32
import jsobj

extern import
  c file "dom.c"

// A real DOM element -- an opaque, Perceus-owned reference to a live JS
// object, never a raw integer handle. `obj` is the `any` box `jsobj.box`
// returns (a `kk_cptr_raw_box` around a table slot, see jsobj.c):
// dropping the last `element` value that holds a given slot is what
// releases the underlying JS object (nulls the table slot, letting the
// browser's JS GC reclaim it) -- see jsobj.c's `kk_js_obj_free_fun` and
// ../readme.md's "Perceus ownership" section. Mirrors how
// `wasiweb/evloop.kk`'s `event-loop-init` types its C-side loop pointer as
// `any`.
pub value struct element(obj : any)

// Private: the raw (possibly-0) slot number `dom.c` forwards to from
// `koka:dom`'s `get-element-by-id` import; 0 means "not found" (jsobj.c
// reserves slot 0 as invalid for exactly this reason). Wrapped by the public
// `get-element-by-id` below into a `maybe<element>` so 0 never leaks into
// Koka code as a valid element, and so the table slot is only ever boxed
// (and thus only ever Perceus-tracked) for the `Just` case.
extern get-element-by-id-raw(id : string) : ioc int32
  c "kk_wasiweb_dom_get_element_by_id"

pub fun get-element-by-id(id : string) : ioc maybe<element>
  val slot = get-element-by-id-raw(id)
  if slot == 0.int32 then Nothing else Just(Element(jsobj/box(slot)))

// Private: forwards the element's boxed slot straight through; `dom.c`
// unboxes it back to a raw slot (borrowed, so this call still owns+drops its
// own reference to the box, same as it owns+drops the `string`).
extern set-inner-text-raw(elem : any, text : string) : ioc ()
  c "kk_wasiweb_dom_set_inner_text"

pub fun set-inner-text(elem : element, text : string) : ioc ()
  set-inner-text-raw(elem.obj, text)

// Pure ABI forwarding: `listener-id` is picked by this module (a Koka-side
// counter, see `add-listener` below), not by `dom.c` -- there is no
// per-listener C-side table any more. Private: internal plumbing only.
extern add-event-listener-raw(elem : any, event : string, listener-id : int) : ioc ()
  c "kk_wasiweb_dom_add_event_listener"

// Registers the single dispatcher `dom.c` stores and routes every DOM event
// (from any listener, on any element) through. Private: the only C-side
// function that ever takes a `kk_function_t` is this one, and it is called
// exactly once (see the top-level `val` below).
extern register-dispatcher(dispatch : (int) -> ioc ()) : ioc ()
  c "kk_dom_register_dispatcher"

// Forwards to `lib/std/async/api/wasiweb/evloop.c`'s non-static
// `kk_wasiweb_loop_ref`: lazily inits the evloop singleton if this program
// never itself calls `std/async`'s `event-loop-init`, bumps its refcount,
// and marks the kklib context "keep alive" -- mirrors what
// `event-loop-run` does for the `std/async`-driven path. Called once per
// registered listener (see `add-listener`); logic (when to call it) lives
// in Koka, `dom.c` just forwards the call.
extern loop-ref() : ioc ()
  c "kk_wasiweb_loop_ref"

extern loop-unref() : ioc ()
  c "kk_wasiweb_loop_unref"

// The id -> listener table, moved out of `dom.c` into ordinary Koka: a
// simple association list is plenty for this sample's scale (a handful of
// listeners on one demo page). `unsafe-total` to dismiss the `st<global>`
// effect at module-init time, same pattern as `std/core/debug`'s
// `trace-enabled`.
val listeners : ref<global,list<(int, () -> ioc ())>> = unsafe-total{ ref([]) }

// The one dispatcher registered with `dom.c`, called for every DOM event
// regardless of which listener it targets; looks the callback up by id and
// invokes it (listeners fire repeatedly, unlike a one-shot timer).
fun dispatch-event( listener-id : int ) : ioc ()
  match (!listeners).lookup( fn(id) id == listener-id )
    Just(cb) -> cb()
    Nothing  -> ()  // unknown id (already removed, or a stray event) -- ignore

// Module init: register `dispatch-event` as `dom.c`'s single stored
// dispatcher exactly once, before any listener can be registered.
val register-dispatcher-once : () = unsafe-total{ register-dispatcher(dispatch-event) }

// Private: registers `cb` (an internal, `ioc`-effectful callback) for
// `event` on `elem`, allocating a fresh id (a simple process-wide counter,
// see `std/core`'s `unique`), keeping the evloop alive for as long as this
// listener exists. Not exported -- the public surface below never takes a
// raw callback, only `events`'s `channel<()>` result.
fun add-listener(elem : element, event : string, cb : () -> ioc ()) : ioc ()
  val id = unique()
  listeners := Cons((id,cb), !listeners)
  loop-ref()
  add-event-listener-raw(elem.obj, event, id)

// Public, Koka-idiomatic listener API: no raw callbacks. Registers a
// listener for `event` on `elem` and returns a fresh `channel<()>` that
// receives a `()` value every time the event fires (payload types beyond
// `()` can follow later; the DOM event object itself is not marshaled
// yet). Callers consume it with `receive`/`try-receive` from
// std/async/channel.kk, e.g.:
// ```
// val ch = btn.events("click")
// ch.receive()   // waits for (or returns immediately with) the next click
// ```
pub fun events(elem : element, event : string) : <async,ndet> channel<()>
  val ch = channel()
  async-ioc
    elem.add-listener(event) fn() ch.emit-io(())
  ch
