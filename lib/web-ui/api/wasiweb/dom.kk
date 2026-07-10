/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// DOM fringe for the framework: thin Koka wrappers over the "koka:dom"
// core-module imports (dom.c). Structural DOM mutation happens ONLY through
// these explicit calls; dropping `element`/`sub` values merely releases the
// wasm-side references (see jsobj.c and the design spec's "detach is a call,
// release is a drop").
//
// `subscribe` takes a callback and is framework-internal: vdom.kk passes the
// runtime's own emit function. Application code never sees a callback — it
// gets messages out of the app's channel (see app.kk), or `events`'s channel
// below when using the fringe standalone.
module web-ui/api/wasiweb/dom

import std/num/int32
import std/num/float64
import std/async
import std/async/internal
import std/core/unsafe
import std/core/undiv
import web-ui/api/wasiweb/jsobj

extern import
  c file "dom.c"

// A live DOM element: an opaque, Perceus-owned reference to a JS object.
// Dropping the last `element` value releases the wasm-side reference (the
// browser can then GC the node once it is also detached) — it never detaches
// the node from the tree by itself.
pub value struct element(obj : any)

// A listener subscription: Perceus-owned; dropping it removes the listener
// host-side (idempotent). Prefer explicit `unsubscribe` in framework code
// (the patcher) — the drop is the structural safety net.
pub value struct sub(obj : any, id : int)

// ----------------------------------------------------------------
// element lookup / creation

extern get-element-by-id-raw(id : string) : ioc int32
  c "kk_domc_get_element_by_id"

pub fun get-element-by-id(id : string) : ioc maybe<element>
  val slot = get-element-by-id-raw(id)
  if slot == 0.int32 then Nothing else Just(Element(jsobj/box(slot)))

extern create-element-raw(tag : string) : ioc int32
  c "kk_domc_create_element"

pub fun create-element(tag : string) : ioc element
  Element(jsobj/box(create-element-raw(tag)))

extern create-text-raw(s : string) : ioc int32
  c "kk_domc_create_text"

pub fun create-text(s : string) : ioc element
  Element(jsobj/box(create-text-raw(s)))

// ----------------------------------------------------------------
// structural mutation (explicit; the only way the visible DOM changes)

extern append-child-raw(parent : any, child : any) : ioc ()
  c "kk_domc_append_child"

pub fun append-child(parent : element, child : element) : ioc ()
  append-child-raw(parent.obj, child.obj)

extern remove-child-raw(parent : any, child : any) : ioc ()
  c "kk_domc_remove_child"

pub fun remove-child(parent : element, child : element) : ioc ()
  remove-child-raw(parent.obj, child.obj)

extern replace-child-raw(parent : any, fresh : any, old : any) : ioc ()
  c "kk_domc_replace_child"

pub fun replace-child(parent : element, fresh : element, old : element) : ioc ()
  replace-child-raw(parent.obj, fresh.obj, old.obj)

extern insert-before-raw(parent : any, child : any, anchor : any) : ioc ()
  c "kk_domc_insert_before"

// insert (or MOVE, if already attached) `child` before `anchor`
pub fun insert-before(parent : element, child : element, anchor : element) : ioc ()
  insert-before-raw(parent.obj, child.obj, anchor.obj)

// ----------------------------------------------------------------
// attributes / text / input value

extern set-attribute-raw(elem : any, name : string, value : string) : ioc ()
  c "kk_domc_set_attribute"

pub fun set-attribute(elem : element, name : string, value : string) : ioc ()
  set-attribute-raw(elem.obj, name, value)

extern remove-attribute-raw(elem : any, name : string) : ioc ()
  c "kk_domc_remove_attribute"

pub fun remove-attribute(elem : element, name : string) : ioc ()
  remove-attribute-raw(elem.obj, name)

extern set-text-raw(elem : any, text : string) : ioc ()
  c "kk_domc_set_text"

pub fun set-text(elem : element, text : string) : ioc ()
  set-text-raw(elem.obj, text)

// JS→Koka string: a named string property of the element (empty if absent).
// The host page defines which names it answers: "value" (form inputs),
// "hash" (window.location.hash, on the window object).
extern get-prop-raw(elem : any, name : string) : ioc string
  c "kk_domc_get_prop"

pub fun get-prop(elem : element, name : string) : ioc string
  get-prop-raw(elem.obj, name)

// The current value of an input element (empty if none).
pub fun get-value(elem : element) : ioc string
  elem.get-prop("value")

extern current-event-raw() : ioc int32
  c "kk_domc_current_event"

// The JS event currently being dispatched -- only meaningful inside an
// event-handler message builder (html.kk's OnEvent); a transient handle
// whose slot frees as soon as the value drops.
pub value struct event(obj : any)

pub fun current-event() : ioc event
  Event(jsobj/box(current-event-raw()))

// a named string property of the current event ("key" for keyboard events,
// "drag-data" for the dataTransfer text payload -- see the host page)
pub fun event/prop(ev : event, name : string) : ioc string
  get-prop-raw(ev.obj, name)

pub fun event/key(ev : event) : ioc string
  ev.prop("key")

extern get-num-prop-raw(elem : any, name : string) : ioc float64
  c "kk_domc_get_num_prop"

// a numeric property of an element (e.g. "clientWidth"); 0.0 if absent
pub fun element/num-prop(elem : element, name : string) : ioc float64
  get-num-prop-raw(elem.obj, name)

// a named numeric property of the current event (0.0 when absent)
pub fun event/num-prop(ev : event, name : string) : ioc float64
  get-num-prop-raw(ev.obj, name)

pub fun event/client-x(ev : event) : ioc float64
  ev.num-prop("clientX")

pub fun event/client-y(ev : event) : ioc float64
  ev.num-prop("clientY")

pub fun event/drag-data(ev : event) : ioc string
  ev.prop("drag-data")

// the CURRENT event's wheel delta, normalized by deltaMode and sign-flipped
// to ui/state's `apply-wheel` convention (delta > 0 = wheel-up = reveal
// earlier content -- see the host page's implementation); only meaningful
// inside a "wheel" listener.
pub extern event-wheel-dx() : ioc float64
  c "kk_domc_event_wheel_dx"

pub extern event-wheel-dy() : ioc float64
  c "kk_domc_event_wheel_dy"

// measured pixel width of one line of `content` set in `css-font` (a CSS
// `font` shorthand, e.g. "700 italic 15px Georgia,serif"), host-measured
pub extern measure-text-width(content : string, css-font : string) : ioc float64
  c "kk_domc_measure_text_width"

// measured pixel height of `content` in `css-font` when wrapped to `max-w`
// pixels (host reflows a hidden div)
pub extern measure-text-box-height(content : string, css-font : string, max-w : float64) : ioc float64
  c "kk_domc_measure_text_box_height"

// `rich` measurement on wasi-web: unlike jsweb (`lib/web-ui/api/jsweb/dom.kk`'s
// `measure-rich-box`, which drives a real hidden `<span>`-per-run container
// through a dedicated host import), there is no "koka:dom" host import for
// per-span DOM measurement yet -- adding one needs a NEW import PLUS the
// host page's JS implementation (`support/wasi-web/*.js`), both out of this
// task's scope (Task 3 is jsweb; the native/impeller backend already has its
// own real implementation). This keeps `ui/api/web/backend.kk` -- which
// BOTH hosts share -- typechecking for wasi-web too, by composing the
// text-measurement imports that already exist: total width sums each run's
// own natural width in its own font (gap runs in `base-css-font`, span runs
// in their override), mirroring the per-run decomposition
// `ui/api/web/backend.kk`'s `measure-rich-web` builds; total height reflows
// the whole `content` in `base-css-font` at `max-w` (accurate for uniform
// runs; a span whose font is much taller than the base will under-report,
// same class of approximation `measure-web`'s single-line height already
// makes for plain text -- concretely, on wasi-web a span set in a LARGER
// font than the surrounding base text can get the container's reported
// height under-measured, so that span's content risks being clipped by the
// container's `overflow:hidden`). Spans report NO rects -- the same "ignore
// spans" fallback Task 1 shipped for jsweb before this task, now scoped to
// wasi-web alone; a `rich` widget's spans are simply not clickable there
// (`on-click` is silently inert) until a real host import lands. KNOWN,
// DOCUMENTED, out-of-scope-for-now limitation -- see the design spec's
// "Known limitations" section (`docs/superpowers/specs/
// 2026-08-01-rich-text-primitive-design.md`) for the plan-level record.
pub fun measure-rich-box(content : string, base-css-font : string,
                         span-starts : vector<int32>, span-ends : vector<int32>, span-css-fonts : vector<string>,
                         max-w : float64) : ioc (float64, float64, vector<float64>, vector<int32>)
  val n = span-starts.length
  fun run-width( pos : int, i : int ) : ioc float64
    if i >= n then
      (if pos < content.count then measure-text-width(content.slice.advance(pos).string, base-css-font) else 0.0)
    else
      val s = span-starts.at(i).default(0.int32).int
      val e = span-ends.at(i).default(0.int32).int
      val f = span-css-fonts.at(i).default(base-css-font)
      val gap-w = if s > pos then measure-text-width(content.slice.advance(pos).truncate.extend(s - pos).string, base-css-font) else 0.0
      val span-w = measure-text-width(content.slice.advance(s).truncate.extend(e - s).string, f)
      gap-w + span-w + run-width(e, i + 1).pretend-decreasing
  val tw-natural = run-width(0, 0)
  // `1.0e6` mirrors `ui/widget`'s `is-unbounded` threshold / this backend's
  // own `single-line-w` convention (`ui/api/web/backend.kk`) -- not imported
  // here to avoid a `web-ui -> ui` dependency, same as jsweb's `dom.js`.
  val wrap-mode = max-w < 1.0e6
  val tw = if wrap-mode then tw-natural.min(max-w) else tw-natural
  val th = measure-text-box-height(content, base-css-font, max-w)
  (tw, th, [].vector, list(1, n).map(fn(_) 0.int32).vector)

extern window-raw() : ioc int32
  c "kk_domc_window"

// The browser window object (a JS object like any other -- usable as an
// event target for window-level events such as "hashchange").
pub fun window() : ioc element
  Element(jsobj/box(window-raw()))

// Navigation: window.location.hash := s (fires "hashchange" when it differs).
pub extern set-hash(s : string) : ioc ()
  c "kk_domc_set_hash"

// The current window.location.hash (including the leading '#', or empty).
pub fun get-hash() : ioc string
  window().get-prop("hash")

// ----------------------------------------------------------------
// listeners: single C-stored dispatcher; id→action registry in Koka.

extern add-listener-raw(elem : any, event : string, listener-id : int) : ioc any
  c "kk_dom_add_listener"

extern remove-listener-now-raw(subobj : any) : ioc ()
  c "kk_domc_remove_listener_now"

extern register-dispatcher(dispatch : (int) -> ioc ()) : ioc ()
  c "kk_domc_register_dispatcher"

extern loop-ref() : ioc ()
  c "kk_domc_loop_ref"

extern loop-unref() : ioc ()
  c "kk_domc_loop_unref"

// id → action registry (ordinary Koka state; C never stores callbacks
// beyond the single dispatcher).
val listeners : ref<global,list<(int, () -> ioc ())>> = unsafe-total{ ref([]) }

fun dispatch-event( listener-id : int ) : ioc ()
  match (!listeners).lookup( fn(id) id == listener-id )
    Just(action) -> action()
    Nothing      -> ()  // already unsubscribed; stray event — ignore

val register-dispatcher-once : () = unsafe-total{ register-dispatcher(dispatch-event) }

// Framework-internal (vdom passes the runtime's emit): registers `action`
// for `event` on `elem`; keeps the event loop alive while subscribed.
pub fun subscribe(elem : element, event : string, action : () -> ioc ()) : ioc sub
  val id = unique()
  listeners := Cons((id, action), !listeners)
  loop-ref()
  Sub(add-listener-raw(elem.obj, event, id), id)

// Eager, explicit deregistration: registry entry out (Koka), host
// removeEventListener (idempotent), loop refcount down. The sub's eventual
// drop releases the table slot.
pub fun unsubscribe(s : sub) : ioc ()
  listeners := (!listeners).filter( fn(entry) entry.fst != s.sub/id )
  remove-listener-now-raw(s.obj)
  loop-unref()

// ----------------------------------------------------------------
// standalone (non-vdom) use: events as a channel, never a raw callback.

// Subscriptions handed out by `events` live as long as the program: retain
// them here so the sub's drop (which removes the host listener -- by design)
// does not fire the moment the value goes out of scope below.
val retained-subs : ref<global,list<sub>> = unsafe-total{ ref([]) }

pub fun sub/retain(s : sub) : ioc ()
  retained-subs := Cons(s, !retained-subs)

pub fun events(elem : element, event : string) : <async,ndet> channel<()>
  val ch = channel()
  async-ioc
    retain(elem.subscribe(event, fn() ch.emit-io(())))
  ch

// ----------------------------------------------------------------
// synthetic input (ui/test-live): real DOM events through real listeners

pub extern inject-click( x : float64, y : float64 ) : ioc ()
  c "kk_domc_inject_click"

// types into the FOCUSED input; False if nothing focusable is focused
pub extern inject-text( s : string ) : ioc bool
  c "kk_domc_inject_text"

// the page title (browser test probes read pass/fail from it)
pub extern set-title( s : string ) : ioc ()
  c "kk_domc_set_title"

pub extern inject-key( key : string ) : ioc ()
  c "kk_domc_inject_key"
pub extern inject-move( x : float64, y : float64 ) : ioc ()
  c "kk_domc_inject_move"
pub extern inject-wheel( x : float64, y : float64, dy : float64 ) : ioc ()
  c "kk_domc_inject_wheel"

// ----------------------------------------------------------------
// ui/image's `FromPixels` (task 4, web parity): raw RGBA8888 -> a PNG
// data-url via an offscreen canvas + `putImageData` (see dom.c / the host
// page) -- so `FromPixels` renders through the SAME `<img src>` /
// onload-probe path as every other source variant.
extern pixels-to-dataurl-raw( rgba : vector<int8>, w : int32, h : int32 ) : ioc string
  c "kk_domc_pixels_to_dataurl"

pub fun pixels-to-dataurl( rgba : vector<int8>, w : int, h : int ) : ioc string
  pixels-to-dataurl-raw(rgba, w.int32, h.int32)
