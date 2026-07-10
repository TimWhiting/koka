/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// DOM fringe for `--target=jsweb`: the compiled Koka runs in the page, so
// elements, subscriptions, and events are direct javascript references (no
// externref table -- the javascript GC owns the objects; `unsubscribe`
// removes listeners eagerly just like the wasi-web implementation).
//
// `subscribe` takes a callback and is framework-internal: vdom passes the
// runtime's own emit function. Application code never sees a callback -- it
// gets messages out of the app's channel (see web-ui/app), or `events`'s
// channel below when using the fringe standalone.
module web-ui/api/jsweb/dom

import std/async
import std/async/internal
import std/core/unsafe
import std/num/int32

extern import
  js file "dom.js"

// A live DOM element: a direct reference to the javascript object.
pub value struct element(obj : any)

// A listener subscription: dropping it is inert on this backend (the
// javascript GC owns it); `unsubscribe` removes the listener eagerly.
pub value struct sub(obj : any)

extern is-null(x : any) : bool
  js "kk_dom_is_null"

// ----------------------------------------------------------------
// element lookup / creation

extern get-element-by-id-raw(id : string) : ioc any
  js "kk_dom_get_element_by_id"

pub fun get-element-by-id(id : string) : ioc maybe<element>
  val el = get-element-by-id-raw(id)
  if el.is-null then Nothing else Just(Element(el))

extern create-element-raw(tag : string) : ioc any
  js "kk_dom_create_element"

pub fun create-element(tag : string) : ioc element
  Element(create-element-raw(tag))

extern create-text-raw(s : string) : ioc any
  js "kk_dom_create_text"

pub fun create-text(s : string) : ioc element
  Element(create-text-raw(s))

// ----------------------------------------------------------------
// structural mutation (explicit; the only way the visible DOM changes)

extern append-child-raw(parent : any, child : any) : ioc ()
  js "kk_dom_append_child"

pub fun append-child(parent : element, child : element) : ioc ()
  append-child-raw(parent.obj, child.obj)

extern remove-child-raw(parent : any, child : any) : ioc ()
  js "kk_dom_remove_child"

pub fun remove-child(parent : element, child : element) : ioc ()
  remove-child-raw(parent.obj, child.obj)

extern replace-child-raw(parent : any, fresh : any, old : any) : ioc ()
  js "kk_dom_replace_child"

pub fun replace-child(parent : element, fresh : element, old : element) : ioc ()
  replace-child-raw(parent.obj, fresh.obj, old.obj)

extern insert-before-raw(parent : any, child : any, anchor : any) : ioc ()
  js "kk_dom_insert_before"

// insert (or MOVE, if already attached) `child` before `anchor`
pub fun insert-before(parent : element, child : element, anchor : element) : ioc ()
  insert-before-raw(parent.obj, child.obj, anchor.obj)

// ----------------------------------------------------------------
// attributes / text / properties

extern set-attribute-raw(elem : any, name : string, value : string) : ioc ()
  js "kk_dom_set_attribute"

pub fun set-attribute(elem : element, name : string, value : string) : ioc ()
  set-attribute-raw(elem.obj, name, value)

extern remove-attribute-raw(elem : any, name : string) : ioc ()
  js "kk_dom_remove_attribute"

pub fun remove-attribute(elem : element, name : string) : ioc ()
  remove-attribute-raw(elem.obj, name)

extern set-text-raw(elem : any, text : string) : ioc ()
  js "kk_dom_set_text"

pub fun set-text(elem : element, text : string) : ioc ()
  set-text-raw(elem.obj, text)

extern get-prop-raw(elem : any, name : string) : ioc string
  js "kk_dom_get_prop"

// a named string property of the element (empty if absent)
pub fun get-prop(elem : element, name : string) : ioc string
  get-prop-raw(elem.obj, name)

// The current value of an input element (empty if none).
pub fun get-value(elem : element) : ioc string
  elem.get-prop("value")

extern get-num-prop-raw(elem : any, name : string) : ioc float64
  js "kk_dom_get_num_prop"

// a numeric property of an element (e.g. "clientWidth"); 0.0 if absent
pub fun element/num-prop(elem : element, name : string) : ioc float64
  get-num-prop-raw(elem.obj, name)

// ----------------------------------------------------------------
// events

extern current-event-raw() : ioc any
  js "kk_dom_current_event"

// The JS event currently being dispatched -- only meaningful inside an
// event-handler message builder (html's OnEvent).
pub value struct event(obj : any)

pub fun current-event() : ioc event
  Event(current-event-raw())

// a named string property of the current event ("key" for keyboard events,
// "drag-data" for the dataTransfer text payload)
pub fun event/prop(ev : event, name : string) : ioc string
  get-prop-raw(ev.obj, name)

pub fun event/key(ev : event) : ioc string
  ev.prop("key")

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
// earlier content -- see dom.js's `kk_dom_wheel_scale`); only meaningful
// inside a "wheel" listener.
pub extern event-wheel-dx() : ioc float64
  js "kk_dom_event_wheel_dx"

pub extern event-wheel-dy() : ioc float64
  js "kk_dom_event_wheel_dy"

// True when the browser reports `prefers-color-scheme: dark`
pub extern prefers-dark() : ioc bool
  js "kk_dom_prefers_dark"

// measured pixel width of one line of `content` set in `css-font` (a CSS
// `font` shorthand, e.g. "700 italic 15px Georgia,serif"), via the host canvas
pub extern measure-text-width(content : string, css-font : string) : ioc float64
  js "kk_dom_measure_text_width"

// measured pixel height of `content` in `css-font` when wrapped to `max-w`
// pixels (a hidden reflowed div)
pub extern measure-text-box-height(content : string, css-font : string, max-w : float64) : ioc float64
  js "kk_dom_measure_text_box_height"

// measure a `rich` widget's runs: `span-starts`/`span-ends` are CODEPOINT
// offsets into `content` (parallel to each other and to `span-css-fonts`),
// mirroring `ui/widget`'s `text-span` convention. The JS side builds a
// hidden container with one `<span>` per run -- base-styled gaps and
// span-styled runs, interleaved left to right -- IDENTICAL in structure to
// `ui/api/web/backend.kk`'s paint case, so measured geometry matches
// painted geometry, then reads back the container's own box plus each
// span's `getClientRects()` (one rect per LINE a span occupies when it
// wraps -- no glyph-index math needed on this backend, unlike native).
//
// The return is FLATTENED rather than a nested vector (Koka's extern
// binding does not carry nested vector/tuple shapes cleanly across the JS
// boundary the way flat scalars/vectors do): `rect-quads` packs every
// span's rect(s) back-to-back, 4 float64s (x,y,w,h) each, in span order;
// `rect-counts` says how many of those quads belong to each span in turn
// (`ui/api/web/backend.kk`'s `measure-rich-web` reassembles the grouping).
// `max-w` follows `measure-text-box-height`'s convention: at or above
// `ui/widget`'s `unbounded-w` sentinel means "single line, natural width"
// (no wrap) -- there is no separate `wrap : bool` parameter, wrap-state is
// always derivable from `max-w` alone (see `ui/widget`'s `is-unbounded`).
pub extern measure-rich-box(content : string, base-css-font : string,
                            span-starts : vector<int32>, span-ends : vector<int32>, span-css-fonts : vector<string>,
                            max-w : float64) : ioc (float64, float64, vector<float64>, vector<int32>)
  js "kk_dom_measure_rich_box"

extern window-raw() : ioc any
  js "kk_dom_window"

// The browser window object (usable as an event target for window-level
// events such as "hashchange").
pub fun window() : ioc element
  Element(window-raw())

// Navigation: window.location.hash := s (fires "hashchange" when it differs).
pub extern set-hash(s : string) : ioc ()
  js "kk_dom_set_hash"

// The current window.location.hash (including the leading '#', or empty).
pub fun get-hash() : ioc string
  window().get-prop("hash")

// ----------------------------------------------------------------
// listeners

extern subscribe-raw(elem : any, event : string, action : () -> ioc ()) : ioc any
  js "kk_dom_subscribe"

// Framework-internal (vdom passes the runtime's emit): registers `action`
// for `event` on `elem`.
pub fun subscribe(elem : element, event : string, action : () -> ioc ()) : ioc sub
  Sub(subscribe-raw(elem.obj, event, action))

extern unsubscribe-raw(subobj : any) : ioc ()
  js "kk_dom_unsubscribe"

// Eager, explicit deregistration (idempotent).
pub fun unsubscribe(s : sub) : ioc ()
  unsubscribe-raw(s.obj)

// ----------------------------------------------------------------
// standalone (non-vdom) use: events as a channel, never a raw callback.

// Subscriptions handed out by `events` live as long as the program: retain
// them for interface parity with the wasi-web implementation.
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
  js "kk_dom_inject_click"

// types into the FOCUSED input; False if nothing focusable is focused
pub extern inject-text( s : string ) : ioc bool
  js "kk_dom_inject_text"

// the page title (browser test probes read pass/fail from it)
pub extern set-title( s : string ) : ioc ()
  js "kk_dom_set_title"

pub extern inject-key( key : string ) : ioc ()
  js "kk_dom_inject_key"
pub extern inject-move( x : float64, y : float64 ) : ioc ()
  js "kk_dom_inject_move"
pub extern inject-wheel( x : float64, y : float64, dy : float64 ) : ioc ()
  js "kk_dom_inject_wheel"

// ----------------------------------------------------------------
// ui/image's `FromPixels` (task 4, web parity): raw RGBA8888 -> a PNG
// data-url via an offscreen canvas + `putImageData` (see dom.js) -- so
// `FromPixels` renders through the SAME `<img src>` / onload-probe path as
// every other source variant. `w`/`h` go through `int32` (a plain JS number
// on this backend) for the same reason other numeric DOM args do.
extern pixels-to-dataurl-raw( rgba : vector<int8>, w : int32, h : int32 ) : ioc string
  js "kk_dom_pixels_to_dataurl"

pub fun pixels-to-dataurl( rgba : vector<int8>, w : int, h : int ) : ioc string
  pixels-to-dataurl-raw(rgba, w.int32, h.int32)
