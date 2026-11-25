/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// #include <kklib.h>  -- textually pasted into dom.kk's generated .c via
// `extern import c file` (same convention as evloop.c/jsobj.c).

// The framework's DOM fringe: plain wasm core-module imports under the
// "koka:dom" namespace, string marshaling (kk_string_t <-> ptr/len), the
// externref <-> table-slot conversion via jsobj.c, one stored dispatcher
// kk_function_t, and the dispatch-event export. All logic (listener
// registries, vdom, the app loop) lives in Koka -- see dom.kk/vdom.kk/app.kk.

//----------------------------------------------
// raw imports (implemented by the host page, see todo/index.html)
//----------------------------------------------

__attribute__((import_module("koka:dom"), import_name("get-element-by-id")))
extern __externref_t koka_dom_get_element_by_id(const uint8_t* ptr, size_t len);
__attribute__((import_module("koka:dom"), import_name("inject-click")))
extern void koka_dom_inject_click(double x, double y);
__attribute__((import_module("koka:dom"), import_name("inject-text")))
extern int32_t koka_dom_inject_text(const uint8_t* ptr, size_t len);
__attribute__((import_module("koka:dom"), import_name("set-title")))
extern void koka_dom_set_title(const uint8_t* ptr, size_t len);
__attribute__((import_module("koka:dom"), import_name("inject-key")))
extern void koka_dom_inject_key(const uint8_t* ptr, size_t len);
__attribute__((import_module("koka:dom"), import_name("inject-move")))
extern void koka_dom_inject_move(double x, double y);
__attribute__((import_module("koka:dom"), import_name("inject-wheel")))
extern void koka_dom_inject_wheel(double x, double y, double dy);

// wheel deltas of the CURRENT event, normalized + sign-flipped to
// ui/state's `apply-wheel` convention (see the host's implementation for the
// full rationale -- kept host-side since it needs deltaMode/window.innerHeight).
__attribute__((import_module("koka:dom"), import_name("event-wheel-dx")))
extern double koka_dom_event_wheel_dx(void);
__attribute__((import_module("koka:dom"), import_name("event-wheel-dy")))
extern double koka_dom_event_wheel_dy(void);

__attribute__((import_module("koka:dom"), import_name("create-element")))
extern __externref_t koka_dom_create_element(const uint8_t* ptr, size_t len);

__attribute__((import_module("koka:dom"), import_name("create-text")))
extern __externref_t koka_dom_create_text(const uint8_t* ptr, size_t len);

__attribute__((import_module("koka:dom"), import_name("append-child")))
extern void koka_dom_append_child(__externref_t parent, __externref_t child);

__attribute__((import_module("koka:dom"), import_name("remove-child")))
extern void koka_dom_remove_child(__externref_t parent, __externref_t child);

__attribute__((import_module("koka:dom"), import_name("replace-child")))
extern void koka_dom_replace_child(__externref_t parent, __externref_t fresh, __externref_t old);

__attribute__((import_module("koka:dom"), import_name("set-attribute")))
extern void koka_dom_set_attribute(__externref_t el, const uint8_t* nptr, size_t nlen, const uint8_t* vptr, size_t vlen);

__attribute__((import_module("koka:dom"), import_name("remove-attribute")))
extern void koka_dom_remove_attribute(__externref_t el, const uint8_t* nptr, size_t nlen);

__attribute__((import_module("koka:dom"), import_name("set-text")))
extern void koka_dom_set_text(__externref_t el, const uint8_t* ptr, size_t len);

// JS->Koka string, two calls: the host reports the UTF-8 byte length of a
// (named) string property of the object, then copies it into a buffer we
// allocate. The host snapshots the value on the length call and copies THAT
// snapshot, so the two calls cannot race a DOM mutation (single-threaded
// regardless). Property names the host understands: "value" (inputs),
// "hash" (window.location.hash) -- see the host page.
__attribute__((import_module("koka:dom"), import_name("get-prop-length")))
extern int32_t koka_dom_get_prop_length(__externref_t el, const uint8_t* nptr, size_t nlen);

__attribute__((import_module("koka:dom"), import_name("get-prop-copy")))
extern void koka_dom_get_prop_copy(__externref_t el, uint8_t* buf);

// host text measurement: a line width in a CSS font, and a wrapped box height
__attribute__((import_module("koka:dom"), import_name("measure-text-width")))
extern double kk_domi_measure_text_width(const char* s, size_t len, const char* f, size_t flen);

double kk_domc_measure_text_width(kk_string_t content, kk_string_t css, kk_context_t* ctx) {
  kk_ssize_t len, flen;
  const char* cbuf = kk_string_cbuf_borrow(content, &len, ctx);
  const char* fbuf = kk_string_cbuf_borrow(css, &flen, ctx);
  double w = kk_domi_measure_text_width(cbuf, (size_t)len, fbuf, (size_t)flen);
  kk_string_drop(content, ctx);
  kk_string_drop(css, ctx);
  return w;
}

__attribute__((import_module("koka:dom"), import_name("measure-text-box-height")))
extern double kk_domi_measure_text_box_height(const char* s, size_t len, const char* f, size_t flen, double maxw);

double kk_domc_measure_text_box_height(kk_string_t content, kk_string_t css, double maxw, kk_context_t* ctx) {
  kk_ssize_t len, flen;
  const char* cbuf = kk_string_cbuf_borrow(content, &len, ctx);
  const char* fbuf = kk_string_cbuf_borrow(css, &flen, ctx);
  double h = kk_domi_measure_text_box_height(cbuf, (size_t)len, fbuf, (size_t)flen, maxw);
  kk_string_drop(content, ctx);
  kk_string_drop(css, ctx);
  return h;
}

__attribute__((import_module("koka:dom"), import_name("get-num-prop")))
extern double koka_dom_get_num_prop(__externref_t el, const uint8_t* nptr, size_t nlen);

// insert `child` before `anchor` under `parent` (anchor never null here --
// appends use the separate append-child import)
__attribute__((import_module("koka:dom"), import_name("insert-before")))
extern void koka_dom_insert_before(__externref_t parent, __externref_t child, __externref_t anchor);

// the JS event currently being dispatched (valid only during a
// dispatch-event re-entry; the host sets/clears it around the call)
__attribute__((import_module("koka:dom"), import_name("current-event")))
extern __externref_t koka_dom_current_event(void);

// the browser window object (for window-level events like hashchange)
__attribute__((import_module("koka:dom"), import_name("window")))
extern __externref_t koka_dom_window(void);

// navigation: window.location.hash = <s>
__attribute__((import_module("koka:dom"), import_name("set-hash")))
extern void koka_dom_set_hash(const uint8_t* ptr, size_t len);

// Returns a host-side subscription record (an opaque JS object holding
// {element, event, bound function}) so removal needs no JS-side bookkeeping.
__attribute__((import_module("koka:dom"), import_name("add-listener")))
extern __externref_t koka_dom_add_listener(__externref_t el, const uint8_t* ptr, size_t len, uint64_t listener_id);

// ui/image's `FromPixels` (task 4, web parity): raw RGBA8888 -> a PNG
// data-url via an offscreen canvas + putImageData (see the host page). The
// SAME length-then-copy two-call pattern as get-prop -- the host snapshots
// the data-url on the length call so the two calls cannot disagree.
__attribute__((import_module("koka:dom"), import_name("pixels-to-dataurl-length")))
extern int32_t koka_dom_pixels_to_dataurl_length(const uint8_t* rgba, size_t rgba_len, int32_t w, int32_t h);
__attribute__((import_module("koka:dom"), import_name("pixels-to-dataurl-copy")))
extern void koka_dom_pixels_to_dataurl_copy(uint8_t* buf);

// Idempotent: removing an already-removed subscription is a no-op host-side.
__attribute__((import_module("koka:dom"), import_name("remove-listener")))
extern void koka_dom_remove_listener(__externref_t subscription);

//----------------------------------------------
// helpers from sibling modules (non-static, forward-declared -- same
// convention as before; see jsobj.c and lib/std/async/api/wasiweb/evloop.c)
//----------------------------------------------

extern int32_t       kk_js_obj_alloc(__externref_t ref, kk_context_t* ctx);
extern __externref_t kk_js_obj_get(int32_t slot);
extern int32_t       kk_js_obj_slot_borrow(kk_box_t box, kk_context_t* ctx);
extern void          kk_js_obj_release_slot(int32_t slot, kk_context_t* ctx);

extern void kk_wasiweb_loop_ref(kk_context_t* ctx);
extern void kk_wasiweb_loop_unref(kk_context_t* ctx);

static const uint8_t* kk_dom_string_borrow(kk_string_t s, size_t* len, kk_context_t* ctx) {
  kk_ssize_t l;
  const uint8_t* buf = kk_string_buf_borrow(s, &l, ctx);
  *len = (size_t)l;
  return buf;
}

// borrow an element box's externref (box stays owned by the caller)
static __externref_t kk_dom_el_borrow(kk_box_t elem, kk_context_t* ctx) {
  return kk_js_obj_get(kk_js_obj_slot_borrow(elem, ctx));
}

//----------------------------------------------
// element operations (called from dom.kk externs; all consume their
// kk_box_t/kk_string_t arguments, kklib convention)
//----------------------------------------------

kk_unit_t kk_domc_set_title(kk_string_t s, kk_context_t* ctx) {
  size_t len; const uint8_t* buf = kk_dom_string_borrow(s, &len, ctx);
  koka_dom_set_title(buf, len);
  kk_string_drop(s, ctx);
  return kk_Unit;
}

kk_unit_t kk_domc_inject_key(kk_string_t s, kk_context_t* ctx) {
  size_t len; const uint8_t* buf = kk_dom_string_borrow(s, &len, ctx);
  koka_dom_inject_key(buf, len);
  kk_string_drop(s, ctx);
  return kk_Unit;
}

kk_unit_t kk_domc_inject_move(double x, double y, kk_context_t* ctx) {
  kk_unused(ctx);
  koka_dom_inject_move(x, y);
  return kk_Unit;
}

kk_unit_t kk_domc_inject_wheel(double x, double y, double dy, kk_context_t* ctx) {
  kk_unused(ctx);
  koka_dom_inject_wheel(x, y, dy);
  return kk_Unit;
}

double kk_domc_event_wheel_dx(kk_context_t* ctx) {
  kk_unused(ctx);
  return koka_dom_event_wheel_dx();
}

double kk_domc_event_wheel_dy(kk_context_t* ctx) {
  kk_unused(ctx);
  return koka_dom_event_wheel_dy();
}

kk_unit_t kk_domc_inject_click(double x, double y, kk_context_t* ctx) {
  kk_unused(ctx);
  koka_dom_inject_click(x, y);
  return kk_Unit;
}

bool kk_domc_inject_text(kk_string_t s, kk_context_t* ctx) {
  size_t len; const uint8_t* buf = kk_dom_string_borrow(s, &len, ctx);
  int32_t ok = koka_dom_inject_text(buf, len);
  kk_string_drop(s, ctx);
  return (ok != 0);
}

int32_t kk_domc_get_element_by_id(kk_string_t id, kk_context_t* ctx) {
  size_t len; const uint8_t* buf = kk_dom_string_borrow(id, &len, ctx);
  __externref_t ref = koka_dom_get_element_by_id(buf, len);
  kk_string_drop(id, ctx);
  if (__builtin_wasm_ref_is_null_extern(ref)) return 0;
  return kk_js_obj_alloc(ref, ctx);
}

int32_t kk_domc_create_element(kk_string_t tag, kk_context_t* ctx) {
  size_t len; const uint8_t* buf = kk_dom_string_borrow(tag, &len, ctx);
  __externref_t ref = koka_dom_create_element(buf, len);
  kk_string_drop(tag, ctx);
  return kk_js_obj_alloc(ref, ctx);
}

int32_t kk_domc_create_text(kk_string_t s, kk_context_t* ctx) {
  size_t len; const uint8_t* buf = kk_dom_string_borrow(s, &len, ctx);
  __externref_t ref = koka_dom_create_text(buf, len);
  kk_string_drop(s, ctx);
  return kk_js_obj_alloc(ref, ctx);
}

void kk_domc_append_child(kk_box_t parent, kk_box_t child, kk_context_t* ctx) {
  koka_dom_append_child(kk_dom_el_borrow(parent, ctx), kk_dom_el_borrow(child, ctx));
  kk_box_drop(parent, ctx); kk_box_drop(child, ctx);
}

void kk_domc_remove_child(kk_box_t parent, kk_box_t child, kk_context_t* ctx) {
  koka_dom_remove_child(kk_dom_el_borrow(parent, ctx), kk_dom_el_borrow(child, ctx));
  kk_box_drop(parent, ctx); kk_box_drop(child, ctx);
}

void kk_domc_replace_child(kk_box_t parent, kk_box_t fresh, kk_box_t old, kk_context_t* ctx) {
  koka_dom_replace_child(kk_dom_el_borrow(parent, ctx), kk_dom_el_borrow(fresh, ctx), kk_dom_el_borrow(old, ctx));
  kk_box_drop(parent, ctx); kk_box_drop(fresh, ctx); kk_box_drop(old, ctx);
}

void kk_domc_set_attribute(kk_box_t elem, kk_string_t name, kk_string_t value, kk_context_t* ctx) {
  size_t nlen; const uint8_t* nbuf = kk_dom_string_borrow(name, &nlen, ctx);
  size_t vlen; const uint8_t* vbuf = kk_dom_string_borrow(value, &vlen, ctx);
  koka_dom_set_attribute(kk_dom_el_borrow(elem, ctx), nbuf, nlen, vbuf, vlen);
  kk_string_drop(name, ctx); kk_string_drop(value, ctx); kk_box_drop(elem, ctx);
}

void kk_domc_remove_attribute(kk_box_t elem, kk_string_t name, kk_context_t* ctx) {
  size_t nlen; const uint8_t* nbuf = kk_dom_string_borrow(name, &nlen, ctx);
  koka_dom_remove_attribute(kk_dom_el_borrow(elem, ctx), nbuf, nlen);
  kk_string_drop(name, ctx); kk_box_drop(elem, ctx);
}

void kk_domc_set_text(kk_box_t elem, kk_string_t text, kk_context_t* ctx) {
  size_t len; const uint8_t* buf = kk_dom_string_borrow(text, &len, ctx);
  koka_dom_set_text(kk_dom_el_borrow(elem, ctx), buf, len);
  kk_string_drop(text, ctx); kk_box_drop(elem, ctx);
}

// JS->Koka string: allocate a scratch buffer, let the host copy its UTF-8
// snapshot in, build a kk_string from it. The host encodes with TextEncoder,
// so the bytes are valid UTF-8 by construction.
kk_string_t kk_domc_get_prop(kk_box_t elem, kk_string_t name, kk_context_t* ctx) {
  __externref_t el = kk_dom_el_borrow(elem, ctx);
  size_t nlen; const uint8_t* nbuf = kk_dom_string_borrow(name, &nlen, ctx);
  int32_t len = koka_dom_get_prop_length(el, nbuf, nlen);
  kk_string_t s;
  if (len <= 0) {
    s = kk_string_empty();
  }
  else {
    uint8_t* buf = (uint8_t*)kk_malloc(len, ctx);
    koka_dom_get_prop_copy(el, buf);
    s = kk_string_alloc_dupn_valid_utf8((kk_ssize_t)len, buf, ctx);
    kk_free(buf, ctx);
  }
  kk_string_drop(name, ctx);
  kk_box_drop(elem, ctx);
  return s;
}

double kk_domc_get_num_prop(kk_box_t elem, kk_string_t name, kk_context_t* ctx) {
  __externref_t el = kk_dom_el_borrow(elem, ctx);
  size_t nlen; const uint8_t* nbuf = kk_dom_string_borrow(name, &nlen, ctx);
  double v = koka_dom_get_num_prop(el, nbuf, nlen);
  kk_string_drop(name, ctx);
  kk_box_drop(elem, ctx);
  return v;
}

void kk_domc_insert_before(kk_box_t parent, kk_box_t child, kk_box_t anchor, kk_context_t* ctx) {
  koka_dom_insert_before(kk_dom_el_borrow(parent, ctx), kk_dom_el_borrow(child, ctx), kk_dom_el_borrow(anchor, ctx));
  kk_box_drop(parent, ctx); kk_box_drop(child, ctx); kk_box_drop(anchor, ctx);
}

int32_t kk_domc_window(kk_context_t* ctx) {
  return kk_js_obj_alloc(koka_dom_window(), ctx);
}

// a fresh (transient) slot for the event being dispatched right now; the
// wrapping Koka `event` value is typically dropped as soon as the message
// is built, releasing the slot immediately.
int32_t kk_domc_current_event(kk_context_t* ctx) {
  return kk_js_obj_alloc(koka_dom_current_event(), ctx);
}

void kk_domc_set_hash(kk_string_t s, kk_context_t* ctx) {
  size_t len; const uint8_t* buf = kk_dom_string_borrow(s, &len, ctx);
  koka_dom_set_hash(buf, len);
  kk_string_drop(s, ctx);
}

//----------------------------------------------
// subscriptions: the host's add-listener returns a subscription record
// (externref) that lands in the same jsobj table; its box carries a
// DIFFERENT free function which -- within the destructor discipline (only
// idempotent fringe calls, no user code) -- tells the host to
// removeEventListener before releasing the slot. Explicit `unsubscribe`
// from Koka does the same eagerly; the host side is idempotent so the
// eventual drop is a harmless no-op repeat.
//----------------------------------------------

static void kk_dom_sub_free_fun(void* p, kk_block_t* block, kk_context_t* ctx) {
  kk_unused(block);
  int32_t slot = (int32_t)(intptr_t)p;
  __externref_t sub = kk_js_obj_get(slot);
  if (!__builtin_wasm_ref_is_null_extern(sub)) {
    koka_dom_remove_listener(sub);  // idempotent host-side
  }
  kk_js_obj_release_slot(slot, ctx);
}

// add a listener: returns the subscription's boxed slot (sub free fun above)
kk_box_t kk_dom_add_listener(kk_box_t elem, kk_string_t event, kk_integer_t listener_id, kk_context_t* ctx) {
  size_t len; const uint8_t* buf = kk_dom_string_borrow(event, &len, ctx);
  uint64_t id = (uint64_t)kk_integer_clamp64(listener_id, ctx);
  __externref_t sub = koka_dom_add_listener(kk_dom_el_borrow(elem, ctx), buf, len, id);
  kk_string_drop(event, ctx); kk_box_drop(elem, ctx);
  int32_t slot = kk_js_obj_alloc(sub, ctx);
  return kk_cptr_raw_box(&kk_dom_sub_free_fun, (void*)(intptr_t)slot, ctx);
}

// eager removeEventListener (host idempotent); slot release still happens at
// the box's drop (exactly once, via kk_dom_sub_free_fun -> release_slot).
void kk_domc_remove_listener_now(kk_box_t sub, kk_context_t* ctx) {
  int32_t slot = kk_js_obj_slot_borrow(sub, ctx);
  __externref_t ref = kk_js_obj_get(slot);
  if (!__builtin_wasm_ref_is_null_extern(ref)) {
    koka_dom_remove_listener(ref);
  }
  kk_box_drop(sub, ctx);
}

// ui/image's `FromPixels` (task 4, web parity): unbox the vector<int8> (a
// kk_vector_t of individually BOXED int8 elements -- not a flat byte buffer,
// so each element needs unboxing) into a scratch uint8 buffer the host can
// read directly out of wasm linear memory, then the length+copy round trip
// (same shape as kk_domc_get_prop above) brings the resulting data-url
// string back.
kk_string_t kk_domc_pixels_to_dataurl(kk_vector_t rgba, int32_t w, int32_t h, kk_context_t* ctx) {
  kk_ssize_t len;
  kk_box_t* elems = kk_vector_buf_borrow(rgba, &len, ctx);
  uint8_t* raw = (uint8_t*)kk_malloc(len > 0 ? len : 1, ctx);
  for (kk_ssize_t i = 0; i < len; i++) {
    raw[i] = (uint8_t)kk_int8_unbox(elems[i], KK_BORROWED, ctx);
  }
  int32_t rlen = koka_dom_pixels_to_dataurl_length(raw, (size_t)len, w, h);
  kk_free(raw, ctx);
  kk_string_t s;
  if (rlen <= 0) {
    s = kk_string_empty();
  }
  else {
    uint8_t* buf = (uint8_t*)kk_malloc(rlen, ctx);
    koka_dom_pixels_to_dataurl_copy(buf);
    s = kk_string_alloc_dupn_valid_utf8((kk_ssize_t)rlen, buf, ctx);
    kk_free(buf, ctx);
  }
  kk_vector_drop(rgba, ctx);
  return s;
}

//----------------------------------------------
// the one stored dispatcher + dispatch-event export (unchanged pattern)
//----------------------------------------------

static bool          kk_dom_dispatcher_set; // = false
static kk_function_t kk_dom_dispatcher;     // valid iff kk_dom_dispatcher_set

void kk_domc_register_dispatcher(kk_function_t dispatch, kk_context_t* ctx) {
  kk_unused(ctx);
  kk_dom_dispatcher = dispatch;
  kk_dom_dispatcher_set = true;
}

__attribute__((export_name("koka:dom/dispatch-event")))
void kk_dom_export_dispatch_event(uint64_t listener_id) {
  kk_context_t* ctx = kk_get_context();
  if (!kk_dom_dispatcher_set) return;
  kk_function_t dispatch = kk_dom_dispatcher;
  kk_function_dup(dispatch, ctx);  // fires repeatedly, never consumed
  kk_integer_t id = kk_integer_from_uint64(listener_id, ctx);
  kk_function_call(kk_unit_t, (kk_function_t, kk_integer_t, kk_context_t*), dispatch, (dispatch, id, ctx), ctx);
  // re-entry into an already-_start-returned instance: flush stdio each time
  // (see evloop.c's kk_wasiweb_dispatch for the full story)
  fflush(NULL);
}

//----------------------------------------------
// evloop keep-alive forwarding (logic in Koka; see dom.kk)
//----------------------------------------------

void kk_domc_loop_ref(kk_context_t* ctx)   { kk_wasiweb_loop_ref(ctx); }
void kk_domc_loop_unref(kk_context_t* ctx) { kk_wasiweb_loop_unref(ctx); }
