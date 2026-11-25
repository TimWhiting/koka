/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// #include <kklib.h>  -- textually pasted into net.kk's generated .c via
// `extern import c file` (same convention as dom.c/jsobj.c).

// Network fringe: plain wasm core-module imports under the "koka:net"
// namespace (implemented by support/wasi-web/web-ui-host.js). Only the calls
// that start or drive a connection live here; everything a connection
// reports back (open/message/close, a finished fetch) arrives as an ordinary
// DOM event on the returned JS object, through dom.c's listener machinery.

//----------------------------------------------
// raw imports
//----------------------------------------------

// new WebSocket(url): the socket itself is the event target
__attribute__((import_module("koka:net"), import_name("ws-open")))
extern __externref_t koka_net_ws_open(const uint8_t* ptr, size_t len);

// send a text frame (dropped host-side unless the socket is open)
__attribute__((import_module("koka:net"), import_name("ws-send")))
extern void koka_net_ws_send(__externref_t ws, const uint8_t* ptr, size_t len);

__attribute__((import_module("koka:net"), import_name("ws-close")))
extern void koka_net_ws_close(__externref_t ws);

// start fetch(url, {method, headers, body}); `headers` is "Name: value"
// lines, `timeout_ms` > 0 aborts the request after that long. Returns an
// EventTarget that fires one "done" event carrying `status` (0 on a network
// error or timeout) and `text`
__attribute__((import_module("koka:net"), import_name("fetch-start")))
extern __externref_t koka_net_fetch_start(const uint8_t* mptr, size_t mlen,
                                          const uint8_t* uptr, size_t ulen,
                                          const uint8_t* hptr, size_t hlen,
                                          const uint8_t* bptr, size_t blen,
                                          int32_t timeout_ms);

//----------------------------------------------
// helpers from sibling modules (non-static, forward-declared)
//----------------------------------------------

extern int32_t       kk_js_obj_alloc(__externref_t ref, kk_context_t* ctx);
extern __externref_t kk_js_obj_get(int32_t slot);
extern int32_t       kk_js_obj_slot_borrow(kk_box_t box, kk_context_t* ctx);

static const uint8_t* kk_net_string_borrow(kk_string_t s, size_t* len, kk_context_t* ctx) {
  kk_ssize_t l;
  const uint8_t* buf = kk_string_buf_borrow(s, &l, ctx);
  *len = (size_t)l;
  return buf;
}

static __externref_t kk_net_obj_borrow(kk_box_t obj, kk_context_t* ctx) {
  return kk_js_obj_get(kk_js_obj_slot_borrow(obj, ctx));
}

//----------------------------------------------
// operations (called from net.kk externs; all consume their arguments)
//----------------------------------------------

int32_t kk_netc_ws_open(kk_string_t url, kk_context_t* ctx) {
  size_t len; const uint8_t* buf = kk_net_string_borrow(url, &len, ctx);
  __externref_t ws = koka_net_ws_open(buf, len);
  kk_string_drop(url, ctx);
  return kk_js_obj_alloc(ws, ctx);
}

kk_unit_t kk_netc_ws_send(kk_box_t ws, kk_string_t data, kk_context_t* ctx) {
  size_t len; const uint8_t* buf = kk_net_string_borrow(data, &len, ctx);
  koka_net_ws_send(kk_net_obj_borrow(ws, ctx), buf, len);
  kk_string_drop(data, ctx); kk_box_drop(ws, ctx);
  return kk_Unit;
}

kk_unit_t kk_netc_ws_close(kk_box_t ws, kk_context_t* ctx) {
  koka_net_ws_close(kk_net_obj_borrow(ws, ctx));
  kk_box_drop(ws, ctx);
  return kk_Unit;
}

int32_t kk_netc_fetch_start(kk_string_t method, kk_string_t url, kk_string_t headers, kk_string_t body, int32_t timeout_ms, kk_context_t* ctx) {
  size_t mlen; const uint8_t* mbuf = kk_net_string_borrow(method, &mlen, ctx);
  size_t ulen; const uint8_t* ubuf = kk_net_string_borrow(url, &ulen, ctx);
  size_t hlen; const uint8_t* hbuf = kk_net_string_borrow(headers, &hlen, ctx);
  size_t blen; const uint8_t* bbuf = kk_net_string_borrow(body, &blen, ctx);
  __externref_t target = koka_net_fetch_start(mbuf, mlen, ubuf, ulen, hbuf, hlen, bbuf, blen, timeout_ms);
  kk_string_drop(method, ctx); kk_string_drop(url, ctx); kk_string_drop(headers, ctx); kk_string_drop(body, ctx);
  return kk_js_obj_alloc(target, ctx);
}
