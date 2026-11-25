/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// #include <kklib.h>  -- textually pasted into store.kk's generated .c via
// `extern import c file` (same convention as dom.c/net.c).

// Storage and file fringe: wasm core-module imports under "koka:store"
// (support/wasi-web/web-ui-host.js). Reads return a small JS object whose
// string/number properties store.kk reads back with dom's get-prop/num-prop;
// picking files returns an EventTarget that fires one "done" event.

__attribute__((import_module("koka:store"), import_name("get")))
extern __externref_t koka_store_get(const uint8_t* kptr, size_t klen);

__attribute__((import_module("koka:store"), import_name("set")))
extern void koka_store_set(const uint8_t* kptr, size_t klen, const uint8_t* vptr, size_t vlen);

__attribute__((import_module("koka:store"), import_name("remove")))
extern void koka_store_remove(const uint8_t* kptr, size_t klen);

__attribute__((import_module("koka:store"), import_name("keys")))
extern __externref_t koka_store_keys(const uint8_t* pptr, size_t plen);

__attribute__((import_module("koka:store"), import_name("pick-files")))
extern __externref_t koka_store_pick_files(const uint8_t* aptr, size_t alen, int32_t directory);

__attribute__((import_module("koka:store"), import_name("download")))
extern void koka_store_download(const uint8_t* nptr, size_t nlen, const uint8_t* tptr, size_t tlen);

extern int32_t kk_js_obj_alloc(__externref_t ref, kk_context_t* ctx);

static const uint8_t* kk_store_borrow(kk_string_t s, size_t* len, kk_context_t* ctx) {
  kk_ssize_t l;
  const uint8_t* buf = kk_string_buf_borrow(s, &l, ctx);
  *len = (size_t)l;
  return buf;
}

int32_t kk_storec_get(kk_string_t key, kk_context_t* ctx) {
  size_t klen; const uint8_t* k = kk_store_borrow(key, &klen, ctx);
  __externref_t r = koka_store_get(k, klen);
  kk_string_drop(key, ctx);
  return kk_js_obj_alloc(r, ctx);
}

kk_unit_t kk_storec_set(kk_string_t key, kk_string_t value, kk_context_t* ctx) {
  size_t klen; const uint8_t* k = kk_store_borrow(key, &klen, ctx);
  size_t vlen; const uint8_t* v = kk_store_borrow(value, &vlen, ctx);
  koka_store_set(k, klen, v, vlen);
  kk_string_drop(key, ctx); kk_string_drop(value, ctx);
  return kk_Unit;
}

kk_unit_t kk_storec_remove(kk_string_t key, kk_context_t* ctx) {
  size_t klen; const uint8_t* k = kk_store_borrow(key, &klen, ctx);
  koka_store_remove(k, klen);
  kk_string_drop(key, ctx);
  return kk_Unit;
}

int32_t kk_storec_keys(kk_string_t prefix, kk_context_t* ctx) {
  size_t plen; const uint8_t* p = kk_store_borrow(prefix, &plen, ctx);
  __externref_t r = koka_store_keys(p, plen);
  kk_string_drop(prefix, ctx);
  return kk_js_obj_alloc(r, ctx);
}

int32_t kk_storec_pick_files(kk_string_t accept, bool directory, kk_context_t* ctx) {
  size_t alen; const uint8_t* a = kk_store_borrow(accept, &alen, ctx);
  __externref_t r = koka_store_pick_files(a, alen, directory ? 1 : 0);
  kk_string_drop(accept, ctx);
  return kk_js_obj_alloc(r, ctx);
}

kk_unit_t kk_storec_download(kk_string_t name, kk_string_t text, kk_context_t* ctx) {
  size_t nlen; const uint8_t* n = kk_store_borrow(name, &nlen, ctx);
  size_t tlen; const uint8_t* t = kk_store_borrow(text, &tlen, ctx);
  koka_store_download(n, nlen, t, tlen);
  kk_string_drop(name, ctx); kk_string_drop(text, ctx);
  return kk_Unit;
}
