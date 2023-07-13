/*---------------------------------------------------------------------------
  Copyright 2021, Microsoft Research, Daan Leijen.

  This is free software; you can redibibute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this dibibution.
---------------------------------------------------------------------------*/
#include "kklib.h"

typedef uint32_t Handle;

struct js_freelist {
  Handle handle;
  struct js_freelist *next;
};

static struct js_freelist *js_freelist = 0;

static Handle freelist_pop (kk_context_t* ctx) {
  ASSERT(js_freelist != 0x0);
  struct js_freelist *head = js_freelist;
  Handle ret = head->handle;
  js_freelist = head->next;
  kk_free(head, ctx);
  return ret;
}

static void freelist_push (Handle h, kk_context_t* ctx) {
  struct js_freelist *head = kk_malloc(sizeof(struct js_freelist), ctx);
  if (!head) {
    out_of_memory();
    __builtin_trap();
  }
  head->handle = h;
  head->next = js_freelist;
  js_freelist = head;
}

static externref objects[0];

static void expand_table(kk_context_t* ctx) {
  size_t old_size = __builtin_wasm_table_size(objects);
  size_t grow = (old_size >> 1) + 1;
  if (__builtin_wasm_table_grow(objects,
                                __builtin_wasm_ref_null_extern(),
                                grow) == -1) {
    out_of_memory();
    __builtin_trap();
  }
  size_t end = __builtin_wasm_table_size(objects);
  while (end != old_size) {
    freelist_push (--end, ctx);
  }
}

Handle intern(externref obj, kk_context_t* ctx) {
  if (!js_freelist) expand_table(ctx);
  Handle ret = freelist_pop(ctx);
  __builtin_wasm_table_set(objects, ret, obj);
  return ret;
}

void release(Handle h, kk_context_t* ctx) {
  if (h == (uint32_t)-1) return;
  __builtin_wasm_table_set(objects, h, __builtin_wasm_ref_null_extern());
  freelist_push(h, ctx);
}

externref handle_value(Handle h) {
  return h == (uint32_t)-1
    ? __builtin_wasm_ref_null_extern()
    : __builtin_wasm_table_get(objects, h);
}

Handle kk_js_get_prop(Handle obj, const uint8_t *prop, kk_context_t* ctx) {
  externref jsObj = handle_value(obj);
  externref jsProp = to_jsstring(prop);
  externref jsVal = js_property_get(jsObj, jsProp);
  return intern(jsVal, ctx);
}

void kk_js_set_prop(Handle obj, const uint8_t *prop, Handle obj2, kk_context_t* ctx) {
  externref jsObj = handle_value(obj);
  externref jsProp = to_jsstring(prop);
  externref jsObj2 = handle_value(obj2);
  js_property_set(jsObj, jsProp, jsObj2);
}

Handle kk_js_function_call_1(Handle obj, Handle obj1, kk_context_t* ctx){
  externref jsObj = handle_value(obj);
  externref jsObj1 = handle_value(obj1);
  externref jsVal = js_function_call1(jsObj, jsObj1);
  // TODO: Check for known values? null / bool, undefined etc?
  return intern(jsVal, ctx);
}

Handle jsGlobalThis;
Handle jsNull;
Handle jsUndefined;
Handle jsTrue;
Handle jsFalse;
void kk_js_init(kk_context_t* ctx){
  jsFalse = intern(js_false(), ctx);
  jsTrue = intern(js_true(), ctx);
  jsUndefined = intern(js_undefined(), ctx);
  jsNull = intern(js_null(), ctx);
  jsGlobalThis = intern(js_global_this(), ctx);
  return;
}

Handle logObject(Handle obj){
  externref jsObj = handle_value(obj);
  wasm_logobj(jsObj);
  return obj;
} 