#pragma once
#include "kklib.h"
#ifndef KK_WASM_H
#define KK_WASM_H
#include <stdint.h>
#include <stdlib.h>

#define WASM_EXPORT(name) \
  __attribute__((export_name(#name))) \
  name
#define WASM_IMPORT(mod, name) \
  __attribute__((import_module(#mod))) \
  __attribute__((import_name(#name))) \
  name

#define ASSERT(x) do { if (!(x)) __builtin_trap(); } while (0)

typedef __externref_t externref;

void WASM_IMPORT(rt, invoke)(externref, int);
void WASM_IMPORT(rt, out_of_memory)(void);

void WASM_IMPORT(env, wasm_log)(void*);
void WASM_IMPORT(env, wasm_logobj)(externref);
void WASM_IMPORT(env, wasm_logi)(int);
externref WASM_IMPORT(env, to_jsstring)(char*);
externref WASM_IMPORT(env, to_jsnumber)(int*);
externref WASM_IMPORT(env, js_property_get)(externref, externref);
void WASM_IMPORT(env, js_property_set)(externref, externref, externref);
externref WASM_IMPORT(env, js_function_call1)(externref, externref);
externref WASM_IMPORT(env, js_global_this)();
externref WASM_IMPORT(env, js_undefined)();
externref WASM_IMPORT(env, js_null)();
externref WASM_IMPORT(env, js_true)();
externref WASM_IMPORT(env, js_false)();

typedef uint32_t Handle;

Handle intern(externref obj, kk_context_t* ctx);
externref handle_value(Handle h);
Handle kk_js_get_prop(Handle obj, const uint8_t *prop, kk_context_t* ctx);
void kk_js_set_prop(Handle obj, const uint8_t *prop, Handle obj2, kk_context_t* ctx);
Handle kk_js_function_call_1(Handle obj, Handle obj1, kk_context_t* ctx);
Handle logObject(Handle obj);
void kk_js_init(kk_context_t* ctx);

extern Handle jsGlobalThis;
extern Handle jsNull;
extern Handle jsUndefined;
extern Handle jsTrue;
extern Handle jsFalse;

#endif // KK_WASM_H
