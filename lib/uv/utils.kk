module uv/utils

import uv/generated
import uv/error
import std/core/cextern

extern import
  c file "inline/utils"

// Needs to be extern otherwise, the compiler will optimize out the function and not keep the reference alive
// Ensure that a reference is > 1 until after this point
pub extern owned/keepalive(^s: owned-c<a>): <> ()
  ""

// Release a reference (decref an owned reference)
pub fun owned/release(s: owned-c<a>): <> ()
  ()

// Retain a reference (incref an owned reference)
pub extern owned/retain(s: owned-c<a>): <> ()
  ""
  
pub alias uv-cb2<a,b> = (a, b) -> io-event () 
pub alias uv-cb1<a> = (a) -> io-event () 
pub alias uv-unit-cb = () -> io-event ()

pub inline fun a/set-cb(a: a, f: uv-unit-cb, ?uv-handle: (a) -> uv-handle-sp): <> ()
  a.uv-handle.uv-handle/unit/set-cb(f)

pub inline fun uv-handle/unit/set-cb(^s: c-pointer<uv-handle-s-c>, f: uv-unit-cb): <> ()
  s.ptr/unit/set-cb(f)

inline extern ptr/unit/set-cb(^s: c-pointer<a>, f: uv-unit-cb): <> ()
  c inline "((uv_handle_t*)#1)->data = (void*)kk_function_as_ptr(#2, kk_context())"
  wasm inline "kk_Unit"

pub fun a/get-cb(a: a, ?uv-handle: (a) -> uv-handle-sp): io-event uv-unit-cb
  a.uv-handle.uv-handle/unit/get-cb()

pub fun uv-handle/unit/get-cb(^s: c-pointer<uv-handle-s-c>): io-event uv-unit-cb
  s.ptr/unit/get-cb()

extern ptr/unit/get-cb(^s: c-pointer<a>): io-event uv-unit-cb
  c inline "kk_function_t fn = kk_function_from_ptr(((uv_handle_t*)#1)->data, kk_context());\n fn"
  wasm inline "kk_function_t t;\n t"

pub val unit-cb: c-pointer<intptr_t> = unit-cb-addr();

pub extern unit-cb-addr(): c-pointer<intptr_t>
  c inline "(intptr_t)kk_uv_unit_callback"
  wasm inline "0"
  js inline "0"

pub val null-cb = 0.intptr_t

pub inline extern int/ptr(i: intptr_t): c-pointer<t>
  c inline "(intptr_t)#1"
  wasm inline "0"

pub inline extern ptr/uv-loop(): io-event c-pointer<uv-loop-s-c>
  c inline "(intptr_t)uvloop()"
  wasm inline "0"

pub inline extern fndup(): ()
  c inline "kk_function_dup(_fself, kk_context())"
  wasm inline ""

// Just the fact that f is an owned parameter will cause a dup
pub inline extern unit/fndup(f: uv-unit-cb): ()
  c inline ""

// Just the fact that f is an owned parameter will cause a dup
pub inline extern single/fndup(f: uv-cb1<a>): ()
  c inline ""

// Just the fact that f is an owned parameter will cause a dup
pub inline extern double/fndup(f: uv-cb2<a,b>): ()
  c inline ""

pub inline extern fndrop(): ()
  c inline "kk_function_drop(_fself, kk_context())"

pub inline extern unit/fndrop(f: uv-unit-cb): ()
  c inline "kk_function_drop(#1, kk_context())"

pub inline extern single/fndrop(f: uv-cb1<a>): ()
  c inline "kk_function_drop(#1, kk_context())"

pub inline extern double/fndrop(f: uv-cb2<a,b>): ()
  c inline "kk_function_drop(#1, kk_context())"

pub inline fun close(^s: c-pointer<uv-handle-s-c>): io-event ()
  s.uv-close(0.intptr_t.int/ptr)

pub inline fun a/close(a: a, ?uv-handle: (a) -> uv-handle-sp): io-event ()
  a.uv-handle.close()

pub inline fun hnd/close(hnd: c-pointer<uv-handle-s-c>, callback: () -> io-event ()): io-event ()
  hnd.close(callback)


