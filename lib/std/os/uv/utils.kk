module std/os/uv/utils

import std/os/uv/generated
import std/core/cextern

extern import
  c file "utils-inline"

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
  a.uv-handle.set-cb(f)

pub fun unit/set-cb(^s: c-pointer<uv-handle-s-c>, f: uv-unit-cb): <> ()
  s.ptr.set-cb(f)

inline extern ptr/unit/set-cb(^s: intptr_t, f: uv-unit-cb): <> ()
  c inline "((uv_handle_t*)#1)->data = (void*)kk_function_as_ptr(#2, kk_context())"

pub fun a/get-cb(a: a, ?uv-handle: (a) -> uv-handle-sp): io-event uv-unit-cb
  a.uv-handle.get-cb()

pub fun unit/get-cb(^s: c-pointer<uv-handle-s-c>): io-event uv-unit-cb
  s.ptr.get-cb()

pub extern ptr/uv-loop(): io-event intptr_t
  c inline "(intptr_t)uvloop()"

extern ptr/unit/get-cb(^s: intptr_t): io-event uv-unit-cb
  c inline "kk_function_t fn = kk_function_from_ptr(((uv_handle_t*)#1)->data, kk_context());\n fn"

pub val unit-cb: c-pointer<intptr_t> = C-pointer(unit-cb-addr());

pub extern unit-cb-addr(): intptr_t
  c inline "(intptr_t)kk_uv_unit_callback"

pub val null-cb = C-pointer(0.intptr_t)

pub inline extern fndup(): ()
  c inline "kk_function_dup(_fself, kk_context())"

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
  s.ptr.external/uv-close(0.intptr_t)

pub inline fun a/close(a: a, ?uv-handle: (a) -> uv-handle-sp): io-event ()
  a.uv-handle.close()