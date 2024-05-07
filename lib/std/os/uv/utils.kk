module std/os/uv/utils

import std/os/uv/generated
import std/core/cextern

extern import
  c file "utils-inline"

pub fun owned/keepalive(^s: owned-c<a>): <> ()
  ()

pub fun owned/consume(s: owned-c<a>): <> ()
  ()
  
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

pub extern ptr/uv-loop(): intptr_t
  c inline "(intptr_t)uvloop()"

extern ptr/unit/get-cb(^s: intptr_t): io-event uv-unit-cb
  c inline "kk_function_t fn = kk_function_from_ptr(((uv_handle_t*)#1)->data, kk_context());\n fn"

pub val unit-cb: c-pointer<intptr_t> = C-pointer(unit-cb-addr());

pub extern unit-cb-addr(): intptr_t
  c inline "(intptr_t)kk_uv_unit_callback"

pub val null-cb = C-pointer(0.intptr_t)

pub inline extern fndup(): ()
  c inline "kk_function_dup(_fself, kk_context())"

pub inline extern fndrop(): ()
  c inline "kk_function_drop(_fself, kk_context())"

pub inline fun close(^s: c-pointer<uv-handle-s-c>): io-event ()
  s.uv-close(null-cb)

pub inline fun a/close(a: a, ?uv-handle: (a) -> uv-handle-sp): io-event ()
  a.uv-handle.close()