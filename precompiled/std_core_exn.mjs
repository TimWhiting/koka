// Koka generated module: std/core/exn, koka version: 3.2.4
"use strict";
 
// imports
import * as $std_core_types from './std_core_types.mjs';
import * as $std_core_hnd from './std_core_hnd.mjs';
 
// externals
/*---------------------------------------------------------------------------
  Copyright 2012-2024, Microsoft Research, Daan Leijen.
  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/
/* assign here so inlined primitives are available in system.core itself */
const $std_core_exn = {// primitive operations emitted by the compiler
                        "_throw_exception": _throw_exception
                      , "_error_from_exception": _error_from_exception
                      , "_unsupported_external": _unsupported_external
                      }
/*------------------------------------------------
  Exceptions
------------------------------------------------*/
function _exn_capture_stack(exn) {
  /*
  if ("captureStackTrace" in Error) {
    Error.captureStackTrace(exn,_InfoException);  // best on Node.js
  }
  else
  */
  {
    exn.stack = (new Error()).stack; // in browsers
  }
  if (exn.stack==null) exn.stack = "";
  // strip off leaf functions from the stack trace
  exn.stack = exn.stack.replace(/\n\s*at (exn_exception|exception|(Object\.)?throw_1|Object\.error|exn_error_pattern|Object\.error_pattern|exn_error_range|Object\._vector_at)\b.*/g,"");
}
function exn_stacktrace( exn ) {
  if (exn instanceof Error && typeof exn.stack === "string") {
    return exn.stack;
  }
  else {
    return "";
  }
}
function exn_info( exn ) {
  //console.log("exn_info: " + exn.stack);
  /*
  if (exn instanceof _InfoException && exn.info != null) {
    return exn.info;
  }
  else if (exn instanceof _InfoSystemException && exn.info != null) {
    return exn.info;
  }
  else if (exn instanceof _FinalizeException) {
    return Finalize;
  }
  else if (exn instanceof AssertionError) {
    return Assert;
  }
  else
  */
  if (exn instanceof RangeError) {
    return ExnRange;
  }
  else if (exn instanceof Error && typeof exn.code === "string" ) {
    return ExnSystem(exn.code);
  }
  else {
    return ExnError;
  }
}
function exn_message( exn ) {
  if (exn==null) {
    return "invalid error";
  }
  if (typeof exn.get_message === "function") { // for FinalizeException
    var msg = exn.get_message();
    if (typeof msg === "string") return msg;
  }
  if (typeof exn.message === "string") {
    return exn.message;
  }
  else if (typeof exn === "string") {
    return exn;
  }
  else if (typeof exn.toString === "function") {
    return exn.toString();
  }
  else {
    return "Unknown error";
  };
}
// Throw a JavaScript exception as a Koka exception
export function _throw_exception( exn ) {
  var st  = exn_stacktrace(exn);
  var exc = Exception( exn_message(exn) + (st ? "\n" + st : ""), exn_info(exn) );
  return throw_exn(exc);
}
export function _error_from_exception( exn ) {
  var st  = exn_stacktrace(exn);
  var exc = Exception( exn_message(exn) + (st ? "\n" + st : ""), exn_info(exn) );
  return $Error(exc);
}
export function _unsupported_external( msg ) {
  _throw_exception(msg);
}
 
// type declarations
 
 
// runtime tag for the effect `:exn`
export var exn_fs__tag;
var exn_fs__tag = "exn@exn";
 
export var _tag_ExnError;
var _tag_ExnError = "std/core/exn/ExnError";
 
export var _tag_ExnAssert;
var _tag_ExnAssert = "std/core/exn/ExnAssert";
 
export var _tag_ExnTodo;
var _tag_ExnTodo = "std/core/exn/ExnTodo";
 
export var _tag_ExnRange;
var _tag_ExnRange = "std/core/exn/ExnRange";
 
export var _tag_ExnPattern;
var _tag_ExnPattern = "std/core/exn/ExnPattern";
 
export var _tag_ExnSystem;
var _tag_ExnSystem = "std/core/exn/ExnSystem";
 
export var _tag_ExnInternal;
var _tag_ExnInternal = "std/core/exn/ExnInternal";
// type exception-info
export const ExnError = { _tag: _tag_ExnError }; // exception-info
export const ExnAssert = { _tag: _tag_ExnAssert }; // exception-info
export const ExnTodo = { _tag: _tag_ExnTodo }; // exception-info
export const ExnRange = { _tag: _tag_ExnRange }; // exception-info
export function ExnPattern(location, definition) /* (location : string, definition : string) -> exception-info */  {
  return { _tag: _tag_ExnPattern, location: location, definition: definition };
}
export function ExnSystem(errno) /* (errno : int) -> exception-info */  {
  return { _tag: _tag_ExnSystem, errno: errno };
}
export function ExnInternal(name) /* (name : string) -> exception-info */  {
  return { _tag: _tag_ExnInternal, name: name };
}
// type exception
export function Exception(message, info) /* (message : string, info : exception-info) -> exception */  {
  return { message: message, info: info };
}
// type error
export function $Error(exception) /* forall<a> (exception : exception) -> error<a> */  {
  return { _tag: 1, exception: exception };
}
export function Ok(result) /* forall<a> (result : a) -> error<a> */  {
  return { _tag: 2, result: result };
}
// type exn
export function _Hnd_exn(_cfc, _brk_throw_exn) /* forall<e,a> (int, forall<b> hnd/clause1<exception,b,exn,e,a>) -> exn<e,a> */  {
  return { _cfc: _cfc, _brk_throw_exn: _brk_throw_exn };
}
 
// declarations
 
 
// Automatically generated. Retrieves the `@cfc` constructor field of the `:exn` type.
export function exn_fs__cfc(exn_0) /* forall<e,a> (exn : exn<e,a>) -> int */  {
  return exn_0._cfc;
}
 
 
// handler for the effect `:exn`
export function exn_fs__handle(hnd, ret, action) /* forall<a,e,b> (hnd : exn<e,b>, ret : (res : a) -> e b, action : () -> <exn|e> a) -> e b */  {
  return $std_core_hnd._hhandle(exn_fs__tag, hnd, ret, action);
}
 
 
// Automatically generated. Retrieves the `@brk-throw-exn` constructor field of the `:exn` type.
export function exn_fs__brk_throw_exn(exn_0) /* forall<e,a,b> (exn : exn<e,a>) -> hnd/clause1<exception,b,exn,e,a> */  {
  return exn_0._brk_throw_exn;
}
 
 
// select `throw-exn` operation out of effect `:exn`
export function throw_exn_fs__select(hnd) /* forall<a,e,b> (hnd : exn<e,b>) -> hnd/clause1<exception,a,exn,e,b> */  {
  return hnd._brk_throw_exn;
}
 
 
// Throw an exception
// Call the `final ctl throw-exn` operation of the effect `:exn`
export function throw_exn(exn_0) /* forall<a> (exn : exception) -> exn a */  {
   
  var ev_10032 = $std_core_hnd._evv_at(0);
  var _x0 = ev_10032.hnd._brk_throw_exn;
  return _x0(ev_10032.marker, ev_10032, exn_0);
}
 
 
// Automatically generated. Retrieves the `info` constructor field of the `:exception` type.
export function exception_fs_info(exception) /* (exception : exception) -> exception-info */  {
  return exception.info;
}
 
 
// Automatically generated. Retrieves the `message` constructor field of the `:exception` type.
export function exception_fs_message(exception) /* (exception : exception) -> string */  {
  return exception.message;
}
 
export function exception_fs__copy(_this, message, info) /* (exception, message : ? string, info : ? exception-info) -> exception */  {
  if (message !== undefined) {
    var _x1 = message;
  }
  else {
    var _x1 = _this.message;
  }
  if (info !== undefined) {
    var _x2 = info;
  }
  else {
    var _x2 = _this.info;
  }
  return Exception(_x1, _x2);
}
 
 
// Throw an exception with a specified message.
export function $throw(message, info) /* forall<a> (message : string, info : ? exception-info) -> exn a */  {
   
  var ev_10035 = $std_core_hnd._evv_at(0);
  var _x3 = ev_10035.hnd._brk_throw_exn;
  var _x4 = (info !== undefined) ? info : ExnError;
  return _x3(ev_10035.marker, ev_10035, Exception(message, _x4));
}
 
 
// Raise a pattern match exception. This is function is used internally by the
// compiler to generate error messages on pattern match failures.
export function error_pattern(location, definition) /* forall<a> (location : string, definition : string) -> exn a */  {
   
  var message_10003 = $std_core_types._lp__plus__plus__rp_(location, $std_core_types._lp__plus__plus__rp_(": ", $std_core_types._lp__plus__plus__rp_(definition, ": pattern match failure")));
   
  var ev_10038 = $std_core_hnd._evv_at(0);
  var _x5 = ev_10038.hnd._brk_throw_exn;
  return _x5(ev_10038.marker, ev_10038, Exception(message_10003, ExnPattern(location, definition)));
}
 
 
// Automatically generated. Tests for the `ExnError` constructor of the `:exception-info` type.
export function is_exnError(exception_info) /* (exception-info : exception-info) -> bool */  {
  return (exception_info._tag === _tag_ExnError);
}
 
 
// Automatically generated. Tests for the `ExnAssert` constructor of the `:exception-info` type.
export function is_exnAssert(exception_info) /* (exception-info : exception-info) -> bool */  {
  return (exception_info._tag === _tag_ExnAssert);
}
 
 
// Automatically generated. Tests for the `ExnTodo` constructor of the `:exception-info` type.
export function is_exnTodo(exception_info) /* (exception-info : exception-info) -> bool */  {
  return (exception_info._tag === _tag_ExnTodo);
}
 
 
// Automatically generated. Tests for the `ExnRange` constructor of the `:exception-info` type.
export function is_exnRange(exception_info) /* (exception-info : exception-info) -> bool */  {
  return (exception_info._tag === _tag_ExnRange);
}
 
 
// Automatically generated. Tests for the `ExnPattern` constructor of the `:exception-info` type.
export function is_exnPattern(exception_info) /* (exception-info : exception-info) -> bool */  {
  return (exception_info._tag === _tag_ExnPattern);
}
 
 
// Automatically generated. Tests for the `ExnSystem` constructor of the `:exception-info` type.
export function is_exnSystem(exception_info) /* (exception-info : exception-info) -> bool */  {
  return (exception_info._tag === _tag_ExnSystem);
}
 
 
// Automatically generated. Tests for the `ExnInternal` constructor of the `:exception-info` type.
export function is_exnInternal(exception_info) /* (exception-info : exception-info) -> bool */  {
  return (exception_info._tag === _tag_ExnInternal);
}
 
 
// Show the exception message
export function show(exn_0) /* (exn : exception) -> string */  {
  return exn_0.message;
}
 
 
// Catch any exception raised in `action` and handle it.
// Use `on-exit` when appropriate.
export function handle_fs_try(action, hndl) /* forall<a,e> (action : () -> <exn|e> a, hndl : (exception) -> e a) -> e a */  {
  return exn_fs__handle(_Hnd_exn(0, function(m /* hnd/marker<657,656> */ , ___wildcard_x654__16 /* hnd/ev<exn> */ , x /* exception */ ) {
        return $std_core_hnd.yield_to_final(m, function(___wildcard_x654__45 /* (hnd/resume-result<638,656>) -> 657 656 */ ) {
            return hndl(x);
          });
      }), function(_res /* 656 */ ) {
      return _res;
    }, action);
}
 
 
// monadic lift
export function error_fs__mlift_try_10030(_y_x10022) /* forall<a,e> (a) -> <exn|e> error<a> */  {
  return Ok(_y_x10022);
}
 
 
// Transform an exception effect to an  `:error` type.
export function error_fs_try(action) /* forall<a,e> (action : () -> <exn|e> a) -> e error<a> */  {
  return exn_fs__handle(_Hnd_exn(0, function(m /* hnd/marker<705,error<704>> */ , ___wildcard_x654__16 /* hnd/ev<exn> */ , x /* exception */ ) {
        return $std_core_hnd.yield_to_final(m, function(___wildcard_x654__45 /* (hnd/resume-result<638,error<704>>) -> 705 error<704> */ ) {
            return $Error(x);
          });
      }), function(_res /* error<704> */ ) {
      return _res;
    }, function() {
       
      var x_0_10043 = action();
      if ($std_core_hnd._yielding()) {
        return $std_core_hnd.yield_extend(function(_y_x10022 /* 704 */ ) {
          return Ok(_y_x10022);
        });
      }
      else {
        return Ok(x_0_10043);
      }
    });
}
 
 
// Catch an exception raised by `throw` and handle it.
// This is `try` but with the arguments reversed, and is
// often convenient to use as `with catch fn(e) ...`
export function $catch(hndl, action) /* forall<a,e> (hndl : (exception) -> e a, action : () -> <exn|e> a) -> e a */  {
  return exn_fs__handle(_Hnd_exn(0, function(m /* hnd/marker<736,735> */ , ___wildcard_x654__16 /* hnd/ev<exn> */ , x /* exception */ ) {
        return $std_core_hnd.yield_to_final(m, function(___wildcard_x654__45 /* (hnd/resume-result<638,735>) -> 736 735 */ ) {
            return hndl(x);
          });
      }), function(_res /* 735 */ ) {
      return _res;
    }, action);
}
 
 
// Automatically generated. Tests for the `Error` constructor of the `:error` type.
export function is_error(error) /* forall<a> (error : error<a>) -> bool */  {
  return (error._tag === 1);
}
 
 
// Automatically generated. Tests for the `Ok` constructor of the `:error` type.
export function is_ok(error) /* forall<a> (error : error<a>) -> bool */  {
  return (error._tag === 2);
}
 
 
// Transform an `:error` type back to an `exn` effect.
export function untry(err) /* forall<a> (err : error<a>) -> exn a */  {
  if (err._tag === 1) {
     
    var ev_10047 = $std_core_hnd._evv_at(0);
    var _x6 = ev_10047.hnd._brk_throw_exn;
    return _x6(ev_10047.marker, ev_10047, err.exception);
  }
  else {
    return err.result;
  }
}
 
 
// Transform an `:error` type back to an `exn` effect.
export function exn(err) /* forall<a> (err : error<a>) -> exn a */  {
  return untry(err);
}
 
 
// Use default value `def` in case of an error.
export function $default(t, def) /* forall<a> (t : error<a>, def : a) -> a */  {
  return (t._tag === 1) ? def : t.result;
}
 
 
// Transform an `:error` type to a `:maybe` value.
export function maybe(t) /* forall<a> (t : error<a>) -> maybe<a> */  {
  if (t._tag === 1) {
    return $std_core_types.Nothing;
  }
  else {
    return $std_core_types.Just(t.result);
  }
}
 
 
// Transform an `:error` type to an `:either` value.
export function either(t) /* forall<a> (t : error<a>) -> either<exception,a> */  {
  if (t._tag === 1) {
    return $std_core_types.Left(t.exception);
  }
  else {
    return $std_core_types.Right(t.result);
  }
}
 
 
// Set a `hndler` that is always called when the `action` finishes (either normally or with an exception).
export function on_exit(hndler, action) /* forall<a,e> (hndler : () -> e (), action : () -> e a) -> e a */  {
  return $std_core_hnd.finally_prompt(hndler, action());
}
 
export function exn_error_range() /* forall<a> () -> exn a */  {
   
  var ev_10052 = $std_core_hnd._evv_at(0);
  var _x7 = ev_10052.hnd._brk_throw_exn;
  return _x7(ev_10052.marker, ev_10052, Exception("index out-of-range", ExnRange));
}
 
 
// Prepend `exn`'s message with `pre`.
export function prepend(exn_0, pre) /* (exn : exception, pre : string) -> exception */  {
  var _x8 = exn_0.message;
  var _x9 = exn_0.info;
  return Exception($std_core_types._lp__plus__plus__rp_(pre, $std_core_types._lp__plus__plus__rp_(": ", _x8)), _x9);
}