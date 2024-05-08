/*---------------------------------------------------------------------------
  Copyright 2023 Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

module std/os/event-loop

import std/core/cextern
import std/num/int32
import std/os/uv/generated
import std/os/uv/utils

extern import
  c { conan="libuv[>=1.47.0]"; vcpkg="libuv"; library="uv" }
// TODO: wasm {}

extern import
  c file "event-loop-inline.c"

// Handles a uv loop
pub fun default-event-loop(action)
  if host() == "libc" then
    handle-loop(action)
  else // TODO: Support event loop on other platforms
    action()

val @initialize = init-uv-alloc()

// Runs a UV loop
fun handle-loop(action)
  init-loop()
  val res = action() 
  run-loop()
  close-loop()
  res

abstract extend type exception-info
  pub con AsyncExn( status-code : uv-errno-t )

extern run-loop(): io-event ()
  c "kk_uv_loop_run"
  wasm "kk_emscripten_loop_run"
  js inline ""
  cs inline ""

extern init-loop(): io-event ()
  c "kk_uv_loop_init"
  wasm inline "kk_Unit"
  js inline ""
  cs inline ""

// initializes only the allocators (not an event loop)
// needed for some file operations which alloc - kk_uv_fs_mkdtemp, kk_uv_fs_mkstemp
pub extern init-uv-alloc(): ()
  c "kk_uv_alloc_init"
  wasm inline "kk_Unit"
  cs inline ""
  js inline ""

extern close-loop(): io-event ()
  c "kk_uv_loop_close"
  wasm inline "kk_Unit"
  cs inline ""
  js inline ""

pub inline fun hnd/close(hnd: c-pointer<uv-handle-s-c>, callback: () -> io-event ()): io-event ()
  hnd.close(callback)

pub extern ptr/close(hnd: intptr_t, callback: () -> io-event ()): io-event ()
  c "kk_uv_close"
  wasm inline "kk_Unit"
  cs inline ""
  js inline ""

pub fun error-from-uverr<a>(code: int32): exn error<a>
  val code' = code.int/uv-errno-t
  Error(Exception(code'.message, AsyncExn(code')))

pub inline fun result/untry(code: int, a: () -> a): exn a
  if code == 0 then a()
  else 
    val code' = code.int32.int/uv-errno-t
    throw-exn(Exception(code'.message, AsyncExn(code'))) // TODO: Errno refactoring

pub inline fun unit/untry(code: int): exn ()
  if code == 0 then ()
  else
    val code' = code.int32.int/uv-errno-t 
    throw-exn(Exception(code'.message, AsyncExn(code')))

pub fun message(code: uv-errno-t): string
  match code
    UV_E2BIG -> "argument list too long"
    UV_EACCES -> "permission denied"
    UV_EADDRINUSE -> "address already in use"
    UV_EADDRNOTAVAIL -> "address not available"
    UV_EAFNOSUPPORT -> "address family not supported"
    UV_EAGAIN -> "resource temporarily unavailable"
    UV_EAI_ADDRFAMILY -> "address family not supported"
    UV_EAI_AGAIN -> "temporary failure"
    UV_EAI_BADFLAGS -> "bad ai_flags value"
    UV_EAI_BADHINTS -> "invalid value for hints"
    UV_EAI_CANCELED -> "request canceled"
    UV_EAI_FAIL -> "permanent failure"
    UV_EAI_FAMILY -> "ai_family not supported"
    UV_EAI_MEMORY -> "out of memory"
    UV_EAI_NODATA -> "no address"
    UV_EAI_NONAME -> "unknown node or service"
    UV_EAI_OVERFLOW -> "argument buffer overflow"
    UV_EAI_PROTOCOL -> "resolved protocol is unknown"
    UV_EAI_SERVICE -> "service not available for socket type"
    UV_EAI_SOCKTYPE -> "socket type not supported"
    UV_EALREADY -> "connection already in progress"
    UV_EBADF -> "bad file descriptor"
    UV_EBUSY -> "resource busy or locked"
    UV_ECANCELED -> "operation canceled"
    UV_ECHARSET -> "invalid Unicode character"
    UV_ECONNABORTED -> "software caused connection abort"
    UV_ECONNREFUSED -> "connection refused"
    UV_ECONNRESET -> "connection reset by peer"
    UV_EDESTADDRREQ -> "destination address required"
    UV_EEXIST -> "file already exists"
    UV_EFAULT -> "bad address in system call argument"
    UV_EFBIG -> "file too large"
    UV_EHOSTUNREACH -> "host is unreachable"
    UV_EINTR -> "interrupted system call"
    UV_EINVAL -> "invalid argument"
    UV_EIO -> "i/o error"
    UV_EISCONN -> "socket is already connected"
    UV_EISDIR -> "illegal operation on a directory"
    UV_ELOOP -> "too many symbolic links encountered"
    UV_EMFILE -> "too many open files"
    UV_EMSGSIZE -> "message too long"
    UV_ENAMETOOLONG -> "name too long"
    UV_ENETDOWN -> "network is down"
    UV_ENETUNREACH -> "network is unreachable"
    UV_ENFILE -> "file table overflow"
    UV_ENOBUFS -> "no buffer space available"
    UV_ENODEV -> "no such device"
    UV_ENOENT -> "no such file or directory"
    UV_ENOMEM -> "not enough memory"
    UV_ENONET -> "machine is not on the network"
    UV_ENOPROTOOPT -> "protocol not available"
    UV_ENOSPC -> "no space left on device"
    UV_ENOSYS -> "function not implemented"
    UV_ENOTCONN -> "socket is not connected"
    UV_ENOTDIR -> "not a directory"
    UV_ENOTEMPTY -> "directory not empty"
    UV_ENOTSOCK -> "socket operation on non-socket"
    UV_ENOTSUP -> "operation not supported on socket"
    UV_EOVERFLOW -> "value too large to be stored in data type"
    UV_EPERM -> "operation not permitted"
    UV_EPIPE -> "broken pipe"
    UV_EPROTO -> "protocol error"
    UV_EPROTONOSUPPORT -> "protocol not supported"
    UV_EPROTOTYPE -> "protocol wrong type for socket"
    UV_ERANGE -> "result too large"
    UV_EROFS -> "read-only file system"
    UV_ESHUTDOWN -> "cannot send after transport endpoint shutdown"
    UV_ESPIPE -> "invalid seek"
    UV_ESRCH -> "no such process"
    UV_ETIMEDOUT -> "connection timed out"
    UV_ETXTBSY -> "text file is busy"
    UV_EXDEV -> "cross-device link not permitted"
    UV_UNKNOWN -> "unknown error"
    UV_EOF -> "end of file"
    UV_ENXIO -> "no such device or address"
    UV_EMLINK -> "too many links"
    UV_EHOSTDOWN -> "host is down"
    UV_EREMOTEIO -> "remote I/O error"
    UV_ENOTTY -> "inappropriate ioctl for device"
    UV_EFTYPE -> "inappropriate file type or format"
    UV_EILSEQ -> "illegal byte sequence"
    UV_ESOCKTNOSUPPORT -> "socket type not supported"
    UV_ENODATA -> "no data available"
    UV_EUNATCH -> "protocol driver not attached"
    UV_ERRNO_MAX -> "unknown error"