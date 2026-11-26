/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting, Microsoft Research, Daan Leijen.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Low-level libuv UDP bindings (mirrors uv/file). A `socket` is an opaque,
// cptr-boxed `uv_udp_t*` (created by bind, freed by close).
module uv/net

import std/num/int32
import uv/evloop

extern import
  c file "net.c"

// Synchronous: create a UDP socket and bind it to host:port. Returns the opaque
// socket handle. (Used via `do-sync`, which supplies the event loop.)
pub extern udp-bind-sync( evloop : any, host : string, port : int32 ) : ioc error<any>
  c "kk_uv_udp_bind_sync"

// Send a datagram to host:port (async; resumes when the send completes).
pub extern udp-send-setup( sock : any, host : string, port : int32, data : bytes, cb : error<()> -> ioc () ) : ioc error<() -> ioc ()>
  c "kk_uv_udp_send"

// Receive one datagram, resuming with (sender-ip, sender-port, payload).
pub extern udp-recv-setup( sock : any, cb : error<(string,int,bytes)> -> ioc () ) : ioc error<() -> ioc ()>
  c "kk_uv_udp_recv"

// Start streaming receive: `cb` is invoked for every datagram until close.
pub extern udp-recv-start( sock : any, cb : error<(string,int,bytes)> -> ioc () ) : ioc error<() -> ioc ()>
  c "kk_uv_udp_recv_start"

// Close and free a socket.
pub extern udp-close-raw( sock : any ) : ioc ()
  c "kk_uv_udp_close"
