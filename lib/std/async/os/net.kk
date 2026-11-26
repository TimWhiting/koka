/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting, Microsoft Research, Daan Leijen.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// High-level async UDP sockets (libuv-backed). MVP: bind + close.
module async/os/net

import std/async
pub import std/async/internal   // re-export event-loop alias (Parc needs the def downstream)
import std/num/int32
import async/api/uv/net

// An open UDP socket (opaque libuv handle).
pub value struct udp-socket( ptr : any )

// Create a UDP socket bound to `host`:`port` (IPv4 or IPv6).
pub fun udp-bind( host : string, port : int ) : _ udp-socket
  val sock = ref(Nothing)
  do-sync fn(evloop)
    match udp-bind-sync(evloop, host, port.int32)
      Error(e) -> Error(e)
      Ok(h) ->
        sock := Just(h)
        Ok(())
  match !sock
    Just(h) -> Udp-socket(h)
    Nothing -> throw("udp-bind: internal error")

// Send a datagram to `host`:`port`.
pub fun udp-send( s : udp-socket, host : string, port : int, data : bytes ) : _ ()
  await("udp-send", fn(_evloop, resume) udp-send-setup(s.ptr, host, port.int32, data, resume))
  ()

// Receive one datagram: (sender-ip, sender-port, payload).
pub fun udp-recv( s : udp-socket ) : _ (string, int, bytes)
  await("udp-recv", fn(_evloop, resume) udp-recv-setup(s.ptr, resume))

fun emit-result( ch : channel<(string,int,bytes)>, res : error<(string,int,bytes)> ) : ioc ()
  match res
    Ok(dg)   -> emit-io(ch, dg)
    Error(_) -> ()

// Start receiving datagrams onto a channel (until the socket is closed).
pub fun udp-listen( s : udp-socket ) : _ channel<(string,int,bytes)>
  val ch = channel()
  do-sync fn(_evloop)
    match udp-recv-start(s.ptr, fn(res) emit-result(ch, res))
      Error(e) -> Error(e)
      Ok(_)    -> Ok(())
  ch

// Close a UDP socket.
pub fun udp-close( s : udp-socket ) : _ ()
  do-sync fn(_evloop)
    udp-close-raw(s.ptr)
    Ok(())
