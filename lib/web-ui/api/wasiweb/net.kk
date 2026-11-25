/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Network fringe for wasi-web: WebSocket and fetch over the "koka:net"
// core-module imports (net.c). A connection's reports come back as ordinary
// DOM events on the JS object, so they reuse dom.kk's `subscribe` and
// `current-event` -- no second dispatcher, and no callbacks in the public API:
// WebSocket events arrive on a channel, a fetch is an `async` call.
module web-ui/api/wasiweb/net

import std/num/int32
import std/num/float64
import std/async
import std/async/internal
import web-ui/api/wasiweb/jsobj
import web-ui/api/wasiweb/dom

extern import
  c file "net.c"

// ----------------------------------------------------------------
// WebSocket

// An open (or opening) WebSocket: Perceus-owned like an `element`; dropping
// the last reference releases the wasm-side slot but does not close it.
pub value struct websocket(target : element)

pub type ws-event
  WsOpen
  WsMessage( data : string )   // text frames only
  WsClose( code : int )
  WsError

extern ws-open-raw(url : string) : ioc int32
  c "kk_netc_ws_open"

extern ws-send-raw(ws : any, data : string) : ioc ()
  c "kk_netc_ws_send"

extern ws-close-raw(ws : any) : ioc ()
  c "kk_netc_ws_close"

// Start connecting to `url` ("ws://host/path"); watch `events` for `WsOpen`.
pub fun ws-open(url : string) : ioc websocket
  Websocket(Element(jsobj/box(ws-open-raw(url))))

// Send a text frame; silently dropped unless the socket is open.
pub fun websocket/send(ws : websocket, data : string) : ioc ()
  ws-send-raw(ws.target.obj, data)

pub fun websocket/close(ws : websocket) : ioc ()
  ws-close-raw(ws.target.obj)

// 0 connecting, 1 open, 2 closing, 3 closed
pub fun websocket/ready-state(ws : websocket) : ioc int
  ws.target.num-prop("readyState").int

// Bytes queued but not yet sent: lets a real-time sender skip a frame
// instead of building a backlog on a slow link.
pub fun websocket/buffered-amount(ws : websocket) : ioc int
  ws.target.num-prop("bufferedAmount").int

// The socket's events as a channel. The listeners are removed again after
// the close event, so a reconnect does not accumulate subscriptions.
pub fun websocket/events(ws : websocket) : <async,ndet> channel<ws-event>
  val ch = channel()
  async-ioc
    val subs = ref([])
    val on-close = fn()
      ch.emit-io(WsClose(current-event().num-prop("code").int))
      (!subs).foreach(unsubscribe)
      subs := []
    subs := [ ws.target.subscribe("open", fn() ch.emit-io(WsOpen)),
              ws.target.subscribe("message", fn() ch.emit-io(WsMessage(current-event().prop("data")))),
              ws.target.subscribe("error", fn() ch.emit-io(WsError)),
              ws.target.subscribe("close", on-close) ]
  ch

// ----------------------------------------------------------------
// fetch

// An HTTP response; `status` is 0 when the request failed outright
// (network error, CORS), with the error message in `text`.
pub struct response( status : int, text : string )

pub fun response/ok(r : response) : bool
  r.status >= 200 && r.status < 300

extern fetch-start-raw(method : string, url : string, headers : string, body : string, timeout-ms : int32) : ioc int32
  c "kk_netc_fetch_start"

// fetch(url) and wait for the whole response body as text. `headers` are
// (name, value) pairs, e.g. [("Authorization", "Bearer ...")]; with
// `timeout-ms` > 0 the request is abandoned after that long (status 0).
pub fun fetch(url : string, method : string = "GET", body : string = "",
              headers : list<(string,string)> = [], timeout-ms : int = 0) : <async,ioc> response
  val hdrs = headers.map(fn((k, v)) k ++ ": " ++ v).join("\n")
  val target = Element(jsobj/box(fetch-start-raw(method, url, hdrs, body, timeout-ms.int32)))
  val done = channel()
  // the host resolves the request asynchronously, so subscribing after the
  // start cannot miss the "done" event
  val s = target.subscribe("done") fn()
    val ev = current-event()
    done.emit-io(Response(ev.num-prop("status").int, ev.prop("text")))
  val r = done.receive
  unsubscribe(s)
  r
