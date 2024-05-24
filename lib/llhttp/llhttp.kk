/*---------------------------------------------------------------------------
  Copyright 2024 Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

module llhttp

import llhttp-capi

// An HTTP request object
pub struct http-req
  method: string
  url: string
  version: string
  headers: list<(string, string)>
  body: string

// An HTTP response object
pub struct http-res
  version: string
  status: string
  headers: list<(string, string)>
  body: string

// Shows a HTTP request as a string
pub fun req/show(h: http-req): string
  h.method ++ " " ++ h.url ++ " " ++ "HTTP/" ++ h.version ++ "\r\n" ++ 
  h.headers.map(fn((k, v)) k ++ ": " ++ v).join("\r\n") ++ "\r\n\r\n"

// Shows a HTTP response as a string
pub fun res/show(h: http-res): string
  "HTTP/" ++ h.version ++ " " ++ h.status ++ "\r\n" ++
  h.headers.map(fn((k, v)) k ++ ": " ++ v).join("\r\n") ++ "\r\n\r\n"

// An effect that encapsulates the statefulness of parsing an HTTP message
// This is okay to escape it's scope due to none of the clauses being `ctl` clauses
pub named effect http-parser<r>
  fun add-string(s: string): ()
  fun add-bytes(s: bytes): ()
  fun is-finished(): bool
  fun get-result(): r

// Creates a new HTTP request parser
pub fun http-req-parser(): io-event ev<http-parser<http-req>>
  val method = ref("")
  val version = ref("")
  val url = ref("")
  val headers = ref(Nil)
  val body = ref("")
  val header-key = ref("")
  val done = ref(False)
  val l = init(default-settings(), HTTP_REQUEST.int)
  l.set-on-version fn(s)
    version := s
    0.int32
  l.set-on-url fn(s)
    url := s
    0.int32
  l.set-on-method fn(s)
    method := s
    0.int32
  l.set-on-header-field fn(s)
    header-key := s
    0.int32
  l.set-on-header-value fn(s)
    headers := Cons((!header-key, s), !headers)
    0.int32
  l.set-on-body fn(s)
    body := s
    0.int32
  l.set-on-message-complete fn()
    done := True
    0.int32
  with parser <- named handler
    fun add-string(s: string)
      l.execute(s)
      ()
    fun add-bytes(s: bytes)
      l.execute(s)
      ()
    fun is-finished()
      !done
    fun get-result()
      Http-req(!method, !url, !version, !headers, !body)
  parser

// Creates a new HTTP response parser
pub fun http-res-parser(): io-event ev<http-parser<http-res>>
  val version = ref("")
  val status = ref("")
  val headers = ref(Nil)
  val body = ref("")
  val header-key = ref("")
  val done = ref(False)
  val l = init(default-settings(), HTTP_RESPONSE.int)
  l.set-on-version fn(s)
    version := s
    0.int32
  l.set-on-status fn(s)
    status := s
    0.int32
  l.set-on-header-field fn(s)
    header-key := s
    0.int32
  l.set-on-header-value fn(s)
    headers := Cons((!header-key, s), !headers)
    0.int32
  l.set-on-body fn(s)
    body := s
    0.int32
  l.set-on-message-complete fn()
    done := True
    0.int32
  with parser <- named handler
    fun add-string(s: string)
      l.execute(s)
      ()
    fun add-bytes(s: bytes)
      l.execute(s)
      ()
    fun is-finished()
      !done
    fun get-result()
      Http-res(!version, !status, !headers, !body)
  parser
