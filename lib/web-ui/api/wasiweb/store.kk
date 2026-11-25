/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Persistent key/value storage and local files for wasi-web, over the
// "koka:store" core-module imports (store.c). Values are strings (callers
// store JSON); the host keeps them in the browser's localStorage, under a
// per-app prefix, so a different backend (e.g. a cloud database) can be
// swapped in behind the same calls. Picking files is `async`, like fetch.
module web-ui/api/wasiweb/store

import std/num/int32
import std/num/float64
import std/async
import std/async/internal
import web-ui/api/wasiweb/jsobj
import web-ui/api/wasiweb/dom

extern import
  c file "store.c"

extern get-raw(key : string) : ioc int32
  c "kk_storec_get"

extern set-raw(key : string, value : string) : ioc ()
  c "kk_storec_set"

extern remove-raw(key : string) : ioc ()
  c "kk_storec_remove"

extern keys-raw(pre : string) : ioc int32
  c "kk_storec_keys"

extern pick-files-raw(accept : string, directory : bool) : ioc int32
  c "kk_storec_pick_files"

extern download-raw(name : string, text : string) : ioc ()
  c "kk_storec_download"

// The stored value, or Nothing if the key is not set.
pub fun store-get(key : string) : ioc maybe<string>
  val r = Element(jsobj/box(get-raw(key)))
  if r.num-prop("has") == 0.0 then Nothing else Just(r.get-prop("value"))

pub fun store-set(key : string, value : string) : ioc ()
  set-raw(key, value)

pub fun store-remove(key : string) : ioc ()
  remove-raw(key)

// The keys starting with `pre`, as a JSON array of strings.
pub fun store-keys-json(pre : string) : ioc string
  Element(jsobj/box(keys-raw(pre))).get-prop("value")

// Let the user pick files (or a whole directory) and read them as text:
// a JSON array of {"name", "path", "text"} (empty if they cancel).
pub fun pick-files(accept : string = "", directory : bool = False) : <async,ioc> string
  val target = Element(jsobj/box(pick-files-raw(accept, directory)))
  val done = channel()
  val s = target.subscribe("done") fn()
    done.emit-io(current-event().prop("files"))
  val r = done.receive
  unsubscribe(s)
  r

// Offer `text` to the user as a file download named `name`.
pub fun download(name : string, text : string) : ioc ()
  download-raw(name, text)
