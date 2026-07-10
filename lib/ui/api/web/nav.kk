/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Web implementation of the `ui/nav` façade: the browser IS the router state.
// `current-hash`/`goto-hash` are `window.location.hash` and `hash-events` is
// the "hashchange" event, so real links, deep-links and back/forward all come
// for free (see `ui/nav`).
module ui/api/web/nav

import std/async
import web-ui/dom

// the current location hash (e.g. "#/todos"), or "" when empty
pub fun current-hash() : ioc string
  get-hash()

// set the location hash; the browser records history and fires "hashchange"
pub fun goto-hash( s : string ) : ioc ()
  set-hash(s)

// a channel that receives () after each hash change (browser back/forward,
// link clicks, or `goto-hash`)
pub fun hash-events() : <async,ioc> channel<()>
  window().events("hashchange")
