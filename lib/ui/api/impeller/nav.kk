/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Native implementation of the `ui/nav` façade: there is no browser URL, so
// the hash is an in-memory store plus a channel the backend ticks whenever a
// `Link` is clicked (see the impeller backend's pointer handling). This makes
// `ui/router` work identically on native; a real in-app history stack /
// back-forward gestures are a later addition behind this same façade.
module ui/api/impeller/nav

import std/async
import std/core/unsafe

// module-global navigation state (the native analogue of `window.location`).
// The change channel is created LAZILY on first `hash-events()` -- a channel
// must not be built at module-init time (the async runtime is not up yet), and
// `hash-events` runs inside the running app (the `route-sub` strand).
val nav-cur : ref<global,string>             = unsafe-total{ ref("") }
val nav-ch  : ref<global,maybe<channel<()>>> = unsafe-total{ ref(Nothing) }

// the current hash (e.g. "#/todos"), or "" when nothing has been navigated
pub fun current-hash() : ioc string
  !nav-cur

// set the hash and notify the subscriber (if `route-sub` has started). A plain
// `ioc` emit -- matches the web façade and the backend's pointer handler.
pub fun goto-hash( s : string ) : ioc ()
  nav-cur := s
  match !nav-ch
    Just(c) -> c.emit-io(())
    Nothing -> ()               // no route-sub yet: current-hash still updated

// the change channel, created on first use (inside the running app)
pub fun hash-events() : <async,ioc> channel<()>
  match !nav-ch
    Just(c) -> c
    Nothing ->
      val c = channel()
      nav-ch := Just(c)
      c
