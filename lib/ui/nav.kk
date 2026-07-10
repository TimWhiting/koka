/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// The portable navigation façade, selected per host like `ui/backend`. It
// exposes the current location hash, a way to set it, and a channel that
// ticks on every change:
//
//   get-hash()    : the current hash (e.g. "#/todos"), or "" when empty
//   set-hash(s)   : set it (fires a change; on the web this records history)
//   hash-events() : a channel that receives () after each change
//
// On the web these ARE `window.location.hash` and the "hashchange" event, so
// links, deep-links and back/forward come from the browser. Natively they are
// an in-memory store + channel the backend pushes to when a `Link` is clicked.
// `ui/router` is built entirely on these three, so routing is portable. The
// History API is a future drop-in behind the same façade.
module ui/nav

pub import ui/api/nav
  [host=wasi-web|jsweb] ui/api/web/nav
  [host=libc]           ui/api/impeller/nav
