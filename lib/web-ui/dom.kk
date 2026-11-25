/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// The DOM fringe interface, selecting a backend implementation per host
// (like `std/async`'s event loop): `wasi-web` talks to the host page over
// `koka:dom` imports with a Perceus-owned externref table; `jsweb` calls
// the DOM directly with inline javascript.
module web-ui/dom

pub import web-ui/api/dom
  [host=wasi-web] web-ui/api/wasiweb/dom
  [host=jsweb]    web-ui/api/jsweb/dom
