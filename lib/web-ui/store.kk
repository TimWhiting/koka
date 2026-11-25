/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Persistent storage and local files, selecting a backend per host like
// `web-ui/net`. Only `wasi-web` is implemented so far.
module web-ui/store

pub import web-ui/api/store
  [host=wasi-web] web-ui/api/wasiweb/store
