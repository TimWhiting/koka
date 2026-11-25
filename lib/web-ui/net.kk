/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Network access (WebSocket, fetch), selecting a backend per host like
// `web-ui/dom`. Only `wasi-web` is implemented so far.
module web-ui/net

pub import web-ui/api/net
  [host=wasi-web] web-ui/api/wasiweb/net
