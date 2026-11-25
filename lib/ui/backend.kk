/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// The platform backend interface, selected per host (like std/async's event
// loop and web-ui/dom): mount a widget tree, re-render it, and pump platform
// input as messages. `mounted<msg>` is abstract -- a vdom tree over
// absolutely-positioned DOM on web, a laid-out tree + window on native.
module ui/backend

pub import ui/api/backend
  [host=wasi-web|jsweb] ui/api/web/backend
  [host=libc]           ui/api/impeller/backend
