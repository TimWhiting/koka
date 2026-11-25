/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// The OS light/dark preference, selected per host: `system-dark()` is the
// user's `prefers-color-scheme` on the browser (jsweb) and defaults to dark
// elsewhere (wasi-web + native fall back until a platform query lands). An app
// reads it once at init to pick its starting palette; a toggle can override.
module ui/style/default/system

pub import ui/style/default/api/system
  [host=jsweb]         ui/style/default/api/jsweb/system
  [host=wasi-web|libc] ui/style/default/api/default/system
