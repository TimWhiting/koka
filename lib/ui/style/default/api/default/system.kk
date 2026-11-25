/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// wasi-web + native: no portable OS color-scheme query yet, so default to dark.
// (wasi-web could read `prefers-color-scheme` through a host shim; native could
// query the platform appearance -- both are follow-ups behind this façade.)
module ui/style/default/api/default/system

// True when the OS prefers a dark color scheme (defaults to dark here)
pub fun system-dark() : ioc bool
  True
