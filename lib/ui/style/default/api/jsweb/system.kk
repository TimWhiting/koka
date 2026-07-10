/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// jsweb: the OS preference is the browser's `prefers-color-scheme` media query.
module ui/style/default/api/jsweb/system

import web-ui/dom

// True when the user's OS/browser prefers a dark color scheme
pub fun system-dark() : ioc bool
  prefers-dark()
