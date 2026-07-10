/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// The default style library: `import ui/style/default` for the palette + theme
// effect, the styled components, and the OS light/dark query. This is ONE
// swappable style layer over the style-agnostic `ui/widget` core; an
// alternative design language would be a sibling (e.g. `ui/style/material`)
// exposing the same component names with its own palette and painting.
module ui/style/default

pub import ui/state   // ephemeral state + the identity implicits stateful components need
pub import ui/style/default/theme
pub import ui/style/default/components
pub import ui/style/default/system
