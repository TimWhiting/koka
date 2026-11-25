/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// The Material 3 style library: `import ui/style/material` for the M3 color
// scheme (`theme`/`light`/`dark`) and the M3 button set (`filled-button`,
// `elevated-button`, `filled-tonal-button`, `text-button`). A sibling of
// `ui/style/default` over the same style-agnostic `ui/widget` core -- swapping
// the import swaps the design language.
module ui/style/material

pub import ui/state   // ephemeral state + interaction identity the components need
pub import ui/style/base
pub import ui/style/material/theme
pub import ui/style/material/components
