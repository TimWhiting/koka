/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// The DEFAULT style library's theme: a palette over typed colors carried by an
// ambient reader effect. `ui/widget` (the core) is style-agnostic and has NO
// theme dependency -- this module and `components` are one *swappable* style
// layer (a future `ui/style/material` would be a sibling with its own palette
// and its own token schema; there is deliberately no universal token set).
//
// Token delivery is a hybrid (see `components`): pages / large components read
// this ambient effect (`theme.accent`), and leaf components take pure implicit
// tokens (`?bg`) that a component boundary bridges from the effect -- so the
// effect keeps deep signatures clean while leaves stay overridable per call.
module ui/style/default/theme

import ui/widget

pub struct palette
  bg      : color   // page background
  fg      : color   // text
  accent  : color   // highlights
  surface : color   // cards / rows

pub val light : palette = Palette(rgb(0.968, 0.968, 0.984), rgb(0.102, 0.102, 0.180),
                                  rgb(0.204, 0.329, 0.820), rgb(1.0, 1.0, 1.0))
pub val dark  : palette = Palette(rgb(0.086, 0.086, 0.118), rgb(0.902, 0.902, 0.941),
                                  rgb(0.478, 0.635, 0.969), rgb(0.137, 0.141, 0.200))

// interpolate two palettes -- bind `theme` to a mix driven by an animated t
// and the WHOLE ui crossfades coherently (one t, no per-widget shear)
pub fun palette/mix( a : palette, b : palette, t : float64 ) : palette
  Palette(a.bg.mix(b.bg, t), a.fg.mix(b.fg, t),
          a.accent.mix(b.accent, t), a.surface.mix(b.surface, t))

// the ambient theme: views read it, the shell binds it
pub effect val theme : palette
