/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Material 3 theme: a subset of the M3 color roles as an ambient effect. This
// is a SEPARATE style library from `ui/style/default` -- it has its OWN theme
// type (there is no universal token schema), and its own components (see
// `components`). An app imports one style library and uses its component names.
module ui/style/material/theme

import ui/widget

// a Material 3 color scheme (the roles the button set needs)
pub struct material-theme
  primary                : color
  on-primary             : color
  secondary-container    : color
  on-secondary-container : color
  surface                : color
  surface-container      : color
  on-surface             : color
  outline                : color
  background             : color
  on-background          : color

// M3 baseline light scheme
pub val light : material-theme = Material-theme(
  primary                = rgb(0.404, 0.314, 0.643),
  on-primary             = rgb(1.0, 1.0, 1.0),
  secondary-container    = rgb(0.910, 0.871, 0.973),
  on-secondary-container = rgb(0.114, 0.098, 0.169),
  surface                = rgb(0.996, 0.969, 1.0),
  surface-container      = rgb(0.933, 0.910, 0.949),
  on-surface             = rgb(0.114, 0.106, 0.125),
  outline                = rgb(0.475, 0.455, 0.494),
  background             = rgb(0.996, 0.969, 1.0),
  on-background          = rgb(0.114, 0.106, 0.125) )

// M3 baseline dark scheme
pub val dark : material-theme = Material-theme(
  primary                = rgb(0.816, 0.737, 1.0),
  on-primary             = rgb(0.220, 0.118, 0.447),
  secondary-container    = rgb(0.290, 0.267, 0.345),
  on-secondary-container = rgb(0.910, 0.871, 0.973),
  surface                = rgb(0.078, 0.071, 0.094),
  surface-container      = rgb(0.129, 0.122, 0.149),
  on-surface             = rgb(0.902, 0.878, 0.914),
  outline                = rgb(0.576, 0.561, 0.600),
  background             = rgb(0.078, 0.071, 0.094),
  on-background          = rgb(0.902, 0.878, 0.914) )

// interpolate two schemes -- bind `theme` to a mix driven by an animated t
// and the WHOLE ui crossfades coherently (one t, no per-widget shear)
pub fun material-theme/mix( a : material-theme, b : material-theme, t : float64 ) : material-theme
  Material-theme(
    primary                = a.primary.mix(b.primary, t),
    on-primary             = a.on-primary.mix(b.on-primary, t),
    secondary-container    = a.secondary-container.mix(b.secondary-container, t),
    on-secondary-container = a.on-secondary-container.mix(b.on-secondary-container, t),
    surface                = a.surface.mix(b.surface, t),
    surface-container      = a.surface-container.mix(b.surface-container, t),
    on-surface             = a.on-surface.mix(b.on-surface, t),
    outline                = a.outline.mix(b.outline, t),
    background             = a.background.mix(b.background, t),
    on-background          = a.on-background.mix(b.on-background, t) )

// the ambient Material theme (parallels `ui/style/default`'s `theme`, but over
// the Material scheme)
pub effect val theme : material-theme
