/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Theming as an algebraic effect. `theme` is a reader effect that view code
// consumes wherever it needs a color; the app shell HANDLES it by binding a
// palette (`with val theme = dark`). Nothing threads a theme parameter
// through components and nothing is global: the handler is the scope, and
// switching themes is just handling the same views with a different value.
module web-ui/theme

import web-ui/html

pub struct palette
  bg      : string   // page background
  fg      : string   // text
  accent  : string   // highlights (links, counts, primary buttons)
  surface : string   // cards / list rows

pub val light : palette = Palette("#f7f7fb", "#1a1a2e", "#3454d1", "#ffffff")
pub val dark  : palette = Palette("#16161e", "#e6e6f0", "#7aa2f7", "#232433")

// the ambient theme: views read it, the shell binds it
pub effect val theme : palette

// style attribute painting an element with the theme's page colors
pub fun page-style<msg>( extra : string = "" ) : theme attr<msg>
  style("background:" ++ theme.bg ++ ";color:" ++ theme.fg
        ++ (if extra.is-empty then "" else ";" ++ extra))

// style attribute for raised surfaces (cards, list rows)
pub fun surface-style<msg>( extra : string = "" ) : theme attr<msg>
  style("background:" ++ theme.palette/surface ++ ";color:" ++ theme.fg
        ++ (if extra.is-empty then "" else ";" ++ extra))

// style attribute for accented text
pub fun accent-style<msg>( extra : string = "" ) : theme attr<msg>
  style("color:" ++ theme.accent
        ++ (if extra.is-empty then "" else ";" ++ extra))
