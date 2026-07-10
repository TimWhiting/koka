/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Styled components: app-themed widgets defined once and used throughout.
// Each one consumes the `theme` effect (their types say so: `theme html<msg>`),
// so every page that builds its view under `with val theme = ...` gets a
// consistent look — and a theme switch restyles all of them at once.
module web-ui/ui

import web-ui/html
import web-ui/theme

// a filled, accent-colored button (primary actions)
pub fun primary-button<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : theme html<msg>
  button([style("background:" ++ theme.accent ++ ";color:#ffffff;border:none;"
                ++ "border-radius:6px;padding:6px 14px;cursor:pointer")] ++ attrs,
         children)

// a quiet button on the surface color (secondary actions)
pub fun quiet-button<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : theme html<msg>
  button([style("background:" ++ theme.palette/surface ++ ";color:" ++ theme.fg
                ++ ";border:1px solid " ++ theme.accent ++ "55;"
                ++ "border-radius:6px;padding:6px 12px;cursor:pointer")] ++ attrs,
         children)

// a text input styled to the theme
pub fun text-input<msg>( attrs : list<attr<msg>> = [] ) : theme html<msg>
  input([style("background:" ++ theme.palette/surface ++ ";color:" ++ theme.fg
               ++ ";border:1px solid " ++ theme.accent ++ "44;"
               ++ "border-radius:6px;padding:6px 10px")] ++ attrs)

// children on a raised, themed surface
pub fun card<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : theme html<msg>
  section([surface-style("border-radius:10px;padding:12px 16px;"
                         ++ "box-shadow:0 1px 3px rgba(0,0,0,0.18)")] ++ attrs,
          children)

// a page: accent heading over its content, spaced as a column
pub fun page<msg>( title : string, children : list<html<msg>> = [] ) : theme html<msg>
  section([], [column([], Cons(h2([accent-style()], [text(title)]), children))])

// ----------------------------------------------------------------
// layout utilities: flexbox rows/columns with regular spacing, so views
// never hand-write display:flex

// children left-to-right, vertically centered, evenly gapped
pub fun row<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [], gap : string = "10px" ) : html<msg>
  div([style("display:flex;flex-direction:row;align-items:center;gap:" ++ gap)] ++ attrs,
      children)

// children top-to-bottom, evenly gapped
pub fun column<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [], gap : string = "12px" ) : html<msg>
  div([style("display:flex;flex-direction:column;align-items:flex-start;gap:" ++ gap)] ++ attrs,
      children)

// children centered both ways
pub fun centered<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  div([style("display:flex;justify-content:center;align-items:center")] ++ attrs,
      children)

// an empty element that greedily takes the remaining space of its flexbox
// parent — put one before a footer to push it to the bottom
pub fun spacer<msg>() : html<msg>
  div([style("flex:1 1 auto")], [])
