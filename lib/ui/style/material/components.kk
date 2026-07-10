/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Material 3 components, built on the style-agnostic `ui/style/base` (raw
// `button` + `styled-paint`). Each Material button type is a base `button` with
// a `button-style` DERIVED from the ambient Material theme -- passed as the
// `style` argument whose default reads the theme, and overridable per call.
// This is the swap point: an app that imports `ui/style/material` gets the same
// call shape as `ui/style/default` but the Material look.
module ui/style/material/components

import std/num/float64
import ui/widget
import ui/state
import ui/style/base
import ui/style/material/theme

// a translucent state layer of `c` (M3 hover/press over a transparent button)
fun layer( c : color, alpha : float64 ) : color
  Color(c.r, c.g, c.b, alpha)

// ---- style providers: derive a `button-style` from the Material scheme ----

pub fun filled-style() : theme button-style
  val t = theme
  Button-style(bg = t.primary, fg = t.on-primary,
               hover = t.primary.brighten(1.25), pressed = t.primary.brighten(0.78))

pub fun tonal-style() : theme button-style
  val t = theme
  Button-style(bg = t.secondary-container, fg = t.on-secondary-container,
               hover = t.secondary-container.brighten(1.22), pressed = t.secondary-container.brighten(0.80))

pub fun elevated-style() : theme button-style
  val t = theme
  Button-style(bg = t.surface-container, fg = t.primary,
               hover = t.surface-container.brighten(1.25), pressed = t.surface-container.brighten(0.78))

pub fun text-style() : theme button-style
  val t = theme
  Button-style(bg = layer(t.primary, 0.0), fg = t.primary,       // transparent container
               hover = layer(t.primary, 0.16), pressed = layer(t.primary, 0.26))

// ---- the Material button set (filled / elevated / tonal / text) ----
// each: `simple/*` takes a label, `widget/*` takes any child.

pub fun simple/filled-button<msg>( label : string, on-click : msg, style : button-style = filled-style(),
                                   ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc,theme> widget<msg>
  button( text(label, 15.0, style.fg), on-click, paint = styled-paint(style) )
pub fun widget/filled-button<msg>( child : widget<msg>, on-click : msg, style : button-style = filled-style(),
                                   ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc,theme> widget<msg>
  button( child, on-click, paint = styled-paint(style) )

pub fun simple/elevated-button<msg>( label : string, on-click : msg, style : button-style = elevated-style(),
                                     ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc,theme> widget<msg>
  button( text(label, 15.0, style.fg), on-click, paint = styled-paint(style) )
pub fun widget/elevated-button<msg>( child : widget<msg>, on-click : msg, style : button-style = elevated-style(),
                                     ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc,theme> widget<msg>
  button( child, on-click, paint = styled-paint(style) )

pub fun simple/filled-tonal-button<msg>( label : string, on-click : msg, style : button-style = tonal-style(),
                                         ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc,theme> widget<msg>
  button( text(label, 15.0, style.fg), on-click, paint = styled-paint(style) )
pub fun widget/filled-tonal-button<msg>( child : widget<msg>, on-click : msg, style : button-style = tonal-style(),
                                         ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc,theme> widget<msg>
  button( child, on-click, paint = styled-paint(style) )

pub fun simple/text-button<msg>( label : string, on-click : msg, style : button-style = text-style(),
                                 ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc,theme> widget<msg>
  button( text(label, 15.0, style.fg), on-click, paint = styled-paint(style) )
pub fun widget/text-button<msg>( child : widget<msg>, on-click : msg, style : button-style = text-style(),
                                 ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc,theme> widget<msg>
  button( child, on-click, paint = styled-paint(style) )
