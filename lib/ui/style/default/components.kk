/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// The DEFAULT style library's components. Two ideas run through it:
//
//  * Static overloading -- `simple/foo` takes a string label, `widget/foo`
//    takes any child widget; a call `foo(x)` resolves by the type of `x`. So
//    `primary-button("Save", Save)` and `primary-button(row([icon, label]),
//    Save)` are the same name.
//
//  * Hybrid token delivery -- LEAF components (`button`) take pure IMPLICIT
//    tokens (`?bg`/`?fg`, overridable per call, no effect in the row). LARGE /
//    convenience components (`primary-button`, `card`, `page`) read the ambient
//    `theme` effect and BRIDGE it to the leaves by binding the tokens as vals
//    in scope (`val bg = theme.accent; button(...)`). Deep signatures stay
//    clean (just `theme`); leaves stay overridable.
module ui/style/default/components

import std/num/float64
import ui/widget
import ui/state
import ui/keytrie   // root-key for the composer-built scrollbar scaffolding
import ui/style/base    // ripple (shared by every style's buttons)
import ui/style/default/theme

pub val on-accent : color = rgb(1.0, 1.0, 1.0)   // text on an accent fill

// ----------------------------------------------------------------
// button: the styled leaf. Tokens arrive as IMPLICITS -- resolved from a `val`
// in scope (the themed convenience buttons below bind them), or overridden at
// the call site: `button(text("Delete"), Del, ?bg = rgb(0.8,0.2,0.2))`.

pub fun widget/button<msg>( child : widget<msg>, on-click : msg, radius : float64 = 6.0,
                            ?bg : color, ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc> widget<msg>
  interactive(on-click) fn(s)
    // the brightness GLIDES between rest/hover/press (fast on the way in)
    val glow = animate(if s.interaction/pressed then 0.80 elif s.hovered then 1.25 else 1.0,
                       duration = 110.0, ?key = ?key, ?kk-file-line = ?kk-file-line)
    ripple( box( child, padding = 9.0, bg = Just(Fill(bg.brighten(glow), radius)) ),
            s.interaction/pressed, radius = radius, tint = bg.contrasting )

pub fun simple/button<msg>( label : string, on-click : msg, size : float64 = 15.0,
                            ?bg : color, ?fg : color, ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc> widget<msg>
  interactive(on-click) fn(s)
    val glow = animate(if s.interaction/pressed then 0.80 elif s.hovered then 1.25 else 1.0,
                       duration = 110.0, ?key = ?key, ?kk-file-line = ?kk-file-line)
    ripple( box( text(label, size, fg), padding = 9.0, bg = Just(Fill(bg.brighten(glow), 6.0)) ),
            s.interaction/pressed, radius = 6.0, tint = fg )

// ----------------------------------------------------------------
// themed convenience buttons: read the palette and bridge it to `button`.

// a filled, accent-colored button (primary actions)
pub fun simple/primary-button<msg>( label : string, on-click : msg, size : float64 = 15.0,
                                    ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc,theme> widget<msg>
  val bg = theme.accent
  val fg = on-accent
  simple/button( label, on-click, size = size )
pub fun widget/primary-button<msg>( child : widget<msg>, on-click : msg,
                                    ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc,theme> widget<msg>
  val bg = theme.accent
  widget/button( child, on-click )

// a quiet button on the surface color (secondary actions)
pub fun simple/quiet-button<msg>( label : string, on-click : msg, size : float64 = 15.0,
                                  ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc,theme> widget<msg>
  val bg = theme.palette/surface
  val fg = theme.fg
  simple/button( label, on-click, size = size )
pub fun widget/quiet-button<msg>( child : widget<msg>, on-click : msg,
                                  ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc,theme> widget<msg>
  val bg = theme.palette/surface
  widget/button( child, on-click )

// ----------------------------------------------------------------
// containers + text (read the palette directly -- large components)

// children on a raised, themed surface
pub fun card<msg>( child : widget<msg>, padding : float64 = 14.0, ?key : key ) : theme widget<msg>
  box( child, padding = padding, bg = Just(Fill(theme.palette/surface, 10.0)) )

// a page: a heading over its content, spaced as a filled column. `simple/page`
// takes a string title (rendered accented); `widget/page` takes any header.
pub fun widget/page<msg>( title : widget<msg>, children : list<widget<msg>>, gap : float64 = 14.0, scroll=True, ?key : key ) : <keytree,theme> widget<msg>
  if scroll then 
    widget/scroll(column(Cons(title, children), gap = gap, fill = True))
  else 
    column(Cons(title, children), gap = gap, fill = True)
pub fun simple/page<msg>( title : string, children : list<widget<msg>>, gap : float64 = 14.0, scroll=True, ?key : key ) : <keytree,theme> widget<msg>
  widget/page( accented(title, 20.0), children, gap = gap, scroll = scroll )

// body text in the theme's foreground -- prose that WRAPS to the available
// width (use `text`/`code` for single-line labels)
pub fun body<msg>( content : string, size : float64 = 15.0, ?key : key ) : theme widget<msg>
  paragraph(content, size, theme.fg)

// accented text
pub fun accented<msg>( content : string, size : float64 = 15.0, ?key : key ) : theme widget<msg>
  text(content, size, theme.accent)

// ----------------------------------------------------------------
// stateful components (ephemeral state via ui/state -- NOT app model)

// a collapsible section: clicking the header toggles `body` in/out. Its open
// state is `ui/state`, keyed by the REQUIRED `key` -- the caller mints one per
// instance: `expander("Files", tree, here())`, or `idx(i)` in a mapped list.
// Forgetting it is a type error; `key` is abstract so it cannot be forged.
pub fun expander<msg>( title : string, body : widget<msg>, key : key ) : <keytree,uistate,ioc,theme> widget<msg>
  val (open, set-open) = use-state(False)
  val marker = if open then "▼  " else "▶  "
  val header = act( text(marker ++ title, 15.0, theme.fg), fn() set-open(fn(o) !o) )
  if open then column([ header, box(body, padding = 8.0) ], gap = 8.0)
          else header

// ----------------------------------------------------------------
// menus + dropdowns (the styled content for `ui/overlay` popups). These are
// plain themed widgets -- the app floats them with `with-overlays` / `popup`,
// so nothing here knows about overlays; it is just a surface, rows, and a
// trigger button.

// one row of a menu: an `interactive` row that highlights on hover / press and
// dispatches `on` when clicked. Give a list of these distinct identities with
// `?key = idx(i)` (see `context-menu`).
pub fun menu-item<msg>( label : string, on : msg, ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc,theme> widget<msg>
  // hoist the theme reads (the `interactive` builder must be pure -- see `button`)
  val ac = theme.accent
  val fg = theme.fg
  interactive(on) fn(s)
    val bg = if s.interaction/pressed then Just(Fill(ac, 4.0))
             elif s.hovered then Just(Fill(Color(ac.r, ac.g, ac.b, 0.15), 4.0))
             else Nothing
    val col = if s.interaction/pressed then on-accent else fg
    // SELF-SIZING: sized to the label + padding (no `spacer`/`fill`, which would
    // greedily fill the overlay layer's full viewport width and height).
    box( text(label, 15.0, col), padding = 8.0, bg = bg )

// a context menu / dropdown list: a raised themed surface holding a column of
// `menu-item`s built from `(label, message)` pairs. Float it at a point with
// `ui/view`'s `overlay` (e.g. from an `on-click-at` anchor).
pub fun context-menu<msg>( items : list<(string, msg)>, ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc,theme> widget<msg>
  val rows = items.map-indexed fn(i, it)
    menu-item(it.fst, it.snd, ?key = idx(i))
  box( column(rows, gap = 2.0), padding = 4.0, bg = Just(Fill(theme.palette/surface, 8.0)) )

// a dropdown TRIGGER: a quiet button (labelled with a ▾ affordance) that emits
// `on-open`. Overlay open-state is app state, so the app responds to `on-open`
// by floating `context-menu(items)` with `overlay` -- `items` travels with the
// trigger so the call site reads as one dropdown, and a future self-hoisting
// dropdown could render them itself.
pub fun dropdown<msg>( label : string, items : list<(string, msg)>, on-open : msg,
                       ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc,theme> widget<msg>
  // `items` belongs to the app's overlay (see above); the trigger is just a button
  simple/quiet-button( label ++ "  ▾", on-open )

// a vertical scrollbar LINKED to a scroll region: pass the same `name` you gave
// `scroll`, and place it beside the scroll in a `row`. It subscribes to the
// region's live `scroll-state` (offset/content/viewport) and rebuilds when the
// offset or metrics change, drawing a track the height of the viewport with a
// thumb sized `viewport/content` and positioned by the offset. Its track height
// tracks the region's real viewport once known (the `height` argument is only
// the first-frame fallback, before the region has been laid out and measured).
// Reflects native scrolling; on the web the browser draws its own scrollbar.
// `scrollbar("list", 300.0)` links to `scroll(..., name="list")` in the same
// component (same ambient `?key`).
pub fun scrollbar<msg>( name : string, height : float64, width : float64 = 8.0, ?key : key ) : <keytree,uistate,ioc,theme> widget<msg>
  val region = scroll-key(name, ?key = ?key)
  register-manual-scrollbar(region)   // tell the scene composer NOT to auto-place a bar for this region
  val s = scroll-state(region)
  val track-h = if s.viewport > 0.0 then s.viewport else height   // match the region once measured
  val ratio   = if s.content > 0.0 then (s.viewport / s.content).min(1.0) else 1.0
  val thumb-h = (track-h * ratio).max(20.0).min(track-h)
  val max-off = (s.content - s.viewport).max(0.0)
  val pos     = if max-off > 0.0 then (s.offset / max-off).max(0.0).min(1.0) else 0.0
  val thumb-y = (track-h - thumb-h) * pos
  stack([
    (0.0, 0.0,     rect(width, track-h, bg = Just(Fill(theme.surface, width / 2.0)))),
    (0.0, thumb-y, rect(width, thumb-h, bg = Just(Fill(theme.accent,  width / 2.0)))),
  ])

// the AUTO scrollbar builder: pass to `app`'s `scrollbar=` (self-contained about
// its theme, since the scene composer runs outside the view's theme scope) and
// the composer places it over each overflowing region that has no manual bar. A
// themed track + thumb sized from the live scroll metrics; vertical bars are laid
// out width x viewport, horizontal viewport x width.
pub fun themed-scrollbar<a>( info : scroll-info, axis : scroll-axis, width : float64 = 8.0 ) : <ioc,theme> widget<a>
  val ratio   = if info.content > 0.0 then (info.viewport / info.content).min(1.0) else 1.0
  val max-off = (info.content - info.viewport).max(0.0)
  val pos     = if max-off > 0.0 then (info.offset / max-off).max(0.0).min(1.0) else 0.0
  val span    = (info.viewport * ratio).max(20.0).min(info.viewport)
  val at      = (info.viewport - span) * pos
  val track   = Just(Fill(theme.surface, width / 2.0))
  val thumb   = Just(Fill(theme.accent,  width / 2.0))
  match axis
    Vertical ->
      stack([ (0.0, 0.0, rect(width, info.viewport, bg = track, ?key = root-key)),
              (0.0, at,  rect(width, span,          bg = thumb, ?key = root-key)) ], ?key = root-key)
    Horizontal ->
      stack([ (0.0, 0.0, rect(info.viewport, width, bg = track, ?key = root-key)),
              (at,  0.0, rect(span,          width, bg = thumb, ?key = root-key)) ], ?key = root-key)
