/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Style-agnostic building blocks shared by every style library (default,
// material, ...). The RAW `button` owns interaction (via `ui/state/interactive`)
// but no look -- it takes a `paint` FUNCTION `(child, interaction) -> widget`.
// A style library passes its own paint, so it can draw anything (fill, tonal,
// outline, elevation) and vary it by interaction state.
//
// Cost, measured honestly (checked the generated C, incl. -O2): `styled-paint(
// style)` is a real heap closure capturing `style`, and `paint` is called
// indirectly -- it is NOT specialized away (specialization needs a statically
// known function; a runtime closure that captures data cannot be eliminated,
// and `^`-borrowing only changes refcounting, not the allocation). But this is
// cheap and mostly unavoidable: `interactive` already needs a builder closure
// per button, so the marginal cost of the paint indirection is ~one small
// alloc per button per render. If that ever matters, make the fast path take a
// `button-style` VALUE directly (no function) and keep `paint` for the general
// case. `button-style` + `styled-paint` are that convenient filled-box paint,
// which most design languages can derive a value of and reuse.
module ui/style/base

import std/num/float64
import ui/widget
import ui/state
import ui/keytrie   // root-key for scaffolding widgets built outside a keytree scope

// a paint is a function `(child, interaction) -> widget` -- given the child
// content and the live interaction state, produce the visual. It is passed to
// `button` and called indirectly (a small closure per button; see the module
// note -- it is not specialized away).

// the default paint: a plain padded box (no color) -- a raw button
pub fun paint-plain<msg>( child : widget<msg>, s : interaction ) : widget<msg>
  box(child, padding = 9.0, ?key = root-key)

// a filled-button visual contract most design languages can express. A style
// library derives one from its palette and passes `styled-paint(style)`.
pub struct button-style
  bg      : color
  fg      : color
  hover   : color                    // container color while hovered
  pressed : color                    // container color while pressed
  radius  : float64 = 20.0           // fully-rounded by default (Material 3)
  padding : float64 = 12.0

// a paint that renders a `button-style`, picking the container color by state.
// The INTERACTION dimensions animate as scalars (hover glides in/out; press is
// fast) and the LIVE style colors are mixed by them each build -- so a theme
// crossfade flows through instantly (animating the final color instead would
// re-ease toward every intermediate theme color and trail the theme by a whole
// extra ease). Cells key by this paint's creation site (the button's call
// site, since `styled-paint(style)` is a default argument evaluated there).
pub fun styled-paint<msg>( style : button-style, ?key : key, ?kk-file-line : string ) : ( (widget<msg>, interaction) -> <keytree,uistate,ioc> widget<msg> )
  fn( child, s )
    val hover-t   = animate(if s.hovered && !s.pressed then 1.0 else 0.0,
                            duration = 110.0, ?key = scope("hov"), ?kk-file-line = ?kk-file-line)
    val pressed-t = animate(if s.pressed then 1.0 else 0.0,
                            duration = 60.0, ?key = scope("prs"), ?kk-file-line = ?kk-file-line)
    val base = if s.disabled then style.bg.brighten(0.6) else style.bg
    val bg = base.mix(style.hover, hover-t).mix(style.pressed, pressed-t)
    // the splash is the style's OWN foreground -- Material's state layer is the
    // "on-container" colour at low opacity, so a light label on a dark button
    // ripples light and a dark label on a light button ripples dark. A fixed
    // white splash reads as a flash on pale surfaces and vanishes on white ones.
    ripple( box(child, padding = style.padding, bg = Just(Fill(bg, style.radius))),
            s.pressed, radius = style.radius, tint = style.fg,
            ?key = scope("rip"), ?kk-file-line = ?kk-file-line )

// ----------------------------------------------------------------
// the ink ripple (task #60): a circle that grows from the TOUCH POINT and
// fades when the press ends, cut to the surface it sits on.
//
// Every piece of this is 2D paint the framework already had -- an animated
// circle, a clip, and a layout-neutral overlay -- which is why it works
// identically on the DOM and Impeller backends with no shader and no new
// backend surface. Flutter ships the same effect on web without its 3D stack
// for the same reason: a ripple is a painting problem.
//
// Two details that are not obvious:
//
//   - The splash layer is an `overlay`: it reports NO size, so however large
//     the circle grows it never resizes the button, and it is transparent to
//     input so it cannot swallow the click that started it. `fixed(_, 0, 0)`
//     looks like it would do, and does not -- it CAPS the child's layout, so
//     the splash came out zero-wide and invisible.
//   - `alpha` leads and `radius` follows: on release the alpha fades over
//     ~320ms while the circle keeps its size, then -- once it is invisible --
//     the radius snaps back to 0 with a zero-length animation. That reset is
//     what makes the NEXT press start from its own touch point instead of
//     continuing from wherever the last one ended, and it is invisible
//     precisely because it only happens at alpha 0.
//
// `max-radius` is deliberately generous rather than derived from the widget's
// size (which a builder does not know): the clip cuts the excess, so being too
// large costs nothing and being exact buys nothing.
pub fun ripple<msg>( content : widget<msg>, pressed : bool, radius : float64 = 6.0,
                     tint : color = rgb(1.0, 1.0, 1.0), strength : float64 = 0.12,
                     max-radius : float64 = 220.0,
                     ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc> widget<msg>
  // read the press POINT only here, where the press STATE is read too: the
  // point is an untracked ref and rides on the press write's invalidation
  // (see ui/state's `press-point`)
  val (px, py, pt) = press-point()
  val a01 = animate(if pressed then 1.0 else 0.0,
                    duration = if pressed then 80.0 else 320.0,
                    ?key = ?key, ?kk-file-line = ?kk-file-line ++ ":ripple-a")
  // The radius is DERIVED from the press timestamp, not eased by a cell.
  //
  // An animated cell has to be walked back to 0 between presses, and the only
  // safe moment to do it is after the fade finishes -- by which time the frame
  // loop has settled and may never rebuild to notice. That is the bug this
  // replaces: the second press started at full size and changed only alpha,
  // which reads as nothing happening at all. Deriving the radius means there
  // is no reset to schedule and none to animate; a new press stamps a new
  // time and the radius is 0 again by construction.
  val grow-ms = 420.0
  val r01 = ((anim-time() - pt) / grow-ms).min(1.0).max(0.0)
  // a derived value gets no frames from `animate`, so ask for them here --
  // and NOT gated on alpha: alpha is 0 on the first build after a press, so
  // gating on it stops the frames that would make alpha rise in the first place
  if r01 < 1.0 then request-frame()
  // NOT named `r`: a local `r` would shadow `color`'s own `.r` field, since
  // `tint.r` desugars to `r(tint)`
  val rad = r01 * max-radius
  val splash = if a01 <= 0.01 || rad <= 0.5 then [] else
    [ (px - rad, py - rad,
       overlay( rect(rad * 2.0, rad * 2.0,
                     bg = Just(Fill(Color(tint.r, tint.g, tint.b, strength * a01), rad)),
                     ?key = scope("splash")),
                ?key = scope("splash-box") )) ]
  clip( stack([ (0.0, 0.0, content) ] ++ splash, ?key = scope("ripple-stack")),
        radius = radius, ?key = scope("ripple-clip") )

// the RAW button: interaction + a paint function (default = a plain box).
// `disabled` blocks the click; `hit-slop` widens the hit area.
pub fun button<msg>( child : widget<msg>, on-click : msg, paint : (widget<msg>, interaction) -> <keytree,uistate,ioc> widget<msg> = paint-plain,
                     disabled : bool = False, hit-slop : float64 = 0.0,
                     ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc> widget<msg>
  interactive(on-click, disabled = disabled, hit-slop = hit-slop) fn(s) paint(child, s)
