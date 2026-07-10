// Shared ephemeral-state demo helpers used across the site's pages: each
// drives itself with `ui/state` (`use-state` + `act`), so a page can host an
// interactive widget WITHOUT threading an app message through the shell --
// the same mechanism a real component library uses for uncontrolled UI.
module pages/common

import std/num/float64
import ui/keytrie   // ?key implicits (text/link now key their leaves)
import ui/widget
import ui/state
import ui/style/default
import blocks

pub fun demo-button<a>( label : string, on : () -> <uistate,ioc> () , key : key) : <keytree,uistate,ioc,theme> widget<a>
  act( box(text(label, 16.0, on-accent), padding = 9.0, bg = Just(Fill(theme.accent, 6.0))), on )

// a self-contained counter: its count lives in ui/state, keyed by the CALL SITE
// (`?child-key` = the ambient path + this call's file+line), so every embed is
// independent with zero app wiring. Two on the same source line collide -- give
// those a distinct `?key` (e.g. one per source line, or `idx(i)` in a map).
pub fun live-counter<a>( key : key ) : <keytree,uistate,ioc,theme> widget<a>
  val (n, set) = use-state(0)
  box( row([
    demo-button("−", fn() set(fn(x) x - 1), here()),
    box(text(n.show, 26.0, theme.fg), padding = 6.0),
    demo-button("+", fn() set(fn(x) x + 1), here()),
  ], gap = 12.0), padding = 12.0, bg = Just(Fill(theme.surface, 12.0)) )

// a live "progress" demo driven by ephemeral state (a message-agnostic page
// can't host a message-emitting slider, so this uses buttons + a drawn bar)
pub fun live-progress<a>( key : key ) : <keytree,uistate,ioc,theme> widget<a>
  val (v, set) = use-state(40)
  // the bar EASES to its target: `animate` interpolates toward `v` over 350ms
  // (ease-out), requesting frames only while in flight -- release a button and
  // watch it glide; when it settles the app stops re-rendering entirely.
  val w = animate(240.0 * v.float64 / 100.0, duration = 350.0)
  box( column([
    row([ text("value: ", 15.0, theme.fg), accented(v.show ++ "%", 15.0) ]),
    stack([
      (0.0, 0.0, rect(240.0, 14.0, bg = Just(Fill(theme.bg, 7.0)))),
      (0.0, 0.0, rect(w, 14.0, bg = Just(Fill(theme.accent, 7.0)))),
    ]),
    row([
      demo-button("−10", fn() set(fn(x) (x - 10).max(0)), here()),
      demo-button("+10", fn() set(fn(x) (x + 10).min(100)), here()),
    ], gap = 12.0),
    prose("The value lives in ui/state; the bar `animate`s to it -- frames are "
          ++ "requested only while the animation is unsettled."),
  ], gap = 12.0), padding = 12.0, bg = Just(Fill(theme.surface, 12.0)) )
