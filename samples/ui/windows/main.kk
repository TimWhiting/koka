// Native multi-window: a torn-off inspector (`window(...)`, its own real OS
// window on native) that shares live model state with the main window --
// bumping the counter in EITHER window updates both, because both are just
// views over the one model, dispatching the one `msg` type. A `Panel` tip
// escapes the main window's bounds, anchored to a scoped identity in it (drag
// the main window and the tip follows). InLayer chrome (the default) still
// just composites in-window on jsweb/wasi-web, where there is no real OS window.
module main

import std/num/float64
import ui/widget
import ui/anchor
import ui/view
import ui/style/default
import ui/app

struct model( count : int = 0, show-inspector : bool = False, show-tip : bool = False )

type msg
  Bump
  ToggleInspector
  CloseInspector
  ToggleTip

// the inspector's content: the live count (proves cross-window messaging --
// this window has no state of its own) plus its own bump button and close
// button (the close button also fires via the native titlebar, wired below)
fun inspector-body( m : model, key : key ) : <keytree,uistate,ioc,theme> widget<msg>
  card( column([
    accented("Inspector", 16.0),
    body("count: " ++ m.count.show, ?key = scope("insp-count")),
    row([ primary-button("Bump", Bump, ?key = scope("insp-bump")),
          simple/quiet-button("Close", CloseInspector, ?key = scope("insp-close")) ]),
  ], gap = 10.0) )

// the tooltip panel's content: small, borderless, escapes the main window
fun tip-body( key : key ) : <keytree,uistate,ioc,theme> widget<msg>
  box( body("A Panel view: anchored to the scoped identity below, following the\nmain window, escaping its bounds."),
       padding = 10.0, bg = Just(Fill(theme.palette/surface, 6.0)) )

fun themed-view( m : model, key : key ) : <keytree,uistate,scene<msg>,ioc,theme> widget<msg>
  // the torn-off inspector: a real titled OS window on native, an in-window
  // layer on the web backends. Declarative lifecycle -- open while
  // `show-inspector` is True; the close button dispatches `on-dismiss`.
  if m.show-inspector then
    window("inspector", inspector-body(m, key), title = "Inspector",
           width = 260.0, height = 160.0, on-dismiss = Just(CloseInspector))
  // a Panel tooltip anchored to the "tip-anchor" scoped identity below, shown
  // while the toggle is on (a click toggle is more reliable to demo/test than
  // hover)
  if m.show-tip then
    overlay("tip", tip-body(key), chrome = Panel, target = Scope("tip-anchor"),
            target-align = bottom-left, offset-y = 6.0)
  page("Koka × windows", [
    body("A second, real OS window (torn off via `window(...)`) shares the one\nmodel: bump it from either window."),
    card( column([
      accented("count: " ++ m.count.show, 18.0),
      row([
        primary-button("Bump", Bump, ?key = scope("bump")),
        primary-button(if m.show-inspector then "Close inspector" else "Open inspector",
                        ToggleInspector, ?key = scope("toggle-inspector")),
      ]),
      row([
        body("hover target ->", ?key = scope("tip-anchor")),
        simple/quiet-button(if m.show-tip then "Hide tip" else "Show tip", ToggleTip, ?key = scope("toggle-tip")),
      ]),
    ], gap = 14.0) ),
  ])

fun view( m : model, key : key ) : <keytree,uistate,scene<msg>,ioc> widget<msg>
  with val theme = dark
  themed-view(m, key)

fun update( m : model, msg : msg ) : model
  match msg
    Bump             -> m(count = m.count + 1)
    ToggleInspector  -> m(show-inspector = !m.show-inspector)
    CloseInspector   -> m(show-inspector = False)
    ToggleTip        -> m(show-tip = !m.show-tip)

pub fun main()
  app( Model(), view, update, App-config("Koka × windows", 480, 360) )
