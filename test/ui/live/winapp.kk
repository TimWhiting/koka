// Ad-hoc multi-window smoke (NOT suite-wired): an app whose view emits a real
// second window unconditionally, plus a main-window counter driven by a tick
// subscription. Run natively with KOKA_IMP_FRAMES=n: TWO real OS windows appear
// (the main window + "Second"), the tick forces re-renders so the secondary
// window reconciles+presents once it comes alive, and the frame cap auto-closes
// the process (exit 0). Exercises ui/api/impeller/backend's window diff,
// per-window reconcile/present, and input routing end to end.
module winapp

import std/async
import std/time/duration
import std/core/debug   // trace: stderr, unbuffered (frame-cap _Exit drops buffered stdout)
import ui/widget
import ui/view      // window(): a Titled secondary window as a scene view
import ui/style/default
import ui/app
import ui/backend                     // test-window-id: the second window's table slot
import ui/api/impeller/impeller       // present-count: frames PRESENTED to that window

struct model( n : int )
type msg
  Tick

fun themed-view( m : model, key : key ) : <keytree,uistate,scene<msg>,ioc,theme> widget<msg>
  // emitted OUTSIDE any memo boundary so it re-emits every render (the window
  // stays open); its content shows the shared counter so re-renders are visible
  window("second", box( column([
           text("Second window", 16.0, theme.fg, ?key = scope("w-title")),
           text("n=" ++ m.n.show, 14.0, theme.fg, ?key = scope("w-body")),
         ], gap = 8.0), padding = 16.0, bg = Just(Fill(theme.bg)) ),
         title = "Second")
  box( column([
         text("Main window", 16.0, theme.fg, ?key = scope("main-title")),
         text("n=" ++ m.n.show, 14.0, theme.fg, ?key = scope("main-body")),
       ], gap = 8.0), padding = 16.0, bg = Just(Fill(theme.bg)) )

fun view( m : model, key : key ) : <keytree,uistate,scene<msg>,ioc> widget<msg>
  with val theme = dark
  themed-view(m, key)

fun update( m : model, msg : msg ) : dispatch<msg> model
  match msg
    Tick -> m(n = m.n + 1)

// after the window has had ~1s to open and render: assert frames were
// actually PRESENTED to it (a live-but-blank window reads 0 -- this is the
// regression probe for the per-window pending-dl publish path: a single
// shared slot once routed every secondary frame into window 0)
fun probe-presents() : <async,ioc> ()
  wait(1200.milli-seconds)
  val w = test-window-id("second")
  val n = if w >= 0 then present-count(w) else -1
  trace("winapp: second-window presents=" ++ n.show ++ (if n > 0 then " ok" else " FAIL"))

pub fun main()
  app( Model(0), view, update, App-config("WinApp Main", 360, 240),
       subs = [fn(ch) every(ch, 100.milli-seconds, Tick),
               fn(_ch) probe-presents()] )
