// Builder lists: `ui/lazy`'s `lazy-column` -- a windowed/virtualized list,
// the Flutter `ListView.builder` equivalent. Only the visible window (+/- a
// cache margin) is ever built/laid-out/stateful, no matter how big `count`
// is; scrolled-out rows unmount through the SAME key-retention machinery
// `ui/keytrie` already uses for tabs (see docs/ui/design-notes.md §13).
//
// The demo IS the comparison: two 100k-row lists side by side, identical
// except for their `keep` policy -- KeepAlive vs Transient -- so scrolling
// one row out and back shows the difference directly. A third, infinite
// list (no `count`) scrolls forever, growing its content one page ahead of
// the offset as you go.
module main

import ui/widget
import ui/view      // scene<msg> effect used in view/pane signatures
import ui/style/default
import ui/lazy
import ui/app

struct model()
type msg { Nop }

val total-rows = 100000

// one row: an index label plus a private bump counter, mirroring
// test/ui/lazy.kk's `item-row` (two sibling keyed leaves so each row's
// pieces stay independently addressable).
fun item-row( tag : string, i : int, key : key ) : <keytree,uistate,ioc,theme> widget<msg>
  val (n, set-n) = use-state(0)
  box( row([
    expanded( body(tag ++ " row " ++ i.show ++ "  (bumps: " ++ n.show ++ ")") ),
    act( box(body("bump"), padding = 4.0), fn() set-n(fn(x) x + 1) ),
  ], gap = 8.0),
    padding = 6.0,
    bg = Just(Fill(if i.is-even then theme.palette/surface else theme.palette/surface.brighten(1.06), 4.0)) )

// `lazy-column`'s `item` callback is closed at `<keytree,uistate,ioc>` (no
// ambient `theme`), so items discharge it themselves -- see the same note
// in test/ui/lazy.kk.
fun themed-item( tag : string, i : int, key : key ) : <keytree,uistate,ioc> widget<msg>
  with val theme = dark
  item-row(tag, i, key)

fun bounded-pane( tag : string, keep : keep, headline : string, key : key )
    : <keytree,uistate,scene<msg>,ioc,theme> widget<msg>
  column([
    body(headline, size = 16.0),
    expanded( lazy-column( fn(i, k) themed-item(tag, i, k), count = Just(total-rows),
                           keep = keep, name = tag, ?key = scope(tag) ) ),
  ], gap = 8.0, fill = True)

fun infinite-pane( key : key ) : <keytree,uistate,scene<msg>,ioc,theme> widget<msg>
  column([
    body("infinite (no count -- scroll forever)", size = 16.0),
    expanded( lazy-column( fn(i, k) themed-item("inf", i, k), count = Nothing,
                           name = "inf", ?key = scope("inf") ) ),
  ], gap = 8.0, fill = True)

fun themed-view( m : model, key : key ) : <keytree,uistate,scene<msg>,ioc,theme> widget<msg>
  page("Koka × lazy lists", [
    body("100,000 rows each, but only the visible window (+cache) is ever built -- " ++
         "scroll and watch the window stay small. The two panes below are IDENTICAL " ++
         "except for `keep`: scroll a row out and back to see the difference."),
    expanded( row([
      expanded( card( bounded-pane("kl", KeepAlive, "keep = KeepAlive -- counters survive scroll-out", key) ) ),
      expanded( card( bounded-pane("tl", Transient, "keep = Transient (default) -- counters reset on scroll-out", key) ) ),
    ], gap = 12.0, fill = True) ),
    expanded( card( infinite-pane(key) ), flex = 0.7 ),
  ])

fun view( m : model, key : key ) : <keytree,uistate,scene<msg>,ioc> widget<msg>
  with val theme = dark
  themed-view(m, key)

fun update( m : model, msg : msg ) : model
  m

// the auto scrollbar is composed outside the view's `theme` scope (it runs
// at scene-composition time), so it discharges its own theme -- same idiom
// as samples/ui/scroll.
fun auto-bar( info, axis ) : ioc widget<msg>
  with val theme = dark
  themed-scrollbar(info, axis)

pub fun main()
  app( Model(), view, update, App-config("Koka × lazy lists", 900, 640), scrollbar = auto-bar )
