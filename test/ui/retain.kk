// State retention across unmount (the keep-alive design): three tabs behind
// ONE memo boundary; switching tabs unmounts the hidden pane. A pane minted
// with `keep = KeepAlive` keeps its ephemeral state (a use-state counter)
// until the same path remounts; a Transient pane's state dies with it.
module retain

import std/async
import std/num/float64
import ui/widget
import ui/state
import ui/style/default
import ui/test

pub struct model( tab : int = 0 )

pub type msg
  GoTab( t : int )

// a pane with private ephemeral state: a counter bumped by a click. The
// caller already mints `key` as `scope("pane-a"|"pane-b"|"pane-c", ...)` (the
// retention identity below) -- val/bump are just NAMED children of it (no
// keyed wrapper, no per-pane string): `"pane-a val"` / `"pane-a bump"`.
fun pane( label : string, key : key ) : <keytree,uistate,ioc,theme> widget<msg>
  val (n, set-n) = use-state(0)
  column([
    text(label ++ "=" ++ n.show, 13.0, theme.fg, ?key = scope("val", ?key = key)),
    act(box(text("bump " ++ label, 13.0, theme.fg), padding = 6.0), fn() set-n(fn(x) x + 1),
        ?key = scope("bump", ?key = key)),
  ], gap = 4.0)

fun themed-view( m : model, key : key ) : <keytree,uistate,scene<msg>,ioc,theme> widget<msg>
  // the ACTIVE pane behind a memo boundary: a tab switch is a model message
  // (dirty storm), the boundary re-runs, and the now-unclaimed pane unmounts
  // -- KeepAlive panes retire to the boundary's retained store, Transient
  // panes prune (cells dropped from the state store)
  fun panes( key : key ) : <keytree,uistate,ioc,theme> widget<msg>
    if m.tab == 0 then pane("A", scope("pane-a", keep = KeepAlive))
    elif m.tab == 1 then pane("B", scope("pane-b"))            // Transient
    else pane("C", scope("pane-c", keep = KeepAlive))
  column([
    row([ primary-button("TabA", GoTab(0), ?key = scope("tab-a")),
          primary-button("TabB", GoTab(1), ?key = scope("tab-b")),
          primary-button("TabC", GoTab(2), ?key = scope("tab-c")) ], gap = 6.0),
    memo(panes),
  ], gap = 8.0)

pub fun view( m : model, key : key ) : <keytree,uistate,scene<msg>,ioc> widget<msg>
  with val theme = dark
  box( themed-view(m, key), padding = 12.0 )

pub fun update( m : model, msg : msg ) : dispatch<msg> model
  match msg
    GoTab(t) -> m(tab = t)

pub fun retain-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  check-eq("A starts fresh", t.texts("pane-a val"), ["A=0"])
  t.click("pane-a bump")
  t.click("pane-a bump")
  t.settle()
  check-eq("A bumps", t.texts("pane-a val"), ["A=2"])
  t.click("tab-b")
  t.settle()
  check-eq("B starts fresh", t.texts("pane-b val"), ["B=0"])
  t.click("pane-b bump")
  t.settle()
  check-eq("B bumps", t.texts("pane-b val"), ["B=1"])
  t.click("tab-a")
  t.settle()
  check-eq("A retained across unmount (KeepAlive)", t.texts("pane-a val"), ["A=2"])
  t.click("tab-b")
  t.settle()
  check-eq("B reset across unmount (Transient)", t.texts("pane-b val"), ["B=0"])
  t.click("tab-c")
  t.settle()
  t.click("pane-c bump")
  t.settle()
  check-eq("C bumps", t.texts("pane-c val"), ["C=1"])
  t.click("tab-a")
  t.settle()
  check-eq("A still retained after a third tab", t.texts("pane-a val"), ["A=2"])
  t.click("tab-c")
  t.settle()
  check-eq("C retained too (two KeepAlive panes)", t.texts("pane-c val"), ["C=1"])
  // presence filter: pane-c is MOUNTED, pane-a is KeepAlive-RETAINED (unmounted)
  // -- both keep a `val` child in the keytrie id->path table, so a bare "val"
  // selector matches BOTH ids. It must resolve to the mounted pane (the
  // retained ghost has no node this frame), NOT throw ambiguous.
  check-eq("bare 'val' ignores the retained-pane ghost", t.texts("val"), ["C=1"])

pub fun main()
  test-scenarios("state retention", Model(), view, update,
                 [("retain", retain-scenario)])
