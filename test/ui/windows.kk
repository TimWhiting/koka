// Scene split: window()/Panel views leave the main composite; InLayer stays in.
module windows

import std/async
import std/num/float64
import ui/widget
import ui/state
import ui/view
import ui/style/default
import ui/test

pub struct model( show-inspector : bool = False )
pub type msg
  ToggleInspector
  CloseInspector

// a counter with private ephemeral state: a click bumps it (mirrors
// test/ui/retain.kk's `pane`) -- `label` is the displayed text; the caller's
// `scope(...)` (passed in as `key`) decides KeepAlive vs Transient AND is the
// addressing ancestor (val/bump are its NAMED children: `"insp val"` /
// `"insp bump"`, no keyed wrapper, no per-counter string)
fun ctr( name : string, label : string, key : key ) : <keytree,uistate,ioc,theme> widget<msg>
  val (n, set-n) = use-state(0)
  column([
    text(label ++ "=" ++ n.show, 13.0, theme.fg, ?key = scope("val", ?key = key)),
    act(box(text("bump " ++ name, 13.0, theme.fg), padding = 6.0), fn() set-n(fn(x) x + 1),
        ?key = scope("bump", ?key = key)),
  ], gap = 4.0)

pub fun themed-view( m : model, key : key ) : <keytree,uistate,scene<msg>,ioc,theme> widget<msg>
  // the counters sit behind ONE memo boundary that is called every render,
  // whether or not the window is open (mirrors retain.kk's `memo(panes)`,
  // which picks the active tab): when show-inspector flips to False the
  // build simply claims nothing this pass, so the boundary's kt-close sees
  // the counters' identities as unclaimed/stale -- unmount by consumption.
  // (`window(...)` itself is called directly, OUTSIDE the memo boundary --
  // portals inside a memo boundary now replay on a cache hit (fixes #45,
  // see `ui/view/with-scene`), so this restriction is LIFTED -- but the shape
  // is kept as-is here for test stability (the split/retention scenarios
  // below depend on it).
  fun counters( key : key ) : <keytree,uistate,ioc,theme> widget<msg>
    if m.show-inspector then
      column([
        ctr("keep", "K", scope("insp", keep = KeepAlive)),
        ctr("scratch", "S", scope("scratch")),                      // Transient
      ], gap = 8.0)
    else column([])
  val body = ui/state/memo(counters)
  // -- regression coverage for #45: a portal emitted INSIDE a memo boundary
  // whose deps never change must still be there after the boundary HITS on a
  // later frame (an unrelated uistate change, not a model message so no
  // forced full-rebuild storm). `tip-memo` reads no uistate itself, so once
  // built it hits on every subsequent non-storm frame.
  fun tip-memo( key : key ) : <keytree,uistate,scene<msg>,ioc,theme> widget<msg>
    overlay("m-tip", text("tip content", 13.0, theme.fg, ?key = scope("m-tip", ?key = key)))
    column([])
  val _ = ui/state/memo(tip-memo)
  // nested case: an overlay inside an INNER memo boundary, itself inside an
  // OUTER one. When the outer hits, it never calls the inner's `memo(...)` at
  // all -- the inner's recorded views must still replay (transitive expansion
  // over the parent chain; see `ui/reactive`).
  fun outer-memo( key : key ) : <keytree,uistate,scene<msg>,ioc,theme> widget<msg>
    fun inner-memo( key2 : key ) : <keytree,uistate,scene<msg>,ioc,theme> widget<msg>
      overlay("m-tip-nested", text("nested tip", 13.0, theme.fg, ?key = scope("m-tip-nested", ?key = key2)))
      column([])
    val _ = ui/state/memo(inner-memo)
    column([])
  val _ = ui/state/memo(outer-memo)
  if m.show-inspector then
    window("inspector", column([
             text("inspector body", 13.0, theme.fg, ?key = scope("insp-body")),
             body,
             act-msg(box(text("close", 13.0, theme.fg), padding = 6.0), fn() CloseInspector,
                     ?key = scope("close-insp")),
           ], gap = 8.0),
           title = "Inspector", on-dismiss = Just(CloseInspector))
  overlay("hint", text("layer hint", 13.0, theme.fg, ?key = scope("hint")))   // InLayer: stays composited
  overlay("bigov", rect(4000.0, 30.0, ?key = scope("big")))    // oversized overlay for testing clamping
  column([
    primary-button("Inspect", ToggleInspector, ?key = scope("toggle")),
    text("main body", 13.0, theme.fg, ?key = scope("main-body")),
  ], gap = 8.0)

pub fun view( m : model, key : key ) : <keytree,uistate,scene<msg>,ioc> widget<msg>
  with val theme = dark
  box( themed-view(m, key), padding = 12.0 )

pub fun update( m : model, msg : msg ) : dispatch<msg> model
  match msg
    ToggleInspector -> m(show-inspector = True)
    CloseInspector  -> m(show-inspector = False)

pub fun split-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  check-eq("no window content before toggle", t.texts("insp-body"), [])
  check-eq("layer content composites", t.texts("hint").length, 1)
  t.click("toggle")
  t.settle()
  check-eq("window content reachable after toggle", t.texts("insp-body"), ["inspector body"])
  check-eq("main still reachable", t.texts("main-body"), ["main body"])

pub fun oversize-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  match t.find("big")
    Just((x, y, _, _)) ->
      check("oversize pins to origin (x)", x == 0.0)
      check("oversize pins below top (y)", y >= 0.0)
    Nothing ->
      throw("oversize-scenario: big rect not found")

pub fun retention-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  t.click("toggle")
  t.settle()
  check-eq("keep starts fresh", t.texts("insp val"), ["K=0"])
  check-eq("scratch starts fresh", t.texts("scratch val"), ["S=0"])
  t.click("insp bump")
  t.click("scratch bump")
  t.settle()
  check-eq("keep bumped", t.texts("insp val"), ["K=1"])
  check-eq("scratch bumped", t.texts("scratch val"), ["S=1"])
  t.click("close-insp")
  t.settle()
  check-eq("window content unreachable while closed", t.texts("insp val"), [])
  t.click("toggle")
  t.settle()
  check-eq("keep retained across close/reopen (KeepAlive)", t.texts("insp val"), ["K=1"])
  check-eq("scratch reset across close/reopen (Transient)", t.texts("scratch val"), ["S=0"])

// regression for #45: portals emitted inside a memo boundary must replay when
// the boundary HITS (cache reuse), not vanish -- covers a plain memo boundary
// and a nested inner-boundary-inside-outer-boundary hit
pub fun memo-portal-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  check-eq("tip present after initial settle", t.texts("m-tip"), ["tip content"])
  check-eq("nested tip present after initial settle", t.texts("m-tip-nested"), ["nested tip"])
  // an UNRELATED uistate change (hover), not a model message -- so this does
  // NOT force a full-rebuild storm; the tip boundaries (which read nothing)
  // hit on this frame
  t.hover("toggle")
  t.settle()
  t.settle()
  check-eq("tip still present after unrelated hover (memo hit)", t.texts("m-tip"), ["tip content"])
  check-eq("nested tip still present after unrelated hover (outer memo hit)", t.texts("m-tip-nested"), ["nested tip"])

pub fun main()
  test-scenarios("native windows (headless)", Model(), view, update,
                 [("split", split-scenario), ("oversize", oversize-scenario),
                  ("retention", retention-scenario), ("memo-portal", memo-portal-scenario)])
