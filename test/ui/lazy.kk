// Builder lists: `ui/lazy`'s `lazy-column` -- windowed materialization over the
// unified scroll model. FOUR lists share one model-free app (mirrors
// test/ui/retain.kk's shape: a `use-state` bump counter behind an `act`, no
// model messages needed): "tl" (Transient, bounded 10k), "kl" (KeepAlive,
// bounded 10k), "inf" (Transient, infinite), "d4" (Transient, bounded 10k).
//
// The oversize-row repro for Task 1 review's Critical #1 (an item taller
// than `item-extent` must not desync the window's geometry) lives in
// test/ui/lazy-oversize.kk as its OWN standalone app (one file can only drive
// one `test-scenarios` call -- `forking` cancels the continuation).
//
// The 4th list ("d4") is the task #50 regression: at four panes each column is
// narrow enough that a row's `[val, bump]` content overflows the pane's right
// edge, so the bump button is only PARTLY inside the scroll viewport. That used
// to lose the click -- `find`/`owner-rect` reported the button's full unclipped
// rect and `t.click` aimed at a center the scroll region clips away, so `hit`
// missed and the `use-state` write never fired. Fixed by clipping `owner-rect`
// to the scroll viewport (ui/widget) + baking scroll offsets in the harness
// (ui/test); the `narrow-click` scenario below asserts the bump now lands. See
// task-50-report.md.
module lazy

import std/async
import std/num/float64
import ui/widget
import ui/state
import ui/lazy
import ui/style/default
import ui/test

pub struct model()
pub type msg
  Nop

// the extent/cache lazy-column is configured with in every list below --
// tests reason about their own expectations relative to these same constants
val extent : float64 = 40.0
val cache  : int = 4
val total-rows = 10000

// an item row with private ephemeral state: a counter bumped by a click. TWO
// sibling leaves (mirrors test/ui/retain.kk's `pane`: val / bump), each
// minted as a NAMED child of the row's OWN identity `key` (`idx(i)`, minted
// by `lazy-column` -- no per-row string): `scope("val"|"bump", ?key = key)`
// are constant literals, so the only per-row cost is the index `lazy-column`
// already pays. Selector: `"<tag>-rows :i val"` / `"<tag>-rows :i bump"` --
// the row-index alone (`idx(i)`) is not enough to disambiguate the four
// sibling lists sharing the same index space, so `themed-view` wraps each
// `lazy-column` in its own `scope("<tag>-rows")` ancestor below.
fun item-row( tag : string, i : int, key : key ) : <keytree,uistate,ioc,theme> widget<msg>
  val (n, set-n) = use-state(0)
  row([
    text(tag ++ " row " ++ i.show ++ " n=" ++ n.show, 13.0, theme.fg, ?key = scope("val", ?key = key)),
    act(box(text("bump", 13.0, theme.fg), padding = 4.0), fn() set-n(fn(x) x + 1), ?key = scope("bump", ?key = key)),
  ], gap = 6.0)

// `item-row` needs `theme`, which `lazy-column`'s `item` callback signature
// does not carry (it is closed at `<keytree,uistate,ioc>` -- items must not
// leak arbitrary ambient effects out to every backend); discharge `theme`
// locally in the closure instead of threading it through the signature.
fun themed-item( tag : string, i : int, key : key ) : <keytree,uistate,ioc> widget<msg>
  with val theme = dark
  item-row(tag, i, key)

pub fun themed-view( m : model, key : key ) : <keytree,uistate,scene<msg>,ioc,theme> widget<msg>
  row([
    expanded( lazy-column( fn(i, k) themed-item("tl", i, k), count = Just(total-rows),
                           item-extent = extent, cache = cache, keep = Transient, name = "tl",
                           ?key = scope("tl-rows") ) ),
    expanded( lazy-column( fn(i, k) themed-item("kl", i, k), count = Just(total-rows),
                           item-extent = extent, cache = cache, keep = KeepAlive, name = "kl",
                           ?key = scope("kl-rows") ) ),
    expanded( lazy-column( fn(i, k) themed-item("inf", i, k), count = Nothing,
                           item-extent = extent, cache = cache, keep = Transient, name = "inf",
                           ?key = scope("inf-rows") ) ),
    // the 4th pane (task #50): narrows every column enough that a row's content
    // overflows its pane, so a bump button is only partly inside the viewport
    expanded( lazy-column( fn(i, k) themed-item("d4", i, k), count = Just(total-rows),
                           item-extent = extent, cache = cache, keep = Transient, name = "d4",
                           ?key = scope("d4-rows") ) ),
  ], gap = 8.0, fill = True)

pub fun view( m : model, key : key ) : <keytree,uistate,scene<msg>,ioc> widget<msg>
  with val theme = dark
  box( themed-view(m, key), padding = 12.0 )

pub fun update( m : model, msg : msg ) : dispatch<msg> model
  m

// row-k of `tag` is present iff its `val` label is mounted (a selector
// resolving via idx(i)'s owner, so `find` sees it directly)
fun row-present( t : tester<msg>, tag : string, i : int ) : <keytree,uistate,ioc,exn> bool
  t.find(tag ++ "-rows :" ++ i.show ++ " val").is-just

pub fun window-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  t.settle()   // let the first (viewport=0, fallback n=1+2*cache) render correct itself
  t.settle()
  check("row 0 materializes", t.row-present("tl", 0))
  check("row 60 does NOT materialize (well past any viewport/extent+2*cache)",
        !t.row-present("tl", 60))
  // whatever the window size n0 turns out to be (it depends on the harness's
  // window height, not hardcoded here), it is a CONTIGUOUS prefix [0, n0) and
  // it is small relative to the 10k list
  val present = list(0, 60).filter(fn(i) t.row-present("tl", i))
  val n0 = present.length
  check("materialized set is exactly [0, n0)",
        list(0, n0 - 1).all(fn(i) t.row-present("tl", i)) &&
        (n0 > 60 || !t.row-present("tl", n0)))
  check("window count is bounded (not the whole 10k list)", n0 < 150)

pub fun exact-height-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  t.settle()
  t.settle()
  // both bounded lists (tl, kl) publish an EXACT content extent of
  // count * item-extent -- probed via `all-scroll-states` since the region's
  // internal int key is not part of `ui/lazy`'s public surface
  val want = total-rows.float64 * extent
  check("a bounded region reports exact content height",
        all-scroll-states().any(fn(kv) kv.snd.content == want))
  check("at least two bounded regions (tl AND kl) report it",
        all-scroll-states().filter(fn(kv) kv.snd.content == want).length >= 2)

pub fun moved-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  t.settle()
  t.settle()
  check("row 0 present before scroll", t.row-present("tl", 0))
  t.scroll("tl", -20000.0)   // wheel semantics: dy<0 scrolls DOWN, revealing later rows
  t.settle()
  t.settle()
  check("row 0 gone after scrolling far down", !t.row-present("tl", 0))
  // the window followed the offset: SOME row well past the original window
  // materializes now (>~ (20000/extent - cache), comfortably >100 either way)
  val moved = list(100, 700).any(fn(i) t.row-present("tl", i))
  check("a later row materializes after the scroll", moved)

pub fun recycle-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  t.settle()
  t.settle()
  check-eq("tl row 2 starts fresh", t.texts("tl-rows :2 val"), ["tl row 2 n=0"])
  check-eq("kl row 2 starts fresh", t.texts("kl-rows :2 val"), ["kl row 2 n=0"])
  t.click("tl-rows :2 bump")
  t.click("kl-rows :2 bump")
  t.settle()
  check-eq("tl row 2 bumped", t.texts("tl-rows :2 val"), ["tl row 2 n=1"])
  check-eq("kl row 2 bumped", t.texts("kl-rows :2 val"), ["kl row 2 n=1"])
  // scroll far enough that index 2 unmounts on both lists, then back
  t.scroll("tl", -20000.0)
  t.scroll("kl", -20000.0)
  t.settle()
  t.settle()
  check("tl row 2 unmounted mid-scroll", !t.row-present("tl", 2))
  check("kl row 2 unmounted mid-scroll", !t.row-present("kl", 2))
  t.scroll("tl", 20000.0)
  t.scroll("kl", 20000.0)
  t.settle()
  t.settle()
  check-eq("tl row 2 reset across unmount (Transient)", t.texts("tl-rows :2 val"), ["tl row 2 n=0"])
  check-eq("kl row 2 retained across unmount (KeepAlive)", t.texts("kl-rows :2 val"), ["kl row 2 n=1"])

pub fun infinite-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  t.settle()
  t.settle()
  // each `t.scroll` only clamps to the CURRENT (pre-scroll) content -- the
  // same "one page ahead" limit an infinite list intentionally keeps -- so a
  // single wheel event can only advance one page; repeat it several times to
  // walk the offset well past the FIRST page's content, proving each round
  // published a bigger content than the last (an infinite list never settles
  // at a fixed total the way a bounded list's does)
  list(1, 6).foreach fn(_)
    t.scroll("inf", -20000.0)
    t.settle()
    t.settle()
  check("infinite content grows ahead of the offset",
        all-scroll-states().any(fn(kv) kv.snd.content > kv.snd.offset + kv.snd.viewport - 1.0))
  check("infinite region did scroll (offset advanced past the first page)",
        all-scroll-states().any(fn(kv) kv.snd.offset > 500.0))

// task #50 regression: with four narrow panes a row's bump button overflows its
// pane's right edge and is only PARTLY inside the scroll viewport. Clicking it
// must still fire the `use-state` write (previously the click's coordinates --
// the center of the button's full unclipped rect -- landed in the clipped-away
// region, `hit` missed, and the counter stayed 0). The button's laid-out rect
// here is genuinely wider than the visible sliver, so this only passes because
// `owner-rect` now reports the CLIPPED (hittable) rect.
pub fun narrow-click-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  t.settle()
  t.settle()
  check("tl-rows :2 bump is mounted", t.find("tl-rows :2 bump").is-just)
  check-eq("tl row 2 starts fresh", t.texts("tl-rows :2 val"), ["tl row 2 n=0"])
  t.click("tl-rows :2 bump")
  t.settle()
  t.settle()
  check-eq("tl row 2 bumped through a partly-clipped button", t.texts("tl-rows :2 val"), ["tl row 2 n=1"])
  // the same must hold on the 4th pane itself
  check-eq("d4 row 1 starts fresh", t.texts("d4-rows :1 val"), ["d4 row 1 n=0"])
  t.click("d4-rows :1 bump")
  t.settle()
  t.settle()
  check-eq("d4 row 1 bumped", t.texts("d4-rows :1 val"), ["d4 row 1 n=1"])

pub fun main()
  test-scenarios("lazy-column (headless)", Model(), view, update,
                 [("window", window-scenario),
                  ("exact-height", exact-height-scenario),
                  ("moved", moved-scenario),
                  ("recycle", recycle-scenario),
                  ("infinite", infinite-scenario),
                  ("narrow-click", narrow-click-scenario)])
