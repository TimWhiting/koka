// Task 1 review Critical #1's repro, as its own standalone app (deliberately
// NOT folded into test/ui/lazy.kk's shared tl/kl/inf app): squeezing a 4th
// concurrent `lazy-column` into that app trips a click-dispatch bug that
// reproduces with ANY 4th sibling lazy-column -- trivial content included --
// and is unrelated to this fix (recorded separately, see task-1-report.md
// and the tracked backlog item); isolating this repro sidesteps it and keeps
// both files' failure signal clean.
//
// The repro itself: 20 rows at item-extent 40, row 3 deliberately measures
// 120 tall (a bare `rect`, so its height is exact, not font-metric-dependent).
// Before the `fixed`-based fix (the old `stack([rect(0,extent), item])`
// trick, which `Stack` sizes to the MAX of its children, not the background
// rect) this desynced the whole list: content published 880 instead of the
// exact 800, and every row after the oversize one shifted down by the
// overflow. `fixed` (ui/widget) REPORTS exactly `item-extent` to the column
// no matter what a row measures, so the window's geometry is exact by
// construction; see task-1-report.md for the failing-first run against the
// old `stack` trick.
module lazy-oversize

import std/async
import std/num/float64
import ui/widget
import ui/state
import ui/lazy
import ui/test

pub struct model()
pub type msg
  Nop

val extent : float64 = 40.0
val cache  : int = 4
val ov-rows : int = 20
val ov-oversize-index : int = 3
val ov-oversize-height : float64 = 120.0

// row `ov-oversize-index` measures TALLER than `item-extent` on purpose;
// every other row is a normal short text row. `fixed` must keep the window's
// reported geometry exact regardless. Addressed by `idx(i)` (the row's OWN
// `key`, minted by `lazy-column` -- no per-row string): each leaf's owner IS
// that identity directly (no keyed wrapper needed), selectable as
// `"ov-rows :i"` (the outer `scope("ov-rows")` in `view` below disambiguates
// from any other list sharing the same index space -- moot here with only
// one list, kept for the idiom).
fun ov-item( i : int, key : key ) : <keytree,uistate,ioc> widget<msg>
  if i == ov-oversize-index
    then rect(200.0, ov-oversize-height, ?key = key)
    else text("ov row " ++ i.show, 13.0, default-fg, ?key = key)

pub fun view( m : model, key : key ) : <keytree,uistate,scene<msg>,ioc> widget<msg>
  expanded( lazy-column( ov-item, count = Just(ov-rows),
                         item-extent = extent, cache = cache, keep = Transient, name = "ov",
                         ?key = scope("ov-rows") ) )

pub fun update( m : model, msg : msg ) : dispatch<msg> model
  m

pub fun oversize-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  t.settle()
  t.settle()
  val want = ov-rows.float64 * extent   // 20 * 40 = 800, exact -- not 880
  check("oversize row does not inflate content: reports exact count*extent",
        all-scroll-states().any(fn(kv) kv.snd.content == want),
        "want " ++ want.show)
  // rows straddle the oversize one (2 .. 4): the gap between row 2 and row 4
  // must be EXACTLY 2*item-extent -- regardless of what row 3 (between them)
  // actually measures -- because `fixed` pins every row's REPORTED extent,
  // not just the oversize row's. Comparing two mounted rows' positions (a
  // DELTA) sidesteps this app's own chrome (there is none here, but keeps
  // the assertion robust regardless).
  val y2 = t.find("ov-rows :2")
  val y4 = t.find("ov-rows :" ++ (ov-oversize-index + 1).show)
  match (y2, y4)
    (Just((_, ya, _, _)), Just((_, yb, _, _))) ->
      check("row after the oversize one sits exactly 2*item-extent below row 2",
            yb - ya == 2.0 * extent, "want delta=" ++ (2.0*extent).show ++ ", got " ++ (yb - ya).show)
    _ -> check("both straddling rows are mounted", False)

pub fun main()
  test-scenarios("lazy-column oversize row (headless)", Model(), view, update,
                 [("oversize", oversize-scenario)])
