// REGRESSION TEST: a horizontal-scroll region as a RIGID sibling in a row
// must shrink to its own content width when wrapped in `intrinsic-width`,
// instead of claiming the row's full offered main-axis width.
//
// Found via the docs site's `demo-panel` (samples/ui/site/blocks.kk), which
// puts a `code-block` (a horizontal `scroll`) beside a live widget in a
// `row`: every demo-panel's live half rendered clipped past the page's
// right edge, because `Scroll`'s layout reports the FULL width a flex
// parent offers whenever that axis is bounded (correct for "fill available
// space", the common case) -- so a short code sample still claimed the
// row's entire width, pushing its sibling out past the viewport. The fix
// is at the call site (wrap the scroll in `intrinsic-width`, which probes
// the content's natural width first), not in `Scroll` itself, which is
// working as designed for its primary use (a page's own content scroll).
module intrinsic-scroll-row

import std/async
import std/num/float64
import ui/widget
import ui/keytrie
import ui/state
import ui/test

pub struct model()
pub type msg
  Nop

fun swatch( key : key ) : <keytree,uistate,ioc> widget<msg>
  rect(30.0, 20.0, bg = Just(Fill(rgb(0.2, 0.2, 0.3))), ?key = key)

// a short 30-wide swatch, much narrower than the 400-wide row it sits in.
// Two rows, side by side: `bare` reproduces the bug (no intrinsic-width --
// the horizontal scroll claims the row's full offered width, pushing
// "bare-sibling" out near the row's 400-wide allotment); `wrapped` is the
// fix (`intrinsic-width` around the same scroll). Wrapped in `expanded(
// scroll(...))` at the root, matching how `demo-panel` actually sits on the
// docs site (inside the page's own vertical scroll) -- WITHOUT an enclosing
// vertical scroll, the row's own cross-axis (height) constraint is the
// bounded window height rather than unbounded, which inflates the
// horizontal scroll's HEIGHT to fill it and centers siblings oddly; that
// artifact is specific to a bare root and doesn't occur in real usage.
pub fun view( m : model, key : key ) : <keytree,uistate,scene<msg>,ioc> widget<msg>
  expanded( scroll( column([
    fixed( row([
      scroll( swatch(scope("bare-code")), horizontal = True ),
      swatch(scope("bare-sibling")),
    ], gap = 10.0), width = Just(400.0) ),
    fixed( row([
      intrinsic-width( scroll( swatch(scope("wrapped-code")), horizontal = True ) ),
      swatch(scope("wrapped-sibling")),
    ], gap = 10.0), width = Just(400.0) ),
  ], gap = 20.0), name = "page" ) )

pub fun update( m : model, msg : msg ) : dispatch<msg> model
  m

fun x-of( t : tester<msg>, sel : string ) : <async,keytree,uistate,uicheck,ioc,exn> float64
  match t.find(sel)
    Just((x, _, _, _)) -> x
    Nothing -> -1.0

fun rect-of( t : tester<msg>, sel : string ) : <async,keytree,uistate,uicheck,ioc,exn> string
  match t.find(sel)
    Just((x, y, w, h)) -> "(" ++ x.show ++ "," ++ y.show ++ "," ++ w.show ++ "," ++ h.show ++ ")"
    Nothing -> "not-found"

pub fun scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  t.settle()
  // BUG (documents the failure this test was written against): without
  // intrinsic-width, the bare scroll claims the row's full 400-wide
  // allotment, so the sibling lands far past where a shrink-wrapped
  // 30-wide code block would put it -- more than a code-block-width away
  // from where the code swatch itself starts
  val bare-code-x = x-of(t, "bare-code")
  check("bare horizontal scroll claims the row's full width, pushing its sibling out",
        x-of(t, "bare-sibling") > bare-code-x + 100.0)
  // FIX (the regression this test pins): the code swatch is 30 wide with a
  // 10-wide gap, so the sibling must sit exactly 40 past where the code
  // swatch itself starts -- relative to the code element's own x (not a
  // hardcoded absolute), so this doesn't depend on incidental root chrome
  // offsets
  val wrapped-code-x = x-of(t, "wrapped-code")
  check-eq("intrinsic-width shrinks the scroll to its content, sibling follows immediately",
           x-of(t, "wrapped-sibling"), wrapped-code-x + 40.0)

pub fun main()
  test-scenarios("intrinsic-width around a horizontal scroll in a row", Model(), view, update,
                 [("scenario", scenario)])
