// A scroll nested inside a scroll of the OTHER axis must shrink-wrap its
// viewport in the axis its parent leaves unbounded. The docs site hit this:
// `code-block` is a horizontal scroll, and inside a page's vertical scroll
// (whose child is laid out with unbounded height) its viewport height clamped
// to the 1e7 unbounded sentinel -- every code block became a ten-million-px
// box and the page's scroll extent was effectively infinite.
module nested-scroll

import std/async
import std/num/float64
import ui/widget
import ui/state
import ui/test

pub struct model()
pub type msg
  Nop

// a 20px header over a vertical scroll ("page") whose column holds one
// code-block-shaped child (a horizontal scroll of a wide 30-tall rect) and a
// plain rect after it -- geometry is exact by construction
pub fun view( m : model, key : key ) : <keytree,uistate,scene<msg>,ioc> widget<msg>
  column([
    rect(60.0, 20.0, bg = Just(Fill(rgb(0.5, 0.5, 0.5))), ?key = scope("hdr")),
    expanded( scroll( column([
      // the PADDED box matters: padding subtracts from the unbounded max-height
      // on the way down, so the nested scroll sees 1e7 - 28 -- still unbounded
      // in spirit, no longer equal to the sentinel (this is exactly the docs
      // site's `code-block` shape, which reproduced after a sentinel-equality fix)
      box( scroll( rect(900.0, 30.0, bg = Just(Fill(rgb(0.2, 0.2, 0.3))), ?key = scope("wide")),
                   horizontal = True ),
           padding = 14.0 ),
      rect(100.0, 50.0, bg = Just(Fill(rgb(0.3, 0.2, 0.2))), ?key = scope("after")),
    ], gap = 0.0), name = "page") ),
  ], gap = 0.0)

pub fun update( m : model, msg : msg ) : dispatch<msg> model
  m

fun top-of( t : tester<msg>, sel : string ) : <async,keytree,uistate,uicheck,ioc,exn> float64
  match t.find(sel)
    Just((_, y, _, _)) -> y
    Nothing -> -1.0                 // clipped away / not mounted

pub fun nested-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  t.settle()
  // the horizontal scroll is exactly as tall as its 30-tall child, so the
  // rect after it sits at 20 (header) + 30 + 2*14 (box padding)
  check-eq("content after a nested horizontal scroll sits directly below it",
           top-of(t, "after"), 78.0)
  // the vertical scroll's content extent is (30 + 28) + 50, not 1e7-ish
  check("vertical scroll content is the sum of its children's heights",
        all-scroll-states().any(fn(kv) kv.snd.content == 108.0),
        "want content=108")

pub fun main()
  test-scenarios("nested scroll shrink-wraps its unbounded axis", Model(), view, update,
                 [("nested", nested-scenario)])
