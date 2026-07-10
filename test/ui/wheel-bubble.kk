// A vertical wheel tick that starts over a NESTED horizontal scroll (a
// code-block, a carousel) must reach the enclosing vertical scroll instead
// of being trapped by the horizontal region closest to the cursor --
// `apply-wheel` (ui/state) walks the whole `scroll-at` chain and prefers a
// region on the gesture's own axis over the innermost region regardless of
// axis. A true standalone horizontal carousel (no vertical scroll around
// it) still falls back to consuming a plain vertical wheel, unchanged.
module wheel-bubble

import std/async
import std/num/float64
import std/core/undiv
import ui/widget
import ui/state
import ui/test

pub struct model()
pub type msg
  Nop

// a short vertical "page" scroll (viewport 100) whose one child is a WIDE
// horizontal scroll (viewport 60, content 300) -- both overflow, so both
// qualify as scroll-at regions at the point under the cursor
pub fun view( m : model, key : key ) : <keytree,uistate,scene<msg>,ioc> widget<msg>
  fixed(
    scroll( column([
      scroll( row([ rect(300.0, 60.0, bg = Just(Fill(rgb(0.2, 0.2, 0.3)))) ]),
              horizontal = True, name = "hscroll" ),
      rect(80.0, 400.0, bg = Just(Fill(rgb(0.3, 0.2, 0.2)))),   // pads content past the viewport
    ], gap = 0.0), name = "vscroll" ),
    width = Just(120.0), height = Just(100.0) )

pub fun update( m : model, msg : msg ) : dispatch<msg> model
  m

pub fun wheel-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  t.settle()
  val tree0 = (t.get-tree)()
  // a pure vertical wheel tick (dx=0) at a point inside the horizontal
  // scroll's viewport (it sits at the page's top, so y=10 is inside it).
  // Negative dy: `apply-wheel`'s convention is delta>0 REVEALS EARLIER
  // content (wheel-up); both regions start at offset 0, so a positive delta
  // would correctly stay clamped at 0 regardless of bubbling -- a negative
  // delta is the one that actually moves an offset off zero.
  val changed = pretend-no-div( fn() apply-wheel(tree0, 10.0, 10.0, 0.0, -20.0) )
  check("a vertical wheel over a nested horizontal scroll moves something", changed)
  t.settle()
  val hstate = all-scroll-states().find(fn(kv) kv.snd.content == 300.0)
  val vstate = all-scroll-states().find(fn(kv) kv.snd.content > 300.0)   // vscroll: 60 + 400
  check("the horizontal region's own offset is untouched",
        match hstate { Just((_, s)) -> s.offset == 0.0; Nothing -> False })
  check("the enclosing vertical region moved instead",
        match vstate { Just((_, s)) -> s.offset > 0.0; Nothing -> False })

pub fun main()
  test-scenarios("wheel bubbles past a mismatched-axis scroll to its vertical parent", Model(), view, update,
                 [("wheel", wheel-scenario)])
