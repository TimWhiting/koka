// `clip` is a HIT boundary, not just a paint one.
//
// The point of clipping, for an ink ripple, is that the child cannot draw
// outside the rounded rect. But a clip that only cut PAINT would leave the
// child still touchable out there -- an invisible button extending past its
// own edge, which is worse than no clip at all because nothing on screen
// explains it. So `hit-go`/`hover-key`/`hover-rect` all reject a point
// outside the clip rect before descending.
//
// The child here is deliberately BIGGER than the clip, so there is a band
// that is inside the child's own laid-out rect and outside the clip. Without
// the rejection every check below still finds the child (that band is exactly
// where the bug would live); with it, only the inside click lands.
//
// Corner radii are approximated by the rect on purpose (see `clip`'s doc):
// the corner-cutout case is NOT pinned here because it is not the behaviour --
// a press in the rounded corner still reaches the child, matching what a
// scroll viewport already does.
module clip-hit

import std/async
import std/num/float64
import ui/widget
import ui/keytrie
import ui/reactive
import ui/view
import ui/ident
import ui/test

pub struct model( clicked : bool = False )

pub type msg
  Clicked

// the clip is 120x80; the child inside it is 300x200, so x in (120,300) is
// inside the CHILD and outside the CLIP
val clip-w  = 120.0
val clip-h  = 80.0
val child-w = 300.0
val child-h = 200.0

pub fun view( m : model, key : key ) : <keytree,uistate,scene<msg>,ioc> widget<msg>
  stack([
    (0.0, 0.0, clip(
                 rect(child-w, child-h, bg = Just(Fill(rgb(0.3, 0.55, 0.85))),
                      on-click = Just(Clicked), ?key = scope("box")),
                 radius = 12.0, width = Just(clip-w), height = Just(clip-h),
                 ?key = scope("clip"))),
    (0.0, child-h + 20.0, text("clicked: " ++ m.clicked.show, 13.0, ?key = scope("status"))),
  ])

pub fun update( m : model, msg : msg ) : dispatch<msg> model
  match msg
    Clicked -> m(clicked = True)

pub fun clip-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  check-eq("starts unclicked", t.texts("status"), ["clicked: False"])

  // OUTSIDE the clip but INSIDE the child's own rect: the regression pin. A
  // paint-only clip leaves this hitting.
  t.click-at(clip-w + 40.0, clip-h / 2.0)
  t.settle()
  check-eq("a click past the clip's right edge misses", t.texts("status"), ["clicked: False"])

  // same, below the clip
  t.click-at(clip-w / 2.0, clip-h + 40.0)
  t.settle()
  check-eq("a click below the clip's bottom edge misses", t.texts("status"), ["clicked: False"])

  // INSIDE: the clip must not swallow legitimate input
  t.click-at(clip-w / 2.0, clip-h / 2.0)
  t.settle()
  check-eq("a click inside the clip still reaches the child", t.texts("status"), ["clicked: True"])

pub val shared-scenarios = [
  ("clip", clip-scenario),
]

pub fun main()
  test-scenarios("clip hit-testing", Model(), view, update, shared-scenarios)
