// Accurate inverse-projected hit-testing for `transform3d` (task 3): a
// known-size, known-position box behind a real perspective+rotate-y matrix.
// This test builds the SAME center-wrapped `M'` the paint/hit-go arm uses
// (see `lib/ui/api/impeller/backend.kk`'s `LTransform3d` paint arm and
// `lib/ui/widget.kk`'s `LTransform3d` hit-go arm), forward-projects the
// box's center through it to get a screen point, and asserts:
//   - a click at that projected center HITS the box's message (the box's
//     own center is invariant under any transform pivoted about that same
//     center, so this passes both BEFORE and AFTER the fix -- a sanity
//     check, not the regression pin)
//   - a click well OUTSIDE the box's projected (screen) quad, but still
//     inside its UNTRANSFORMED layout rect, MISSES -- this is the
//     regression pin: the OLD approximate hit-go arm (recurses the child
//     untransformed) wrongly HITS here, because it only compares the click
//     against the untransformed rect and ignores the matrix entirely.
//
// Coordinate frame (resolved empirically, pinned here in a comment):
// `hit-go` threads the SAME (px,py) pointer-screen coordinates all the way
// down, accumulating the ABSOLUTE (x,y) origin of each node as it descends
// (every leaf/box arm compares `px`/`py` against that accumulated origin,
// e.g. `px < x || px > x + w`). `LTransform3d`'s paint arm concatenates
// `M' = translate3(cx,cy,0) * m * translate3(-cx,-cy,0)` about the child's
// center `(cx,cy) = (x + w0/2, y + h0/2)` and paints the child at its own
// (x,y) UNDER that canvas transform -- i.e. `M'` maps the child's own
// pre-transform (x,y)-based absolute frame directly to the screen. So
// `unproject(M', px, py)` already returns coordinates in the SAME
// (x,y)-based absolute frame `hit-go` expects everywhere else: the fix
// passes the unprojected point through as the new (px,py), leaving the
// (x,y) accumulator UNCHANGED -- `child.hit-go(lx, ly, x, y)`, NOT
// `child.hit-go(lx + x, ly + y, x, y)`.
module transform-hit

import std/async
import std/num/float64
import ui/widget
import ui/keytrie   // the `key` type + `keytree` effect (view/scenario signatures)
import ui/reactive  // the `uistate` effect
import ui/view      // the `scene<a>` effect
import ui/ident     // `scope`
import ui/transform
import ui/test

pub struct model( clicked : bool = False )

pub type msg
  Clicked

// the box: fixed size, fixed position. Root layout is TIGHT to the harness's
// window size (`test-scenarios` lays out at `tight(config.width, config.height)`),
// so a bare box as the sole/root widget would be STRETCHED to fill it;
// `stack`'s absolute placement gives it its own natural size at a literal
// (bx,by) instead -- exactly the known position this test needs.
val box-w = 200.0
val box-h = 140.0
val bx    = 0.0
val by    = 0.0

// perspective(800) * rotate-y(0.6): a real, non-trivial 3D tilt (not just a
// 2D affine skew) -- deterministic, so the projection below is reproducible
val mtx = perspective(800.0) * rotate-y(0.6)

pub fun view( m : model, key : key ) : <keytree,uistate,scene<msg>,ioc> widget<msg>
  stack([
    (bx, by, transform3d(
               rect(box-w, box-h, bg = Just(Fill(rgb(0.3, 0.55, 0.85))), on-click = Just(Clicked), ?key = scope("box")),
               mtx, ?key = scope("t3d"))),
    (0.0, box-h + 20.0, text("clicked: " ++ m.clicked.show, 13.0, ?key = scope("status"))),
  ])

pub fun update( m : model, msg : msg ) : dispatch<msg> model
  match msg
    Clicked -> m(clicked = True)

pub fun hit-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  check-eq("starts unclicked", t.texts("status"), ["clicked: False"])
  val cx = bx + box-w / 2.0
  val cy = by + box-h / 2.0
  // the SAME center-wrapped M' the paint/hit-go arm builds
  val m3 = translate3(cx, cy, 0.0) * mtx * translate3(0.0 - cx, 0.0 - cy, 0.0)
  // a far offset along x from the projected center: with
  // perspective(800)*rotate-y(0.6) over this 200x140 box, the RIGHT edge of
  // the box's projected (screen) quad sits at x ~= 177 (well short of the
  // untransformed box's own right edge at x = 200) -- (cx + 95, cy) =
  // (195, 70) is still inside the untransformed rect [0,200]x[0,140] (so the
  // APPROXIMATE hit-go arm, which recurses the child untransformed, wrongly
  // HITS here) but well outside the actual projected quad (so the accurate
  // unproject-based arm correctly MISSES)
  val mx = cx + 95.0
  val my = cy
  t.click-at(mx, my)
  t.settle()
  check-eq("off-quad click misses (regression pin for the old approximate hit)", t.texts("status"), ["clicked: False"])
  // forward-project the box's center through M' to get the click point
  val (cbigx, cbigy, _cbigz, cbigw) = apply-point(m3, cx, cy, 0.0)
  val sx = cbigx / cbigw
  val sy = cbigy / cbigw
  t.click-at(sx, sy)
  t.settle()
  check-eq("projected-center click hits through the transform", t.texts("status"), ["clicked: True"])

pub val shared-scenarios = [
  ("hit", hit-scenario),
]

pub fun main()
  test-scenarios("transform3d hit-testing", Model(), view, update, shared-scenarios)
