// scroll-to-anchor (docs-site groundwork, task #62): `scroll-to(slug)` sets a
// scroll region's OFFSET so the section named by the slug sits at the top of
// its viewport. Scrolling is Koka-owned (no browser `#anchor`, and no browser
// at all natively), so this is a ui/state primitive: the request pends until
// the target is BUILT, and resolution happens inside `bake-scroll` -- between
// layout and paint -- so the frame that first shows the target page already
// paints scrolled. Landing at the top and then jumping is exactly the failure
// mode that placement prevents, and the cross-page scenario below would catch
// it as a wrong offset.
//
// Geometry is exact by construction: sections are fixed 100-tall rects in a
// gap-0 column inside a 300-tall viewport, so section N sits at (N-1)*100 and
// every expected offset is arithmetic, not measurement.
module anchor-scroll

import std/async
import std/num/float64
import ui/widget
import ui/keytrie
import ui/reactive
import ui/state
import ui/view
import ui/ident
import ui/test

pub struct model( page : int = 1 )

pub type msg
  GoPage2
  GoPage1

// ten fixed-height sections; slugs are scope names, exactly as the docs site
// will declare them ("animate-a-value" etc.)
fun sections( pfx : string, key : key ) : <keytree,uistate,ioc> list<widget<msg>>
  list(1, 10).map fn(i)
    rect(280.0, 100.0, bg = Just(Fill(rgb(0.2, 0.2, 0.3))), ?key = scope(pfx ++ "-" ++ i.show))

pub fun view( m : model, key : key ) : <keytree,uistate,scene<msg>,ioc> widget<msg>
  if m.page == 1 then
    column([
      rect(60.0, 20.0, bg = Just(Fill(rgb(0.5, 0.5, 0.5))), on-click = Just(GoPage2), ?key = scope("go2")),
      expanded(scroll(column(sections("a", scope("secs1")), gap = 0.0), name = "doc1")),
    ], gap = 0.0)
  else
    column([
      rect(60.0, 20.0, bg = Just(Fill(rgb(0.5, 0.5, 0.5))), on-click = Just(GoPage1), ?key = scope("hdr2")),
      expanded(scroll(column(sections("b", scope("secs2")), gap = 0.0), name = "doc2")),
    ], gap = 0.0)

pub fun update( m : model, msg : msg ) : dispatch<msg> model
  match msg
    GoPage2 -> m(page = 2)
    GoPage1 -> m(page = 1)

// assert by the SCREEN rect of a section (t.find gives the laid-out, baked,
// clipped rect): what the user sees, rather than internal offsets -- and
// robust to how the region's key is minted
fun top-of( t : tester<msg>, sel : string ) : <async,keytree,uistate,uicheck,ioc,exn> float64
  match t.find(sel)
    Just((_, y, _, _)) -> y
    Nothing -> -1.0                 // clipped away / not mounted

pub fun anchor-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  // 20px header, so the viewport spans y in [20, 300): section tops land at 20
  check-eq("starts unscrolled: first section at the viewport top", top-of(t, "a-1"), 20.0)
  check-eq("a-5 starts clipped out of view", top-of(t, "a-5"), -1.0)

  // (1) SAME-PAGE anchor: no model change at all -- just scroll-to and the
  // render it requests
  scroll-to("a-5")
  t.settle()
  check-eq("in-page anchor puts the section at the viewport top", top-of(t, "a-5"), 20.0)

  // (2) clamped: content 1000, viewport 280, so max offset is 720 and the
  // last section's top can only reach 20 + (900 - 720)
  scroll-to("a-10")
  t.settle()
  check-eq("an anchor near the end clamps to max offset", top-of(t, "a-10"), 200.0)

  // (3) CROSS-PAGE: request an anchor on a page that is NOT built, then
  // navigate. The request must survive until the target exists and resolve on
  // the frame the new page appears.
  scroll-to("b-3")
  t.settle()
  check-eq("a pending anchor does not disturb the current page", top-of(t, "a-10"), 200.0)
  t.click("go2")
  t.settle()
  check-eq("navigation resolves the pending anchor on the new page", top-of(t, "b-3"), 20.0)

  // (4) STALENESS: the keytree registry can retain ids for sections that are
  // no longer mounted. After VISITING page 2 and returning to page 1, "b-5"
  // still resolves in the registry -- but it is not in the tree. A pending
  // anchor must NOT be consumed by that stale id: it waits for the target to
  // actually mount, then scrolls. (The docs site hit this: revisiting a page
  // could silently swallow a cross-page anchor.)
  t.click("hdr2")            // back to page 1 (page 2's sections now stale in the registry)
  t.settle()
  scroll-to("b-5")           // page 2 is NOT mounted; the registry remembers it
  t.settle()
  t.click("go2")             // NOW mount page 2
  t.settle()
  check-eq("a pending anchor survives a stale registry id and resolves on mount",
           top-of(t, "b-5"), 20.0)

pub val shared-scenarios = [
  ("anchor", anchor-scenario),
]

pub fun main()
  test-scenarios("scroll-to-anchor", Model(), view, update, shared-scenarios,
                 App-config("anchor", 400, 300))
