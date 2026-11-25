// `rich`'s wrap geometry and click-hit-testing, proven against
// `ui/test`'s deterministic fixed-width measurer (the same one `Text`'s
// own wrap/hit behavior is proven against) -- no real backend text
// engine involved, matching every other layout-math test in this suite.
//
// The clicked span's name is rendered back into a plain `text` widget
// (scoped "last") so the scenario can assert on it via `t.texts("last")`
// the same way other headless tests in this suite read back app state --
// through what's actually painted, not by reaching into `model` directly.
module rich-text

import std/async
import std/num/float64
import ui/widget
import ui/keytrie
import ui/reactive
import ui/view
import ui/ident
import ui/test

pub struct model( last : string = "none" )
pub type msg
  Clicked( which : string )

pub fun view( m : model, key : key ) : <keytree,uistate,scene<msg>,ioc> widget<msg>
  column([
    fixed(
      rich("plain aaaa bbbb", 10.0, spans = [
        Text-span(6, 10, on-click = Just(Clicked("aaaa"))),
      ], wrap = True, ?key = scope("r")),
      width = Just(24.0) ),   // narrow enough to force a wrap mid-content
    text(m.last, 10.0, ?key = scope("last")),
  ])

pub fun update( m : model, msg : msg ) : dispatch<msg> model
  match msg
    Clicked(which) -> m(last = which)

pub fun rich-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  t.settle()
  check-eq("starts unclicked", t.texts("last"), ["none"])
  // "plain aaaa bbbb" (15 codepoints) at cw=6.0 (10.0 * 0.6), lh=12.5
  // (10.0 * 1.25), 24px width -> 4 chars/line: "plai"(0-3) / "n aa"(4-7) /
  // "aa b"(8-11) / "bbb"(12-14) -- span [6,10) ("aaaa") straddles that wrap:
  // chars 6-7 land on line 1 (rect x=12,y=12.5,w=12,h=12.5 RELATIVE to the
  // `rich` widget's own origin), chars 8-9 land on line 2 (rect
  // x=0,y=25,w=12,h=12.5) -- worked out from `rect-for`'s walk in
  // `with-test-measure`'s `measure-rich` handler. The harness centers the
  // column in its fixed-size window, so the widget's ABSOLUTE origin is
  // (228,0) here (verified via `t.find("r")`), not (0,0) -- click points
  // below are that offset plus the relative rect centers.
  t.click-at(246.0, 18.0)    // inside line 1's slice of the span (chars 6-7)
  t.settle()
  check-eq("click on the span's first-line slice resolves", t.texts("last"), ["aaaa"])
  (t.emit)(Clicked("none"))   // reset between assertions
  t.settle()
  t.click-at(234.0, 31.0)    // inside line 2's slice of the span (chars 8-9)
  t.settle()
  check-eq("click on the span's wrapped-continuation slice also resolves", t.texts("last"), ["aaaa"])

pub fun main()
  test-scenarios("rich bubbles clicks through a wrapped span", Model(), view, update,
                 [("rich", rich-scenario)])
