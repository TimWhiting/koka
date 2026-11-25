// Headless invariants for the site's content model (spec's testing note):
// slugs derive predictably, next/prev is a total order within a quadrant,
// and blocks construct headlessly. Task 4 adds the scenario half: every
// derived route mounts, every derived slug resolves against the REAL shell
// (main.kk), and the cross-page anchor lands the target section at the
// content viewport top.
module smoke

import std/core/unsafe
import std/num/float64
import std/async
import ui/widget
import ui/keytrie
import ui/state
import ui/style/default
import ui/test
import model
import blocks
import pages
import main

val passed : ref<global,int> = unsafe-total{ ref(0) }
val failed : ref<global,int> = unsafe-total{ ref(0) }

// the pure (non-uicheck) half's own tally -- distinct from ui/test's `check`
// (uicheck effect), which the scenario below uses instead
fun pcheck( name : string, cond : bool ) : ioc ()
  if cond then passed := !passed + 1
  else
    failed := !failed + 1
    println("FAIL: " ++ name)

type mm
  MNone

fun no-body( k : key ) : <keytree,uistate,ioc,theme> list<widget<mm>>
  []

val fixture : list<doc-page<mm>> =
  [ Doc-page(QTutorial, "t-one", "T One", "", [Doc-section("Alpha Beta", no-body)]),
    Doc-page(QTutorial, "t-two", "T Two", "", []),
    Doc-page(QReference, "r-one", "R One", "", []) ]

fun pure-checks()
  pcheck("slugify lowercases and dashes", slugify("Animate a Value") == "animate-a-value")
  pcheck("slugify drops punctuation", slugify("Keys & identity!") == "keys--identity")
  val (p1, n1) = fixture.next-prev("t-one")
  pcheck("first page has no prev", p1.is-nothing)
  pcheck("first page's next is its quadrant sibling", n1.map(fn(p) p.slug).default("") == "t-two")
  val (p2, n2) = fixture.next-prev("t-two")
  pcheck("last-in-quadrant has no next (other quadrants excluded)", n2.is-nothing)
  pcheck("prev links back", p2.map(fn(p) p.slug).default("") == "t-one")
  pcheck("unknown slug is (Nothing, Nothing)", fixture.next-prev("nope").fst.is-nothing)
  // parse-code-spans: backtick spans strip to a plain string, with offsets
  // pinned against the STRIPPED string ("the " is 4 chars -> span starts at
  // 4; "padding" is 7 chars -> span ends at 11) so a future refactor can't
  // silently shift them.
  val (pcs-text, pcs-spans) = parse-code-spans("the `padding` param", mono(16.0))
  pcheck("parse-code-spans strips backticks", pcs-text == "the padding param")
  match pcs-spans
    [Text-span(s, e, Just(f), Nothing, Nothing)] ->
      pcheck("parse-code-spans span offsets", s == 4 && e == 11)
      pcheck("parse-code-spans span uses mono font", f.size == 16.0)
    _ -> pcheck("parse-code-spans returns exactly one mono span", False)
  // blocks build headlessly at a root key (no layout needed to construct)
  with with-keytree
  with val theme = theme/dark
  val n : widget<mm> = note("hi", ?key = root-key)
  pcheck("note constructs", True)
  val sa : widget<mm> = see-also([("reference-widgets#text", "Text")], ?key = root-key)
  pcheck("see-also constructs", True)
  println("SMOKE: " ++ (!passed).show ++ "/" ++ (!passed + !failed).show ++ " passed")
  if !failed > 0 then println("SMOKE: FAILED")

// the y of the selector's target, or -1.0 if it isn't mounted/visible --
// same reading as test/ui/anchor-scroll.kk's `top-of`
fun top-of( t : tester<msg>, sel : string ) : <async,keytree,uistate,uicheck,ioc,exn> float64
  match t.find(sel)
    Just((_, y, _, _)) -> y
    Nothing -> -1.0

// drives the REAL shell (main.kk's model/view/update): the cross-page anchor
// lands the target section at the content viewport top, then every derived
// page mounts and every derived slug resolves.
//
// Link clicks are HEADLESS no-ops (`ui/test`'s `dispatch-click` treats
// `HitLink` as host-side-only -- see its comment), so page navigation here
// goes through `t.emit(Navigated(...))` directly rather than `t.click` on
// the sidebar/cross-page links -- the route the brief's fallback describes.
//
// `find-ids` can retain KeepAlive-but-unmounted ids from earlier mounts of
// the same slug (ui/keytrie), but `scroll-to`'s `resolve-anchor` (ui/state)
// filters those matches down to ids `owner-present` in the laid-out tree
// (fixed by 312c08b9c; test/ui/anchor-scroll.kk case (4) pins it), so a
// stale id can no longer shadow the live one. The cross-page check below
// still runs on the page's FIRST mount, before section 2 revisits
// explanation-one-core a second time, but that ordering is now incidental
// rather than load-bearing.
pub fun site-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  // 1. cross-page anchor: from home, "explanation-one-core#state-without-the-model"
  //    switches page AND scrolls the target section to the content viewport
  //    top. The link itself can't be clicked headlessly (see above), so this
  //    drives the two halves the link's target performs -- navigate, then
  //    `scroll-to` the fragment -- and asserts the section lands where the
  //    page's own top-of-viewport element (`doc-title`, unscrolled) sits.
  (t.emit)(Navigated(Home))
  t.settle()
  (t.emit)(Navigated(Page("explanation-one-core")))
  t.settle()
  // `doc-title` sits at content-relative y=0 within the scroll region, but
  // `themed-view` wraps `page-body` in `box(..., padding = 8.0)` BEFORE the
  // scroll -- that padding is INSIDE the scrolled content (contributes to
  // every node's content-relative y, `doc-title`'s included), whereas a
  // `scroll-to`'d node's clamp brings its content-relative y down to equal
  // the offset, landing it exactly at the scroll region's own top edge --
  // 8.0 ABOVE where `doc-title` naturally sits. Subtract that same padding
  // (main.kk's `themed-view`) to get the true content viewport top.
  val viewport-top = top-of(t, "title") - 8.0
  scroll-to("state-without-the-model")
  t.settle()
  check-eq("cross-page anchor lands the section at the content viewport top",
           top-of(t, "state-without-the-model"), viewport-top)

  // 2. every page mounts and every derived slug resolves to EXACTLY ONE
  //    mounted id (explanation-one-core included -- this is its SECOND
  //    mount, which is fine now that resolution filters to what's actually
  //    mounted). Asserting length == 1 rather than merely `is-cons` catches
  //    slug collisions -- e.g. a section title and an `api-entry` name that
  //    both slugify to the same anchor -- that a mere "resolves" check
  //    would miss.
  site-pages().foreach fn(p)
    (t.emit)(Navigated(Page(p.slug)))
    t.settle()
    p.sections.foreach fn(s)
      check("slug resolves to exactly one id: " ++ p.slug ++ "#" ++ slugify(s.title),
            find-ids(slugify(s.title)).length == 1)

pub val shared-scenarios = [
  ("site", site-scenario),
]

pub fun main()
  pure-checks()
  // a SHORT window (unlike the real app's 900x640): the explanation page's
  // content easily fits an ordinary window, so nothing would be left to
  // scroll and the cross-page anchor check would pass trivially at offset 0
  // -- shrinking the height forces the content to overflow, exactly like
  // test/ui/anchor-scroll.kk's 400x300 window does for its fixed sections.
  test-scenarios("site", Model(Home, dark = False), view, update, shared-scenarios,
                 App-config("Koka × ui docs", 900, 220))
