// The documentation site for lib/ui -- DOGFOODED with lib/ui itself. It is a
// real routed SPA: the sidebar items are `link`s (real <a href="#/..."> on the
// web, deep-linkable, back/forward), the content area is a `scroll` region that
// fills the space under a fixed header (`expanded`), and every page mixes prose,
// code, and LIVE widgets. Organized by Diátaxis (tutorials / how-to / reference
// / explanation). The SAME code runs on wasi-web, jsweb, and native.
//
// Routing/rendering are now DERIVED from the content model (model.kk's
// `doc-page`/`doc-section`, pages.kk's `site-pages()`): a route is just
// `Home | Page(slug)`, the sidebar groups `site-pages()` by quadrant in
// display order, and one `render-page` walks any page's sections -- there is
// no more hand-written per-page routing or view (content.kk is retired).
module main

import ui/widget
import ui/style/default
import ui/keytrie
import ui/ident
import ui/state
import ui/router
import ui/app
import model
import blocks
import pages

pub type route
  Home
  Page( slug : string )

// unknown slugs fall back to Home (a broken/removed deep link lands on the
// landing page rather than a dead page)
pub fun parse-route( path : string ) : route
  if path.is-empty then Home
  else match site-pages().find-page(path)
    Just(_) -> Page(path)
    Nothing -> Home

pub fun print-route( r : route ) : string
  match r
    Home -> ""
    Page(s) -> s

pub type msg
  Navigated( route : route )
  ToggleTheme

pub struct model( route : route, dark : bool = False )

// whether `target` (a page slug, or "" for Home) is the current route
fun route/active( r : route, target : string ) : bool
  match r
    Home -> target == ""
    Page(s) -> s == target

// a sidebar entry: a real link to the page, accent-filled when active
fun nav-entry( label : string, target : string, active : bool, ?key : key ) : theme widget<msg>
  val bg = if active then Fill(theme.accent, 8.0) else Fill(theme.surface, 8.0)
  val fg = if active then on-accent else theme.fg
  link( target, box(text(label, 15.0, fg), padding = 10.0, bg = Just(bg)) )

// one quadrant's sidebar group: its header plus its pages' nav entries
fun quadrant-entries( q : quadrant, m : model, key : key ) : <keytree,theme> list<widget<msg>>
  [ text(q.show, 12.0, theme.accent) ] ++
  site-pages().filter(fn(p : doc-page<msg>) p.quadrant.same(q)).map(fn(p) nav-entry(p.title, p.slug, m.route.active(p.slug), ?key = scope("nav-" ++ p.slug)))

// the sidebar derives entirely from `site-pages()`, grouped by quadrant in
// the fixed Diátaxis display order; Home is the one entry outside the
// quadrants (it has no `doc-page` of its own -- see pages.kk). Now that the
// reference quadrant alone has 9 topics, the nav list is taller than a short
// window -- `sidebar` sits beside the content's own `scroll` (below) inside
// a row whose height the outer `expanded` already bounds, so wrapping the
// nav column in its OWN `scroll` lets it pan independently once it doesn't
// fit, instead of silently overflowing past the window's bottom edge.
//
// A vertical `scroll`'s CROSS axis (width, here) reports the full width its
// row parent offers rather than shrinking to its content -- the exact same
// mechanism `demo-panel`'s horizontal `scroll` hit (blocks.kk, `code-block`),
// just on the other axis: it swallowed nearly the whole row's width, leaving
// the content column almost none and exploding its wrapped-text height by
// orders of magnitude (see test/ui/intrinsic-scroll-row.kk for the general
// mechanism). `intrinsic-width` is the same fix: measure the nav column's
// own natural width first, then give the scroll exactly that much.
fun sidebar( m : model, key : key ) : <keytree,theme> widget<msg>
  box( intrinsic-width(scroll( column(
    [ nav-entry("Home", "", m.route.active(""), ?key = scope("nav-home")) ] ++
    [QTutorial, QHowTo, QReference, QExplanation].flatmap(fn(q) quadrant-entries(q, m, key)),
    gap = 8.0), name = "sidebar" )),
    padding = 14.0, bg = Just(Fill(theme.surface, 12.0)) )

// prev/next within the page's quadrant, as plain links either side of a
// spacer; the ends that don't exist are simply omitted
fun next-prev-links( p : doc-page<msg>, key : key ) : <keytree,theme> widget<msg>
  val (prev, next) = next-prev(site-pages(), p.slug)
  val prev-link = match prev
    Just(pp) -> [ link(pp.slug, accented("<- " ++ pp.title, 15.0), ?key = scope("prev")) ]
    Nothing  -> []
  val next-link = match next
    Just(nn) -> [ link(nn.slug, accented(nn.title ++ " ->", 15.0), ?key = scope("next")) ]
    Nothing  -> []
  row( prev-link ++ [ spacer() ] ++ next-link, gap = 12.0 )

// one on-this-page rail entry: the section's title, scrolling its own
// self-anchored heading into view when clicked
fun toc-entry( s : doc-section<msg>, key : key ) : <keytree,uistate,ioc,theme> widget<msg>
  act( text(s.title, 13.0, theme.accent, ?key = scope("toc-" ++ slugify(s.title))),
       fn() scroll-to(slugify(s.title)) )

// a section's heading (self-anchoring, blocks.kk) plus its body
fun section-widgets( s : doc-section<msg>, key : key ) : <keytree,uistate,ioc,theme> list<widget<msg>>
  [ heading(s.title) ] ++ (s.body)(scope(slugify(s.title)))

// ONE renderer for every quadrant page: title, intro, an on-this-page rail
// (section titles that `scroll-to` their own self-anchored heading), every
// section's heading + body, then prev/next
fun render-page( p : doc-page<msg>, key : key ) : <keytree,uistate,ioc,theme> widget<msg>
  column(
    [ doc-title(p.title, ?key = scope("title")),
      prose(p.intro, ?key = scope("intro")),
      row( p.sections.map(fn(s) toc-entry(s, key)), gap = 12.0 ) ] ++
    p.sections.flatmap(fn(s) section-widgets(s, key)) ++
    [ next-prev-links(p, key) ],
    gap = 15.0 )

fun page-body( m : model, key : key ) : <keytree,uistate,ioc,theme> widget<msg>
  match m.route
    Home -> column(home-body(key), gap = 16.0)
    Page(slug) ->
      match site-pages().find-page(slug)
        Just(p) -> render-page(p, key)
        Nothing -> column(home-body(key), gap = 16.0)   // parse-route already guards this

fun themed-view( m : model, key : key ) : <keytree,uistate,ioc,theme> widget<msg>
  box( column([
    // fixed header
    row([
      accented("Koka × ui docs", 20.0),
      spacer(),
      quiet-button(if m.dark then "Light" else "Dark", ToggleTheme),
    ]),
    // sidebar + scrollable content fill the rest
    expanded( row([
      sidebar(m, key),
      expanded( scroll( box(page-body(m, key), padding = 8.0), name = "doc" ) ),
    ], gap = 16.0, fill = True) ),
  ], gap = 16.0, fill = True), padding = 20.0, bg = Just(Fill(theme.bg)) )

pub fun view( m : model, key : key ) : <keytree,uistate,ioc> widget<msg>
  // whole-theme crossfade: one animated t interpolates the palette
  val t = animate(if m.dark then 1.0 else 0.0, duration = 250.0)
  with val theme = theme/light.mix(theme/dark, t)
  themed-view(m, key)

pub fun update( m : model, msg : msg ) : dispatch<msg> model
  match msg
    Navigated(r) -> m(route = r)
    ToggleTheme  -> m(dark = !m.dark)

pub fun main()
  app( Model(Home, dark = system-dark()), view, update,
       App-config("Koka × ui docs", 900, 640),
       subs = [ fn(ch) anchor-route-sub(ch, parse-route, Navigated) ] )
