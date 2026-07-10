// transform3d + async gallery: a FLIP CARD exercises the 4x4 projected-2D
// transform (rotate-y about the card's own vertical axis, through a
// perspective projection) with ACCURATE unprojected hit-testing -- click
// anywhere on the card, not just its untransformed footprint, to flip it.
// This sample is also the PIXEL CHECK for the ImpellerMatrix row/col-major
// transpose (lib/ui/api/impeller/shim.c's `kk_imp_transform`): if the card
// ever mirrors or skews instead of turning cleanly about its vertical axis,
// that transpose (and web/backend.kk's matching `css3d` transpose) is wrong.
//
// The image row demos `image`'s async load: a VISIBLE "loading..." skeleton
// (`min-load = 250ms` holds it long enough to actually see, anti-flicker
// floor made visible on purpose) before the picture settles in, `fit` modes
// side by side (Cover crops to fill a fixed box; Contain letterboxes), plus
// one `https://` URL -- WEB-ONLY: native has no URL fetch (task #53's
// caveat), so it paints the neutral placeholder box there instead.
//
// Two `future-boundary` cards demo the GENERAL async primitive `image` is
// built on (task #53): one `run` that `wait`s then succeeds, and one that
// fails once and recovers on Retry -- the same generation mechanism that
// makes `image`'s own retry work, exercised directly with no pixels
// involved. These run on EVERY backend; they were native-only until task
// #55, where a `run`'s reentrant `fork` off `async-pump` never executed on
// jsweb -- a JS-backend miscompilation of closures created inside a
// tail-call loop, not anything about async (see docs/ui/design-notes.md 19).
module main

import std/core/unsafe
import std/async
import std/num/float64
import std/time/duration
import ui/widget
import ui/async     // image-path/image + future-boundary (task #53's front door)
import ui/transform
import ui/style/default
import ui/app

// the same Mars frame `assets/mars.jpg` was fetched from (NASA/JPL PIA24543,
// public domain) -- the remote-URL demo loads it live over https, which only
// the web backend can do
val mars-url = "https://assets.science.nasa.gov/dynamicimage/assets/science/psd/photojournal/pia/pia24/pia24543/PIA24543.jpg?w=600&h=396&fit=crop&crop=faces%2Cfocalpoint"

struct model( flipped : bool = False )

type msg
  ToggleFlip

// the card's two faces, flat widgets on the z=0 plane that `transform3d`
// perspective-rotates about the card's center
fun card-face( label : string, bg : color, key : key ) : <keytree,uistate,ioc,theme> widget<msg>
  stack([
    (0.0, 0.0, rect(220.0, 140.0, bg = Just(Fill(bg, 12.0)))),
    (70.0, 58.0, text(label, 20.0, on-accent)),
  ])

// `flipped` is the TARGET; `angle` eases toward 0 or pi (500ms, ease-in-out).
// Past the halfway turn (angle > pi/2) the back face is showing -- that is
// also the face-swap threshold a real card edge-on turn would use.
fun flip-card( flipped : bool, key : key ) : <keytree,uistate,ioc,theme> widget<msg>
  val target = if flipped then pi else 0.0
  val angle = animate(target, duration = 500.0, ease = ease-in-out)
  val showing-back = angle > (pi / 2.0)
  val face = if showing-back
    then card-face("Back", theme.accent, scope("back"))
    else card-face("Front", rgb(0.30, 0.34, 0.46), scope("front"))
  // the click handler goes INSIDE the transform3d, not on a box around it:
  // transform3d is paint+hit-only (layout unchanged), so an OUTER
  // `box(transform3d(...), on-click)` would hit-test the box's flat,
  // UNTRANSFORMED footprint -- and mid-flip a click on the footprint's
  // now-exposed background (where the turned card no longer covers) would
  // fire it. With the handler inside, the accurate UNPROJECTED hit gates the
  // click, so only a click on the actual rotated card toggles.
  transform3d(box(face, on-click = Just(ToggleFlip)),
              perspective(800.0) * rotate-y(angle), ?key = scope("xf"))

// a visible loading skeleton -- the default `default-placeholder` is a plain
// empty box (fine when it flashes for a frame); this sample wants the
// placeholder actually SEEN, so it draws a labeled, tinted, fixed-size rect
// (same stack idiom as `card-face`) instead.
fun loading-box( w : float64, h : float64, key : key ) : <keytree,uistate,ioc,theme> widget<msg>
  stack([
    (0.0, 0.0, rect(w, h, bg = Just(Fill(theme.surface, 8.0)))),
    (8.0, (h / 2.0) - 8.0, text("loading...", 13.0, theme.fg)),
  ], ?key = key)

// ---- future-boundary demos: the general async primitive `image` sits on
// top of, exercised directly with no pixels involved.

// resolves after ~400ms with a value -> the `ready` card
fun slow-fact-run() : <async,ioc,exn> string
  wait(400.milli-seconds)
  "42 (computed asynchronously, off the render thread)"

// fails the FIRST time, recovers on the SECOND (a retry click bumps the
// generation and re-runs) -- module-global so it survives across rebuilds,
// same idiom as test/ui/async-boundary.kk's `attempts`
val flaky-attempts : ref<global,int> = unsafe-total{ ref(0) }

fun flaky-run() : <async,ioc,exn> string
  val n = !flaky-attempts
  flaky-attempts := n + 1
  wait(300.milli-seconds)
  if n == 0
    then throw("simulated failure (first attempt) -- click Retry")
    else "recovered on attempt " ++ (n + 1).show

// the two future-boundary demo cards (every backend -- see the module comment)
fun boundary-demo-rows( key : key ) : <keytree,uistate,ioc,theme> list<widget<msg>>
  [
    body("future-boundary: the general async primitive `image` is built on."),
    body("This one waits ~400ms then shows its result -- no pixels, just the"),
    body("placeholder -> ready lifecycle."),
    card(future-boundary(slow-fact-run,
                         fn(v) column([ text("Answer: " ++ v, 15.0, ?key = scope("val")) ]),
                         placeholder = loading-box(260.0, 30.0, scope("ph-slow")),
                         min-load = zero,
                         ?key = scope("slow"))),

    body("This one fails on its first run; click Retry to re-run it (the"),
    body("generation bump discards the stale failure and kicks a fresh run)."),
    card(future-boundary(flaky-run,
                         fn(v) column([ text("Recovered: " ++ v, 15.0, ?key = scope("val")) ]),
                         placeholder = loading-box(260.0, 30.0, scope("ph-flaky")),
                         ?key = scope("flaky"))),
  ]

fun themed-view( m : model, key : key ) : <keytree,uistate,ioc,theme> widget<msg>
  val boundary-rows = boundary-demo-rows(scope("boundary"))
  page("Koka × transform3d + async", [
    body("Click the card: it turns about its own VERTICAL axis through a"),
    body("perspective projection -- hit-testing is ACCURATE through the turn,"),
    body("not just on its flat footprint."),
    card(flip-card(m.flipped, scope("card"))),

    body("async image load: a visible \"loading...\" skeleton (min-load holds"),
    body("it 250ms so it's actually seen) before the picture settles; Cover"),
    body("crops to fill its box, Contain letterboxes to show the whole picture."),
    // the asset is a WIDE photo (600x396, 3:2) on purpose: `Cover` and
    // `Contain` are only distinguishable when the image aspect differs from
    // the box aspect. The first two boxes below are square and wide
    // respectively, so Cover crops each differently, and the third
    // letterboxes the whole frame -- with a square source (the old 100x100
    // logo) all three drew identical pixels and the demo showed nothing.
    card(row([
      image(FromPath("assets/mars.jpg"), fit = Cover, min-load = 250.milli-seconds,
            placeholder = loading-box(96.0, 96.0, scope("ph1")),
            width = 96.0, height = 96.0, ?key = scope("i1")),
      image(FromPath("assets/mars.jpg"), fit = Cover, min-load = 250.milli-seconds,
            placeholder = loading-box(140.0, 70.0, scope("ph2")),
            width = 140.0, height = 70.0, ?key = scope("i2")),
      image(FromPath("assets/mars.jpg"), fit = Contain, min-load = 250.milli-seconds,
            placeholder = loading-box(96.0, 96.0, scope("ph3")),
            width = 96.0, height = 96.0, ?key = scope("i3")),
    ], gap = 16.0)),

    body("fill sources: the same `Fill` that takes a flat colour also takes a"),
    body("linear or radial gradient, or a picture. Every one is a native"),
    body("primitive on BOTH backends -- an Impeller ColorSource and a CSS"),
    body("background -- so none of it is emulated on either side."),
    // geometry is FRACTIONAL (0..1 of the box), which is why the same source
    // describes the small swatches here and the wide banner below without
    // either knowing the other's size
    card(row([
      rect(96.0, 64.0, bg = Just(Fill(theme.accent, 10.0,
             source = Just(SLinear(0.0, 0.0, 1.0, 1.0, theme.accent, theme.surface)))),
           ?key = scope("s-lin")),
      rect(96.0, 64.0, bg = Just(Fill(theme.accent, 10.0,
             source = Just(SRadial(0.5, 0.5, 0.5, theme.accent, theme.surface)))),
           ?key = scope("s-rad")),
      rect(96.0, 64.0, bg = Just(Fill(theme.surface, 10.0,
             source = Just(SImage("assets/mars.jpg", Cover)))),
           ?key = scope("s-img")),
    ], gap = 16.0)),
    body("The same three at a different aspect: the gradients re-resolve their"),
    body("fractions, and Cover re-crops -- no source mentions a pixel."),
    card(column([
      rect(320.0, 28.0, bg = Just(Fill(theme.accent, 8.0,
             source = Just(SLinear(0.0, 0.0, 1.0, 0.0, theme.accent, theme.bg)))),
           ?key = scope("b-lin")),
      rect(320.0, 28.0, bg = Just(Fill(theme.surface, 8.0,
             source = Just(SImage("assets/mars.jpg", Cover)))),
           ?key = scope("b-img")),
    ], gap = 8.0)),

    body("WEB-ONLY below: a remote https:// image (the same frame, fetched"),
    body("live). Native has no URL fetch (task #53's caveat) and paints the"),
    body("neutral placeholder box instead."),
    card(image-path(mars-url, load = Sync, fit = Contain,
                    width = 200.0, height = 132.0, ?key = scope("url"))),
  ] ++ boundary-rows)

fun view( m : model, key : key ) : <keytree,uistate,ioc> widget<msg>
  with val theme = dark
  themed-view(m, key)

fun update( m : model, msg : msg ) : dispatch<msg> model
  match msg
    ToggleFlip -> m(flipped = !m.flipped)

pub fun main()
  app( Model(), view, update, App-config("Koka × transform3d + async", 480, 720) )
