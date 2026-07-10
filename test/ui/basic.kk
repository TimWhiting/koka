// Basic exercise of ui/test: a mini todo app (field + buttons + list +
// counter), driven headless -- clicks and typing dispatch through the same
// hit-testing as the real backends.
module basic

import std/async
import std/num/float64
import std/time/duration  // milli-seconds: the async image min-load
import ui/widget
import ui/async   // image / image-path / FromBytes / FromPixels (task #53)
import ui/style/default
import ui/lazy
import ui/test

pub struct model( items : list<string> = [], clicks : int = 0, note : string = "", show-pic : bool = True,
                  pic-src : string = "assets/x.png", show-async : bool = False,
                  async-pic-src : string = "assets/x.png" )

pub type msg
  Add( what : string )
  Bump
  SetNote( note : string )
  TogglePic
  SwapPicSrc
  ShowAsync            // live tier: toggle the async-image row (task #53)
  SwapAsyncPicSrc      // live tier (review Important #1): swap the ASYNC row's
                       // FromPath source at its stable ?key, no widget -- like
                       // SwapPicSrc, emitted directly by the scenario

// a tiny valid 2x2 PNG (the bytes of test/ui/live/assets/x.png), embedded so
// the `FromBytes` async path decodes a KNOWN input with no file on disk. Values
// > 127 are the int8 two's-complement (255 -> -1), read back as raw bytes C-side.
val demo-png-bytes : vector<int8> =
  [-119,80,78,71,13,10,26,10,0,0,0,13,73,72,68,82,0,0,0,2,0,0,0,2,8,2,0,0,0,
   -3,-44,-102,115,0,0,0,16,73,68,65,84,120,-100,99,-8,-49,-64,0,68,12,16,10,
   0,31,-18,3,-3,-117,95,20,-44,0,0,0,0,73,69,78,68,-82,66,96,-126]
    .map(fn(b) b.int8).vector

// a 2x2 solid-red RGBA buffer (16 bytes) for the `FromPixels` async path (no
// decode -- straight to a texture): each pixel is R=255,G=0,B=0,A=255.
val demo-rgba : vector<int8> =
  [-1,0,0,-1, -1,0,0,-1, -1,0,0,-1, -1,0,0,-1].map(fn(b) b.int8).vector

// the async-image row (live tier): every source variant + a deliberately bad
// path, all `Async`. The valid FromPath carries a `min-load` so the scenario can
// observe the placeholder phase (no texture yet) before ready.
fun async-imgs( async-pic-src : string, ?key : key ) : <keytree,uistate,ioc> widget<msg>
  // keep the animation clock ticking while these load (Minor #1 test fix):
  // a real render-thread block during the off-thread decode would show up as
  // this clock STALLING -- `request-frame()` re-arms every render so the
  // live-tier test can observe `anim-time()` actually advancing across the
  // decode/min-load window, proving the render thread was not blocked.
  request-frame()
  row([
    // `async-pic-src` swaps this SAME-key ASYNC image's source (review
    // Important #1): the SwapAsyncPicSrc scenario emits it directly (like
    // SwapPicSrc does for the Sync "pic" above) to flip between two valid
    // PNGs at a fixed `?key` -- without the FIX, the async ready leaf always
    // draws the constant `async-image-src` marker so this never re-decodes.
    image-path(async-pic-src, load = Async, min-load = 150.milli-seconds,
               fit = Cover, width = 24.0, height = 24.0, ?key = scope("aimg-path")),
    image(FromBytes(demo-png-bytes), fit = Cover, width = 24.0, height = 24.0, ?key = scope("aimg-bytes")),
    image(FromPixels(demo-rgba, 2, 2), fit = Cover, width = 24.0, height = 24.0, ?key = scope("aimg-pixels")),
    image-path("assets/does-not-exist.png", load = Async,
               fit = Cover, width = 24.0, height = 24.0, ?key = scope("aimg-bad")),
  ], gap = 4.0, ?key = scope("aimg-row"))

// `lazy-column`'s `item` callback is closed to `<keytree,uistate,ioc>` (no
// `theme`) -- discharge `theme` locally in the closure, mirroring
// test/ui/lazy.kk's `themed-item`. `key` is the row's OWN identity
// (`idx(i)`, minted by `lazy-column` -- no per-row string): the leaf's
// owner IS that identity directly, selectable as `"lz-rows :i"`.
fun lz-item( i : int, key : key ) : <keytree,uistate,ioc> widget<msg>
  with val theme = dark
  text("lz " ++ i.show, 13.0, theme.fg, ?key = key)

pub fun themed-view( m : model, key : key ) : <keytree,uistate,scene<msg>,ioc,theme> widget<msg>
  val wk = field-key("what")   // resolve the field identity at build time
  // rows-key: minted ONCE (before the map) so every "lines" row is an
  // addressable `idx(i)` child of it ("lines-rows :0" etc) -- an EAGER
  // (non-lazy) scroll region, so nothing ever unmounts here; a row scrolled
  // fully past the viewport is still mounted, just clipped by `owner-rect`
  // (see `clipped-scenario`, distinct from `lazy-scenario`'s
  // virtualization-unmount case)
  val lines-rows-key = scope("lines-rows")
  column([
    field(name = "what", placeholder = "what?", on-enter = Just(fn(v : string) Add(v))),
    act-msg(box(text("Add", 13.0, theme.fg), padding = 6.0), fn() Add(field-text(wk)), ?key = scope("add")),
    primary-button("Bump", Bump, ?key = scope("bump")),
    text("clicks: " ++ m.clicks.show, 13.0, theme.fg, ?key = scope("count")),
    // `text-input` (like every id-bearing widget) stamps its OWN owner from
    // the ambient `?key`, so a scope names it directly -- no wrapper needed.
    text-input(m.note, fn(v) SetNote(v), placeholder = "note", ?key = scope("note")),
    text("note: " ++ m.note, 13.0, theme.fg, ?key = scope("echo")),
    column(m.items.map(fn(i) text(i, 13.0, theme.fg)), gap = 2.0, ?key = scope("list")),
    expanded(scroll(column(list(1, 40).map(fn(i) text("line " ++ i.show, 13.0, theme.fg, ?key = idx(i, ?key = lines-rows-key))), gap = 2.0), name = "lines")),
    // appended BELOW the existing regions so the "lines" region's hit-test
    // coordinates (relied on by the scroll scenario) are undisturbed
    expanded(lazy-column(lz-item, count = Just(200), item-extent = 20.0, name = "lz", ?key = scope("lz-rows"))),
  ]
  // appended LAST so they cannot perturb any earlier region's layout/coords
  // (mirrors the lz-rows comment above). The image asserts that `image` lays
  // out to a findable box (headless) AND, on the native tier, that its GPU
  // texture is identity-cached and released when unmounted -- `toggle-pic`
  // flips `show-pic` so the retention scenario can mount/unmount it.
  // `pic-src` swaps the DECODED SOURCE at this SAME stable `?key` (a
  // carousel/detail-swap shape): the retention scenario emits `SwapPicSrc`
  // directly (`t.emit`, no widget) to flip it between two valid PNGs without
  // unmounting, so it can pin that the native image cache re-decodes on a
  // src change instead of keeping the first texture forever (review
  // Important #1) -- a THIRD button here would grow the column past this
  // fixed headless viewport and break the "lines"/"lz" expanded scroll
  // regions below it, so this is intentionally NOT a clickable widget.
  ++ (if m.show-pic then [image-path(m.pic-src, load = Sync, fit = Cover, width = 48.0, height = 32.0, ?key = scope("pic"))] else [])
  ++ [ act-msg(box(text("toggle pic", 13.0, theme.fg), padding = 6.0), fn() TogglePic, ?key = scope("toggle-pic")) ]
  // live-tier async images (task #53): mounted only when the async scenario
  // asks (keeps the fixed-viewport scroll regions above undisturbed otherwise)
  ++ (if m.show-async then [async-imgs(m.async-pic-src)] else []),
  gap = 8.0)

pub fun view( m : model, key : key ) : <keytree,uistate,scene<msg>,ioc> widget<msg>
  with val theme = dark
  box( themed-view(m, key), padding = 12.0 )

pub fun update( m : model, msg : msg ) : dispatch<msg> model
  match msg
    Add(what) -> m(items = m.items ++ [what])
    Bump -> m(clicks = m.clicks + 1)
    SetNote(v) -> m(note = v)
    TogglePic -> m(show-pic = !m.show-pic)
    SwapPicSrc -> m(pic-src = if m.pic-src == "assets/x.png" then "assets/y.png" else "assets/x.png")
    ShowAsync -> m(show-async = !m.show-async)
    SwapAsyncPicSrc -> m(async-pic-src = if m.async-pic-src == "assets/x.png" then "assets/y.png" else "assets/x.png")

// ONE set of scenarios, three tiers: test-app/test-scenarios (headless),
// live-scenarios (real impeller window), and the web live page -- same
// tester API, same assertions.
pub fun clicks-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  check-eq("starts empty", t.texts("list"), [])
  t.click("bump")
  t.click("bump")
  t.settle()
  check-eq("clicks counted", t.texts("count"), ["clicks: 2"])
  check("field rect exists", t.find("what").is-just)

pub fun typing-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  t.type-text("what", "buy milk")
  t.settle()
  t.click("add")
  t.settle()
  check-eq("todo appears", t.texts("list"), ["buy milk"])
  // CONTROLLED input: the value round-trips through the model per keystroke;
  // a burst must not lose edits to the stale last-rendered tree (the LInput
  // accumulator fix -- the live tiers are what can catch this)
  t.type-text("note", "abcdef")
  t.settle()
  check-eq("controlled input keeps a burst", t.texts("echo"), ["note: abcdef"])
  // #51: a RAW id-bearing widget (text-input) is addressable by a caller's
  // scope with NO wrapper -- `t.find("note")` resolving proves its owner is
  // the "note" scope, not its internal Slot state-key. (type-text above
  // already clicked it via the selector; this pins find directly.)
  check("raw text-input addressable by scope (no wrapper)", t.find("note").is-just)

pub fun keys-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  t.type-text("what", "eggs")
  t.type-text("what", "s")     // "eggss"
  t.settle()
  t.press-key("Backspace")     // -> "eggs"
  t.settle()
  t.press-key("Enter")         // on-enter commits the field value
  t.settle()
  check-eq("enter commits the edited value", t.texts("list"), ["eggs"])

pub fun scroll-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  t.hover("bump")
  t.settle()
  t.scroll("lines", -120.0)    // wheel down: reveal later lines
  t.settle()
  check("scroll offset moved", list-scrolls().any(fn(kv) kv.snd.offset > 0.0))

// pins the FULLY-CLIPPED-NOT-FOUND side of `owner-rect`'s scroll clip
// (lib/ui/widget.kk's owner-rect/owner-rect-list): distinct from
// `lazy-scenario`'s virtualization-unmount case, "lines" is an EAGER
// (non-lazy) scroll region -- every row stays MOUNTED the whole time, so a
// "not found" reading here can only come from the geometric clip, not from
// a row being pruned out of the tree.
pub fun clipped-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  t.settle()
  // `list(1, 40)` is 1-BASED (first row is `i = 1`, not 0)
  check-eq("row 1 visible before scroll", t.texts("lines-rows :1"), ["line 1"])
  check("row 1 has a rect before scroll", t.find("lines-rows :1").is-just)
  t.scroll("lines", -4000.0)   // wheel DOWN by a lot: content pinned at its max offset
  t.settle()
  // row 1 is still MOUNTED (eager region, no virtualization -- `owner-texts`,
  // which only checks presence in the tree, still finds it) but its RECT is
  // now entirely above the viewport top: `owner-rect`'s clip intersection is
  // empty, so `find` reads Nothing -- the geometric clip, not an unmount
  check-eq("row 1 still mounted (present) once fully scrolled past", t.texts("lines-rows :1"), ["line 1"])
  check("row 1 rect gone (clipped) once fully scrolled past", t.find("lines-rows :1").is-nothing)

pub fun lazy-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  t.settle()
  check("first rows materialize", t.texts("lz-rows :0").length == 1 && t.texts("lz-rows :150").is-nil)
  t.scroll("lz", -1200.0)   // wheel down: 1200/20 = 60 rows
  t.settle()
  t.settle()
  // viewport size differs per tier, so assert on presence/absence rather
  // than an exact window edge: row 60 (well within the new window on any
  // reasonable viewport) is present, row 0 (scrolled well out) is gone
  check("window moved", t.texts("lz-rows :60").length == 1 && t.texts("lz-rows :0").is-nil)

// `image` lays out to a box BEFORE its pixels decode (web fetches, native's
// task-5 texture path hasn't landed yet) -- this pins layout/lowering only;
// the retention assert (an unmounted image drops its cache entry) lands in
// task 5 once there IS a cache.
pub fun image-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  t.settle()
  check("image lays out to a box", t.find("pic").is-just)

// scenarios shared by every tier: web scrolling is koka-owned now (the
// wheel listener drives the same bake/apply core as native), so scroll
// runs everywhere just like the rest
pub val shared-scenarios = [
  ("clicks", clicks-scenario),
  ("typing", typing-scenario),
  ("keys", keys-scenario),
  ("scroll", scroll-scenario),
  ("clipped", clipped-scenario),
  ("lazy", lazy-scenario),
  ("image", image-scenario),
]

pub fun main()
  test-scenarios("basic interactions", Model(), view, update,
                 shared-scenarios)
