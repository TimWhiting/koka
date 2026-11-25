// Reference: state & animation.
module pages/reference-state

import std/num/float64
import ui/keytrie   // ?key implicits (text/link now key their leaves)
import ui/widget
import ui/state
import ui/style/default
import blocks
import pages/common

// two buttons that set `set-time-dilation` to a different factor and THEN
// retarget the bar, so each click's animation plays at that factor -- a
// side-by-side comparison instead of a single toggle. `set-time-dilation`
// is a persistent global (lib/ui/state.kk), not scoped to this demo or
// even this page -- it stays at whatever factor was last set until
// changed again, including after navigating away, which is exactly why
// "Normal" is here as its own button rather than a one-shot "slow it
// down" toggle: clicking it is how you undo "Slow (4x)"'s effect on
// every OTHER animation on the site, not just this bar.
fun dilation-demo<a>( key : key ) : <keytree,uistate,ioc,theme> widget<a>
  val (target, set-target) = use-state(40)
  val w = animate(160.0 * target.float64 / 100.0, duration = 1000.0)
  box( column([
    stack([
      (0.0, 0.0, rect(160.0, 12.0, bg = Just(Fill(theme.bg, 6.0)))),
      (0.0, 0.0, rect(w, 12.0, bg = Just(Fill(theme.accent, 6.0)))),
    ]),
    row([
      demo-button("Normal", fn() { set-time-dilation(1.0); set-target(fn(x) if x == 40 then 90 else 40) }, here()),
      demo-button("Slow (4x)", fn() { set-time-dilation(4.0); set-target(fn(x) if x == 40 then 90 else 40) }, here()),
    ], gap = 8.0),
  ], gap = 10.0), padding = 12.0, bg = Just(Fill(theme.surface, 10.0)) )

// a small named scroll region plus Top/Bottom buttons driving
// `set-scroll-offset` directly, and a `scroll-state` read displayed live --
// `scroll-key` derives the SAME identity `scroll(name = ...)` mints, from
// a plain string, no shared state object to thread between them
fun scroll-state-demo<a>( key : key ) : <keytree,uistate,ioc,theme> widget<a>
  val k = scroll-key("state-demo")
  box( column([
    fixed(
      scroll(column([
        rect(70.0, 22.0, bg = Just(Fill(theme.accent, 4.0))),
        rect(70.0, 22.0, bg = Just(Fill(theme.surface, 4.0))),
        rect(70.0, 22.0, bg = Just(Fill(theme.accent, 4.0))),
        rect(70.0, 22.0, bg = Just(Fill(theme.surface, 4.0))),
        rect(70.0, 22.0, bg = Just(Fill(theme.accent, 4.0))),
      ], gap = 4.0), name = "state-demo"),
      width = Just(78.0), height = Just(60.0)),
    text("offset: " ++ scroll-state(k).offset.show, 12.0, theme.fg),
    row([
      demo-button("Top", fn() set-scroll-offset(k, 0.0), here()),
      demo-button("Bottom", fn() { val s = scroll-state(k); set-scroll-offset(k, s.content - s.viewport) }, here()),
    ], gap = 8.0),
  ], gap = 8.0), padding = 12.0, bg = Just(Fill(theme.surface, 10.0)) )

pub fun ref-state-anim-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ api-entry("use-state, use-state-quiet", ["use-state(init, name = \"\")   // (value, setter)",
                                              "use-state-quiet(init, name = \"\")"],
      "Ephemeral state keyed by call site — no app message, no model "
      ++ "field. `use-state` returns `(value, setter)`; calling the "
      ++ "setter re-renders. `use-state-quiet` is the same shape but its "
      ++ "write does NOT itself trigger a re-render — for state a caller "
      ++ "reads back on the NEXT frame anyway (like `animate`, below, "
      ++ "which retargets mid-build for the frame it's about to request), "
      ++ "where a normal `use-state` write would cause an "
      ++ "extra, identical echo render. Reach for plain `use-state` unless "
      ++ "you have that specific reason not to — every live counter on "
      ++ "this site (this one included) uses it.",
      demo = Just(demo-panel(
        ["val (n, set) = use-state(0)",
         "box(",
         "  row([",
         "    demo-button(\"−\",",
         "      fn() set(fn(x) x - 1), here()),",
         "    box(text(n.show, 26.0, theme.fg),",
         "        padding = 6.0),",
         "    demo-button(\"+\",",
         "      fn() set(fn(x) x + 1), here()),",
         "  ], gap = 12.0),",
         "  padding = 12.0,",
         "  bg = Just(Fill(theme.surface, 12.0)))"],
        live-counter(here())))),

    api-entry("animate, animate-color", ["animate(target, duration = 200.0, ease = ease-out)",
                                          "animate-color(target, duration = 200.0, ease = ease-out)"],
      "A value (or color) that MOVES: returns the current interpolated "
      ++ "position, easing toward `target` over `duration` ms. Retargeting "
      ++ "mid-flight continues from the CURRENT position — no jump, so a "
      ++ "hover-out that reverses direction mid-animation looks natural. "
      ++ "Keyed like `use-state`, so each call site animates "
      ++ "independently. While unsettled it requests frames; once "
      ++ "settled, it goes quiet and the app stops re-rendering entirely "
      ++ "— the bar in the Live sample below stops requesting frames the "
      ++ "moment it reaches its target.",
      demo = Nothing),

    api-entry("easings: ease-in, ease-out, ease-in-out", ["ease-in(t)   // t in [0,1], returns [0,1]",
                                                            "ease-out(t)",
                                                            "ease-in-out(t)"],
      "The `ease` parameter `animate`/`animate-color` take: a plain "
      ++ "`float64 -> float64` curve over the unit interval. `ease-out` "
      ++ "(the default) starts fast and settles gently — the natural "
      ++ "choice for something moving TO a resting state, which is most "
      ++ "UI motion.",
      demo = Nothing),

    api-entry("set-time-dilation", ["set-time-dilation(factor)"],
      "Slows every `animate`/`animate-color` on the page by `factor` — "
      ++ "`factor = 1.0` is real time, `factor = 4.0` is quarter speed "
      ++ "(delta time is divided by `factor`). Clamped to at least 1.0: "
      ++ "this can only slow animations, never speed them past real time — "
      ++ "a debug aid for watching a fast animation's easing curve rather "
      ++ "than a production feature. It's a plain `ioc` call, no app "
      ++ "message needed, so `act` can drive it directly — click either "
      ++ "button below, then the other, and compare how fast the bar "
      ++ "gets there:",
      demo = Just(demo-panel(
        ["val w = animate(target, duration = 1000.0)",
         "demo-button(\"Normal\",",
         "  fn() { set-time-dilation(1.0); ... }, here())",
         "demo-button(\"Slow (4x)\",",
         "  fn() { set-time-dilation(4.0); ... }, here())"],
        dilation-demo(here())))),

    api-entry("scroll-state, set-scroll-offset, scroll-to", ["scroll-state(k)   // -> scroll-info",
                                                               "set-scroll-offset(k, v)",
                                                               "scroll-to(selector)"],
      "Read or drive a `scroll` region's live offset/content/viewport "
      ++ "from OUTSIDE it — `k` is the same key `scroll(name = ...)` "
      ++ "mints (`scroll-key(name)` derives it from the name directly). "
      ++ "`scroll-to(selector)` is higher-level: it resolves a selector "
      ++ "to a mounted widget and scrolls its enclosing region so that "
      ++ "widget lands at the viewport top — the mechanism behind every "
      ++ "\"on this page\" link and cross-page anchor on this site, "
      ++ "including the ones in this page's own on-this-page rail above. "
      ++ "Below, the buttons drive `set-scroll-offset` directly (a "
      ++ "`scroll-to`-driven demo would need a real second target "
      ++ "elsewhere on the page to land on); the number is a live "
      ++ "`scroll-state` read.",
      demo = Just(demo-panel(
        ["fixed(scroll(column([...]),",
         "      name = \"state-demo\"),",
         "  width = Just(78.0), height = Just(60.0))",
         "\"offset: \" ++",
         "  scroll-state(scroll-key(\"state-demo\")).offset.show",
         "demo-button(\"Top\", fn()",
         "  set-scroll-offset(scroll-key(\"state-demo\"), 0.0), here())",
         "demo-button(\"Bottom\", fn()",
         "  set-scroll-offset(k, s.content - s.viewport), here())"],
        scroll-state-demo(here())))),

    api-entry("press-point", ["press-point()   // -> (x, y, timestamp)"],
      "The last press location within the CURRENT `interactive` region, "
      ++ "as an untracked ref (reading it doesn't itself trigger a "
      ++ "re-render — it rides on the press write's own invalidation). "
      ++ "`ripple` (paint & effects reference) is built on this: the "
      ++ "circle originates from the press point, not the widget's "
      ++ "center.",
      demo = Nothing),

    api-entry("memo", ["memo(build : (key) -> widget<msg>)"],
      "Establishes a memoization boundary at this call site: while "
      ++ "nothing the boundary's subtree READ has been written since last "
      ++ "render, `memo` returns the CACHED widget — the same pointer, so "
      ++ "reconcile skips relaying out the whole subtree via pointer "
      ++ "equality. Reads inside `build` auto-track; nothing to declare. "
      ++ "Reach for it around an expensive, rarely-changing subtree (a "
      ++ "long static list, a complex chart) once profiling shows re-"
      ++ "layout there costs something — it is not a default wrap-"
      ++ "everything primitive.",
      demo = Nothing),

    api-entry("Live sample: a value driving an animated bar", ["live-progress(key)"],
      "`use-state` holding the target value, `animate` easing the bar "
      ++ "toward it — the two primitives above this page opens with, "
      ++ "combined:",
      demo = Just(live-progress(here()))) ]
