// Reference: paint & effects.
module pages/reference-paint

import ui/keytrie   // ?key implicits (text/link now key their leaves)
import ui/widget
import ui/style/default
import ui/transform
import blocks

pub fun ref-paint-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ api-entry("fill, paint-source", ["Fill(color, radius = 0.0, source = Nothing)",
                                      "SLinear(fx, fy, tx, ty, from-color, to-color)",
                                      "SRadial(cx, cy, radius, inner-color, outer-color)",
                                      "SImage(src, fit = Cover)"],
      "`Fill` is a surface fill: a solid `color` (the fallback), rounded by "
      ++ "`radius`, optionally overridden by a `source` — a gradient or an "
      ++ "image, native on both backends (an Impeller ColorSource, a CSS "
      ++ "background), never emulated. Every source's geometry is a "
      ++ "FRACTION of the box being filled — (0,0) top-left, (1,1) bottom-"
      ++ "right — so one source describes a small swatch and a full-bleed "
      ++ "header without knowing either's size.",
      demo = Just(demo-panel(
        ["rect(70.0, 40.0,",
         "  bg = Just(Fill(theme.accent, 6.0,",
         "    source = Just(SLinear(",
         "      0.0, 0.0, 1.0, 1.0,",
         "      theme.accent, theme.surface)))))",
         "rect(70.0, 40.0,",
         "  bg = Just(Fill(theme.accent, 6.0,",
         "    source = Just(SRadial(",
         "      0.5, 0.5, 0.5,",
         "      theme.accent, theme.surface)))))"],
        fixed(row([
          rect(70.0, 40.0, bg = Just(Fill(theme.accent, 6.0,
                 source = Just(SLinear(0.0, 0.0, 1.0, 1.0, theme.accent, theme.surface))))),
          rect(70.0, 40.0, bg = Just(Fill(theme.accent, 6.0,
                 source = Just(SRadial(0.5, 0.5, 0.5, theme.accent, theme.surface))))),
        ], gap = 8.0), width = Just(90.0))))),

    api-entry("color: rgb, mix, brighten, contrasting", ["rgb(r, g, b)   // 0.0..1.0 each",
                                                           "color/mix(x, y, t)",
                                                           "brighten(c, factor)",
                                                           "color/contrasting(c)"],
      "`rgb` builds a color from 0.0-1.0 channels. `mix` blends two colors "
      ++ "by fraction `t` — the theme crossfade this site's own light/dark "
      ++ "toggle uses. `brighten` multiplies channels by `factor` (clamped) "
      ++ "— the native hover/press affordance, mirroring CSS "
      ++ "`filter: brightness(...)`; `primary-button`/`quiet-button` "
      ++ "(interaction reference) use it for their press glow. "
      ++ "`contrasting` picks a readable foreground (near-black or near-"
      ++ "white) for an arbitrary background — `primary-button`/"
      ++ "`quiet-button`'s ripple (interaction reference) uses it to tint "
      ++ "the press splash so it reads against whatever accent color the "
      ++ "theme has.",
      demo = Just(demo-panel(
        ["rect(50.0, 30.0, bg = Just(Fill(brighten(theme.accent, 1.3))))"],
        rect(50.0, 30.0, bg = Just(Fill(brighten(theme.accent, 1.3))))))),

    api-entry("rotated", ["rotated(child, degrees)"],
      "Rotates `child`'s PAINT only, about its center — layout is "
      ++ "unchanged (the child keeps its laid-out rect, same as `clip`). "
      ++ "For a fixed decorative tilt; for something that turns in "
      ++ "response to interaction (a flip card, a spinner keyed to "
      ++ "progress), reach for `transform3d` below instead.",
      demo = Just(demo-panel(
        ["rotated(",
         "  rect(50.0, 30.0,",
         "       bg = Just(Fill(theme.accent, 4.0))),",
         "  15.0)"],
        fixed(rotated(rect(50.0, 30.0, bg = Just(Fill(theme.accent, 4.0))), 15.0), width = Just(70.0))))),

    api-entry("transform3d", ["transform3d(child, m : mat4)"],
      "Applies a 4x4 matrix (`ui/transform`: `perspective`, `rotate-x`/"
      ++ "`-y`/`-z`, `translate3`, `scale3`, composed with `*`) to `child`'s "
      ++ "PAINT only, about its center — layout stays unchanged, like "
      ++ "`rotated` above but in 3D and composable. Hit-testing is "
      ++ "ACCURATE through the transform: a card tilted or flipped "
      ++ "hit-tests against its actual on-screen (projected) shape, not "
      ++ "its flat untransformed rect — this is the primitive a flip-card "
      ++ "or a tilt-on-hover effect is built from. Below, a fixed tilt "
      ++ "(no press/hover state needed for that part); driving the angle "
      ++ "from a click, like a real flip card, needs an app message this "
      ++ "page doesn't have — `samples/ui/gallery`'s flip-card does "
      ++ "exactly that, animating `angle` between 0 and pi on click.",
      demo = Just(demo-panel(
        ["transform3d(",
         "  rect(60.0, 36.0,",
         "       bg = Just(Fill(theme.accent, 4.0))),",
         "  perspective(800.0) * rotate-y(0.6))"],
        fixed(transform3d(
          rect(60.0, 36.0, bg = Just(Fill(theme.accent, 4.0))),
          perspective(800.0) * rotate-y(0.6)), width = Just(80.0))))),

    api-entry("ripple", ["ripple(content, pressed, radius = 6.0, tint = rgb(1.0, 1.0, 1.0),",
                          "       strength = 0.12, max-radius = 220.0)"],
      "A press ripple — a circle that grows from the press point and "
      ++ "fades, clipped to `content`'s bounds. `pressed` is the live "
      ++ "press state `interactive` (interaction reference) provides to "
      ++ "its `build` callback; the radius derives from the press "
      ++ "timestamp, not an eased cell, so consecutive presses each start "
      ++ "fresh from their own touch point instead of continuing from "
      ++ "wherever the last one ended. `primary-button`/`quiet-button` "
      ++ "(interaction reference) wrap every themed button in this. No "
      ++ "live demo here: like `interactive` (which `ripple` is normally "
      ++ "used inside), driving `ripple`'s `pressed` param from a real "
      ++ "press state needs an `interactive` wrapper, which itself needs "
      ++ "`on-click : msg` — an app message this page doesn't have (the "
      ++ "same constraint the `primary-button`/`quiet-button` entry on "
      ++ "the interaction reference explains). Click the Light/Dark "
      ++ "toggle in this page's own header for it in action — that's a "
      ++ "real `quiet-button`.",
      demo = Nothing) ]
