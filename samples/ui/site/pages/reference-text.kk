// Reference: text & content.
module pages/reference-text

import ui/keytrie   // ?key implicits (text/link now key their leaves)
import ui/widget
import ui/style/default
import ui/async
import blocks

pub fun ref-text-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ api-entry("text", ["text(content, size, color)   // single line"],
      "Draws a single line of text; it does not wrap, and does not shrink "
      ++ "to fit — a string wider than its parent clips. Use "
      ++ "`text` for labels and short strings that should never wrap; use "
      ++ "`paragraph` for anything that might need more than one line.",
      demo = Just(demo-panel(["text(\"Hello\", 16.0, theme.fg)"],
                              text("Hello", 16.0, theme.fg)))),

    api-entry("paragraph", ["paragraph(content, size, color)  // wraps"],
      "Wraps text to the width its parent gives it, breaking at word "
      ++ "boundaries. Every paragraph of prose on this page — this "
      ++ "sentence included — is a `paragraph` widget."),

    api-entry("code", ["code(content, size)   // monospace"],
      "Text set in the mono font, sized for source lines rather than "
      ++ "prose. `code-block` (the layout reference's `Boxes and flex` "
      ++ "section describes its container) is a column of `code` widgets "
      ++ "on a panel background — every code sample on this page is "
      ++ "built from it."),

    api-entry("fonts: sans, serif, mono, bold, font",
      ["sans(size = 15.0)   // system sans, the default",
       "serif(size = 15.0)",
       "mono(size = 14.0)",
       "bold(f)             // weight 700 of an existing font",
       "font(family, size = 15.0, weight = 400, italic = False)"],
      "`text`/`paragraph` take either a plain `size : float64` (system "
      ++ "sans at that size — the common case, used throughout this "
      ++ "site) or a `font` value from one of these for anything else. "
      ++ "`bold` wraps an existing font rather than being its own family "
      ++ "— `bold(sans(16.0))`, not a separate bold-sans constructor. "
      ++ "Reach for `font` directly only for a family/weight/italic "
      ++ "combination none of `sans`/`serif`/`mono`/`bold` already "
      ++ "gives you.",
      demo = Just(demo-panel(
        ["text(\"bold serif\", bold(serif(16.0)), theme.fg)"],
        text("bold serif", bold(serif(16.0)), theme.fg)))),

    api-entry("rect", ["rect(w, h, bg = Nothing, on-click = Nothing)"],
      "A fixed-size, optionally clickable colored box — grid cells, "
      ++ "swatches, placeholders. The `stack` demo on the layout reference "
      ++ "page's colored rectangle is a `rect`, for instance. Unlike `box`, "
      ++ "`rect` has no child — reach for `box` the moment you need to put "
      ++ "something inside it.",
      demo = Just(demo-panel(
        ["rect(60.0, 30.0, bg = Just(Fill(theme.accent, 6.0)))"],
        rect(60.0, 30.0, bg = Just(Fill(theme.accent, 6.0)))))),

    api-entry("image, image-path", ["image-path(src, fit = Contain, load = Async,",
                                     "           placeholder = default-placeholder(),",
                                     "           min-load = zero, width = 0.0, height = 0.0)"],
      "Loads and paints an image. `image-path(src, ...)` is the common "
      ++ "case (a plain asset path or URL); `image(source, ...)` takes an "
      ++ "explicit `image-source` (`FromPath`/`FromBytes`/`FromPixels`) "
      ++ "when the bytes don't come from a simple path. `fit` (`Cover` "
      ++ "crops to fill, `Contain` letterboxes) matters once the image's "
      ++ "own aspect ratio doesn't match the box you give it; `load = "
      ++ "Async` (the default) decodes off the async pump and shows "
      ++ "`placeholder` until it's ready — `min-load` holds the "
      ++ "placeholder at least that long even if the decode finishes "
      ++ "sooner, so a fast local load doesn't flash. `load = Sync` "
      ++ "applies to `FromPath` only and decodes inline on first paint "
      ++ "instead, on either backend — no placeholder, no `min-load`. "
      ++ "The two backends differ in what that costs: native's Sync "
      ++ "decode runs on the render thread and blocks that frame; the "
      ++ "web backend hands the same `FromPath` off to a plain `<img "
      ++ "src>`, whose decode doesn't block JS the same way.",
      demo = Just(demo-panel(
        ["image-path(\"assets/mars.jpg\", fit = Cover,",
         "           width = 120.0, height = 80.0)"],
        image-path("assets/mars.jpg", fit = Cover, width = 120.0, height = 80.0)))) ]
