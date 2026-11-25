// Reference: theming.
module pages/reference-theming

import ui/keytrie   // ?key implicits (expander's here() leaf)
import ui/widget
import ui/style/default
import blocks

pub fun ref-theming-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ api-entry("theme (the ambient effect)", ["effect val theme : palette",
                                              "theme/light, theme/dark : palette",
                                              "palette/mix(a, b, t)"],
      "Every themed component in this reference (and every one on this "
      ++ "site) reads colors from `theme` — an AMBIENT reader effect, not "
      ++ "a parameter threaded through every call. `light`/`dark` are the "
      ++ "two built-in palettes (`bg`/`fg`/`accent`/`surface`), qualified "
      ++ "as `theme/light`/`theme/dark` wherever a bare `light`/`dark` "
      ++ "would be ambiguous; `palette/mix` blends them by fraction `t`, "
      ++ "which is exactly how this site's own Light/Dark toggle works — "
      ++ "this page's own `view` animates a `t` and binds "
      ++ "`with val theme = theme/light.mix(theme/dark, t)` around the "
      ++ "whole page (verified: `samples/ui/site/main.kk`), so every "
      ++ "themed widget crossfades together instead of snapping.",
      demo = Just(demo-panel(
        ["rect(50.0, 30.0,",
         "  bg = Just(Fill(",
         "    theme/light.accent, 4.0)))",
         "rect(50.0, 30.0,",
         "  bg = Just(Fill(",
         "    theme/dark.accent, 4.0)))"],
        fixed(row([
          rect(50.0, 30.0, bg = Just(Fill(theme/light.accent, 4.0))),
          rect(50.0, 30.0, bg = Just(Fill(theme/dark.accent, 4.0))),
        ], gap = 8.0), width = Just(120.0))))),

    api-entry("page, card, body, accented", ["page(title, children, gap = 14.0, scroll = True)",
                                              "card(child, padding = 14.0)",
                                              "body(content, size = 15.0)",
                                              "accented(content, size = 15.0)"],
      "The structural/typography building blocks: `page` is a heading "
      ++ "over a scrolling column of content; `card` is a single child on "
      ++ "the theme's raised surface color; `body` is prose text that "
      ++ "WRAPS to the available width, in the theme's foreground color; "
      ++ "`accented` is a single-line label in the accent color (built on "
      ++ "`text`, not `paragraph` — it does NOT wrap, unlike `body`); this "
      ++ "site actually uses `accented` for its own prev/next links and "
      ++ "header title (`samples/ui/site/main.kk`, `blocks.kk`). This "
      ++ "site's own pages don't happen to reach for `page`/`card`/`body` "
      ++ "(they use `demo-panel`, `box`, and `prose` instead — different "
      ++ "helpers, same underlying widgets), but the samples ship real "
      ++ "call sites: "
      ++ "`samples/ui/counter/main.kk` builds its view around "
      ++ "`page(\"Koka × ui\", [card(column([counter, slow], gap = 16.0))])` "
      ++ "— a heading over one `card`; `samples/ui/gallery/main.kk` uses "
      ++ "`body(...)` repeatedly for its wrapping caption text above each "
      ++ "demo card (e.g. \"future-boundary: the general async primitive "
      ++ "`image` is built on.\").",
      demo = Just(demo-panel(
        ["card(",
         "  column([",
         "    body(\"Wrapping prose inside a card.\"),",
         "    accented(\"An accented label\", 13.0),",
         "  ], gap = 6.0))"],
        fixed(card(
          column([
            body("Wrapping prose inside a card."),
            accented("An accented label", 13.0),
          ], gap = 6.0)), width = Just(160.0))))),

    api-entry("expander", ["expander(title, body, key)"],
      "A collapsible section: clicking the header toggles `body` in or "
      ++ "out. Its open/closed state is ephemeral `ui/state` (state & "
      ++ "animation reference), keyed by the REQUIRED `key` parameter — "
      ++ "not `?key`, a plain positional `key` the caller must mint "
      ++ "(`expander(\"Files\", tree, here())`), so forgetting it is a "
      ++ "type error rather than a silent identity collision. Unlike "
      ++ "`dropdown`/`context-menu` below, `expander` takes no app "
      ++ "message at all — its toggle is pure `act`-style ephemeral "
      ++ "state — so it's the one component on this page that CAN "
      ++ "appear live:",
      demo = Just(demo-panel(
        ["expander(\"Details\",",
         "  text(\"the hidden content\", 14.0, theme.fg),",
         "  here())"],
        expander("Details", text("the hidden content", 14.0, theme.fg), here())))),

    api-entry("dropdown, context-menu", ["dropdown(label, items, on-open : msg)",
                                          "context-menu(items : list<(string, msg)>)"],
      "`context-menu` is a raised surface holding a column of "
      ++ "`(label, message)` rows, meant to be floated at a point with "
      ++ "`ui/view`'s `overlay` — a `scene` portal effect the app runtime "
      ++ "discharges (`ui/app` composes emitted views over the main "
      ++ "content via `with-scene`, so ordinary view code never wraps "
      ++ "itself), e.g. "
      ++ "`overlay(\"menu\", context-menu(items), offset-x = x, offset-y = y)` "
      ++ "(verified: `samples/ui/overlay/main.kk`); `dropdown` is just the TRIGGER button "
      ++ "for one — clicking it emits `on-open`, and the app responds by "
      ++ "floating a `context-menu` itself (the open/closed state is app "
      ++ "state, not something these components own). Both need an app "
      ++ "message this page doesn't have — same constraint the "
      ++ "interaction reference's `primary-button` entry explains. "
      ++ "Unlike `expander` above, there's no ephemeral-state escape "
      ++ "hatch here, since opening a menu is a real navigation the app "
      ++ "needs to know about.",
      demo = Nothing),

    api-entry("ui/style/material", [],
      "A second, sibling style library over the same style-agnostic "
      ++ "`ui/widget` core, NOT a call-compatible drop-in for "
      ++ "`ui/style/default`: it has its own separate `theme` effect "
      ++ "(over a `material-theme` record, not `palette`) and its own "
      ++ "button vocabulary (`filled-button`, `elevated-button`, "
      ++ "`filled-tonal-button`, `text-button` — Material 3's set, not "
      ++ "`primary-button`/`quiet-button`). Only Material's four button "
      ++ "variants are built from `button-style`/`styled-paint` (below) — "
      ++ "this library's own `primary-button`/`quiet-button` hand-roll "
      ++ "their fill directly from `ui/state`'s `interactive` instead, so "
      ++ "adopting `ui/style/material` means learning its own component "
      ++ "names, not swapping one import line. No live demo "
      ++ "here: showing both libraries side by side needs two "
      ++ "independent theme scopes this page doesn't have.",
      demo = Nothing),

    api-entry("button-style, styled-paint", ["button-style(bg, fg, hover, pressed,",
                                              "             radius = 20.0, padding = 12.0)",
                                              "styled-paint(style)"],
      "The custom-style escape hatch, for a button that doesn't fit "
      ++ "`primary-button`/`quiet-button`'s two built-in looks: "
      ++ "`button-style` is a plain data record (fill color at rest, "
      ++ "text color, and two more fills for hover/pressed); "
      ++ "`styled-paint(style)` turns that record into the paint "
      ++ "function `ui/style/base`'s raw `button` takes as its `paint` "
      ++ "argument, picking the right fill by the LIVE interaction "
      ++ "state — this is the mechanism `ui/style/material`'s own "
      ++ "buttons (above) are built from. No live demo here: needs "
      ++ "`interactive`, the same message constraint every "
      ++ "interactive-primitive entry on this site runs into.",
      demo = Nothing) ]
