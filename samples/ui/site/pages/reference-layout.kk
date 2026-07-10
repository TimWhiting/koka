// Reference: layout & containers.
module pages/reference-layout

import ui/keytrie   // ?key implicits (text/link now key their leaves)
import ui/widget
import ui/style/default
import blocks

pub fun ref-boxes-flex-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ api-entry("box", ["box(child, padding = 0.0, bg = Nothing, on-click = Nothing)"],
      "A single child on a padded surface. `padding` adds space around the "
      ++ "child; `bg` fills the box (pass Nothing for no background at "
      ++ "all, which is what most layout-only boxes want). Reach for `box` "
      ++ "when you need padding or a background around one thing; reach "
      ++ "for `row`/`column` once you have more than one child. `box` also "
      ++ "carries every click/drag handler a widget can take — "
      ++ "`on-click`, `on-click-at` (with position), `on-context-at` "
      ++ "(right-click), `drag`/`on-drop` — see the interaction reference "
      ++ "for the drag-and-drop pattern built on the last two.",
      demo = Just(demo-panel(
        ["box(text(\"padded\", 14.0, theme.fg), padding = 12.0,",
         "    bg = Just(Fill(theme.surface, 8.0)))"],
        fixed(box(text("padded", 14.0, theme.fg), padding = 12.0,
                   bg = Just(Fill(theme.surface, 8.0))), width = Just(160.0))))),

    api-entry("row, column, spacer", ["row([..], gap = 10.0, fill = False)",
                                       "column([..], gap = 12.0, fill = False)",
                                       "spacer()"],
      "Lay children out horizontally (`row`) or vertically (`column`); "
      ++ "`gap` is the space between siblings. Put a `spacer()` anywhere "
      ++ "in the children list and it greedily takes whatever room is "
      ++ "left, which is how you push one child to the far edge without "
      ++ "computing widths yourself.",
      demo = Just(demo-panel(
        ["row([text(\"left\", 14.0, theme.fg), spacer(),",
         "     text(\"right\", 14.0, theme.fg)], gap = 8.0)"],
        fixed(row([text("left", 14.0, theme.fg), spacer(),
                    text("right", 14.0, theme.fg)], gap = 8.0), width = Just(110.0))))),

    api-entry("stack", ["stack([(x, y, child), ..])"],
      "Children at absolute (x, y) offsets within the space the parent "
      ++ "gives the stack — for overlapping content (a badge on a corner, "
      ++ "a label over an image) that `row`/`column` can't express, since "
      ++ "those only place children next to each other.",
      demo = Just(demo-panel(
        ["stack([",
         "  (0.0, 0.0,",
         "   rect(80.0, 40.0,",
         "        bg = Just(Fill(theme.surface, 6.0)))),",
         "  (10.0, 10.0,",
         "   text(\"on top\", 13.0, theme.fg)),",
         "])"],
        fixed(stack([
          (0.0, 0.0, rect(80.0, 40.0, bg = Just(Fill(theme.surface, 6.0)))),
          (10.0, 10.0, text("on top", 13.0, theme.fg)),
        ]), width = Just(80.0))))) ]

pub fun ref-scroll-space-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ api-entry("scroll", ["scroll(child, name = \"\", horizontal = False)"],
      "Makes `child` scrollable along one axis once it's bigger than the "
      ++ "space `scroll` is given — pair it with `expanded` in a fixed-"
      ++ "height parent (see `expanded` below), or the scroll region "
      ++ "shrink-wraps to its content instead of clipping. `name` lets a "
      ++ "sibling read or set the scroll offset (`scroll-state`, "
      ++ "`scroll-to` — state & animation reference). Pinned to a 70px "
      ++ "box below, five rows overflow it, so it pans instead of "
      ++ "clipping — every code block on this site uses the same "
      ++ "primitive, `scroll(..., horizontal = True)`.",
      demo = Just(demo-panel(
        ["fixed(",
         "  scroll(column([",
         "    rect(80.0, 28.0, bg = ...),",
         "    rect(80.0, 28.0, bg = ...),",
         "    rect(80.0, 28.0, bg = ...),",
         "    rect(80.0, 28.0, bg = ...),",
         "    rect(80.0, 28.0, bg = ...),",
         "  ], gap = 4.0)),",
         "  width = Just(88.0), height = Just(70.0))"],
        fixed(
          scroll(column([
            rect(80.0, 28.0, bg = Just(Fill(theme.accent, 4.0))),
            rect(80.0, 28.0, bg = Just(Fill(theme.surface, 4.0))),
            rect(80.0, 28.0, bg = Just(Fill(theme.accent, 4.0))),
            rect(80.0, 28.0, bg = Just(Fill(theme.surface, 4.0))),
            rect(80.0, 28.0, bg = Just(Fill(theme.accent, 4.0))),
          ], gap = 4.0)),
          width = Just(88.0), height = Just(70.0))))),

    api-entry("expanded", ["expanded(child, flex = 1.0)"],
      "Inside a row or column, grows `child` to fill whatever main-axis "
      ++ "space is left after the rigid (non-expanded) siblings are "
      ++ "sized — see the layout how-to guide for the header-plus-"
      ++ "scrolling-body pattern this enables. `flex` splits leftover "
      ++ "space between multiple `expanded` siblings by weight. You're "
      ++ "looking at it right now: this site's own shell wraps every "
      ++ "page's content in `expanded(scroll(...))` beneath a fixed-"
      ++ "height header.",
      demo = Just(code-block(["expanded( scroll( box(page-body, padding = 8.0) ) )"]))),

    api-entry("center", ["center(child, max-width = 640.0)"],
      "Centers `child` horizontally, capping its width at `max-width` — "
      ++ "the app-shell idiom for keeping content readable on a wide "
      ++ "window without hand-computing margins. `center` only centers "
      ++ "when its OWN parent stretches it to a width wider than "
      ++ "`max-width` — a bare `fixed` never does that (fixed caps, it "
      ++ "never stretches), so `expanded` inside a `row` is what gives "
      ++ "`center` real room to center within, below; this site's own "
      ++ "page shell uses the same `expanded`-stretches-`center` idiom "
      ++ "at a bigger scale.",
      demo = Just(demo-panel(
        ["fixed(row([",
         "  expanded(center(",
         "    box(text(\"centered\", 13.0, theme.fg),",
         "        padding = 8.0, bg = ...),",
         "    max-width = 70.0)),",
         "]), width = Just(200.0))"],
        fixed(row([
          expanded(center(
            box(text("centered", 13.0, theme.fg), padding = 8.0,
                bg = Just(Fill(theme.surface, 6.0))),
            max-width = 70.0)),
        ]), width = Just(200.0))))),

    api-entry("fixed", ["fixed(child, width = Nothing, height = Nothing)"],
      "Pins `child`'s extent on the given axes: capped at the given size "
      ++ "(the child may measure smaller; it's never stretched), but "
      ++ "`fixed` always REPORTS exactly that size to its parent no "
      ++ "matter what the child actually measured. Every `fixed`-wrapped "
      ++ "demo on this site's reference pages uses it for exactly this: "
      ++ "pinning a small demo to a tidy width regardless of its "
      ++ "content's natural size.",
      demo = Just(demo-panel(
        ["fixed(text(\"clipped if too wide\", 14.0, theme.fg),",
         "      width = Just(90.0))"],
        fixed(text("clipped if too wide", 14.0, theme.fg), width = Just(90.0))))),

    api-entry("intrinsic-width", ["intrinsic-width(child)"],
      "Measures `child` at its own natural width first, then lays it out "
      ++ "tight at that measured size — Flutter's IntrinsicWidth. Costs a "
      ++ "second layout pass, so it's for the cases that need it, not a "
      ++ "default. `demo-panel` (the code-beside-live-demo block every "
      ++ "reference page uses) wraps its code half in this: without it, "
      ++ "a horizontal `scroll` claims the FULL width its row parent "
      ++ "offers instead of shrinking to its own content, which used to "
      ++ "push every demo's live half off the page — see "
      ++ "test/ui/intrinsic-scroll-row.kk for the mechanism this fixed.",
      demo = Nothing) ]

pub fun ref-clip-overlay-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ api-entry("clip", ["clip(child, radius = 0.0, width = Nothing, height = Nothing)"],
      "Clips `child`'s paint to a rounded rect — `radius` rounds the "
      ++ "corners, `width`/`height` (if given) cap the clip region's size "
      ++ "independent of the child's own layout size. Use it when a "
      ++ "child's content (an image, a long block of text) might paint "
      ++ "past a boundary you want to enforce; `fixed` (above) caps "
      ++ "LAYOUT size and lets an oversize child overflow visually — "
      ++ "`clip` caps PAINT and cuts the overflow off instead.",
      demo = Just(demo-panel(
        ["clip(text(\"clipped, not shrunk\", 14.0, theme.fg),",
         "     width = Just(70.0), height = Just(20.0))"],
        clip(text("clipped, not shrunk", 14.0, theme.fg),
             width = Just(70.0), height = Just(20.0))))),

    api-entry("overlay", ["overlay(child)"],
      "Lays `child` out UNBOUNDED but reports zero size upward — for "
      ++ "content a `positioned` layer (below) will place independently "
      ++ "of normal flow, so its presence in a row/column doesn't shift "
      ++ "its siblings. `overlay` and `positioned` are usually paired: "
      ++ "`overlay` opts a subtree out of layout, `positioned` decides "
      ++ "where it actually paints.",
      demo = Nothing),

    api-entry("positioned", ["positioned(child, target = Nothing, target-align = top-left,",
                              "           self-align = top-left, offset-x = 0.0, offset-y = 0.0)"],
      "A full-viewport layer holding `child`, anchored to a target rect: "
      ++ "`child`'s `self-align` point is placed at the target's "
      ++ "`target-align` point (plus the offset), clamped on-screen. "
      ++ "`target = Nothing` anchors to the viewport itself (cursor "
      ++ "overlays, centered modals); a `Just` rect anchors to a specific "
      ++ "region. This is the primitive a tooltip, dropdown, or context "
      ++ "menu is built from — `ui/style/default` ships ready-made "
      ++ "`dropdown`/`context-menu` widgets that wrap `positioned` so you "
      ++ "don't call it directly for the common cases.",
      demo = Nothing) ]

pub fun ref-lazy-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ api-entry("lazy-column", ["lazy-column(item, count = Nothing, item-extent = 40.0,",
                               "            cache = 4, name = \"\")"],
      "A scrolling list that only builds the rows near the viewport "
      ++ "instead of every row up front — `item(i, key)` builds row `i`; "
      ++ "`item-extent` is each row's fixed height (rows must be a "
      ++ "uniform, known height for the windowing math); `cache` is how "
      ++ "many extra rows to keep built just outside the viewport, "
      ++ "trading memory for smoother fast-scroll. Reach for it once a "
      ++ "plain `column` inside a `scroll` would build thousands of rows "
      ++ "at once; for a list of a few dozen items, a `column` is "
      ++ "simpler and the windowing isn't worth it. No live demo here — "
      ++ "a list long enough to show windowing behavior needs more "
      ++ "vertical room than this compact reference format has: think a "
      ++ "scrolling grid with thousands of items, only the visible rows "
      ++ "ever built.",
      demo = Nothing) ]
