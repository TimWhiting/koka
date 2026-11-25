// Reference: interaction.
module pages/reference-interaction

import ui/keytrie   // ?key implicits (text/link now key their leaves)
import ui/widget
import ui/style/default
import blocks
import pages/common

pub fun ref-interactive-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ api-entry("primary-button, quiet-button", ["primary-button(label, on-click : msg, size = 15.0)",
                                                "quiet-button(label, on-click : msg, size = 15.0)"],
      "Themed, click-animated buttons: `primary-button` is filled with the "
      ++ "accent color for the main action on a screen; `quiet-button` "
      ++ "sits on the surface color for secondary actions. Both take an "
      ++ "app message (`on-click : msg`), which this page — like every "
      ++ "reference entry — is written without, so it can't embed the "
      ++ "real widgets live. The demo below shows the click target itself, "
      ++ "via `act` — a plain click wrapper with no press/hover feedback "
      ++ "of its own (unlike `interactive`, below, which `primary-button` "
      ++ "and `quiet-button` are actually built on):",
      demo = Just(demo-panel(
        ["act(",
         "  box(text(\"Try me\", 16.0, on-accent),",
         "      padding = 9.0,",
         "      bg = Just(Fill(theme.accent, 6.0))),",
         "  on )"],
        demo-button("Try me", fn() (), here())))),

    api-entry("text-input", ["text-input(value, on-input : string -> msg, placeholder = \"\", width = 220.0)"],
      "A single-line editable field. `on-input` fires with the field's "
      ++ "current text on every keystroke, so the app model always holds "
      ++ "the live value (a CONTROLLED input, in React terms). No live "
      ++ "demo here: `on-input` needs an app message this page doesn't "
      ++ "have. See `field` (below) for an UNCONTROLLED alternative whose "
      ++ "value lives in ui/state instead of the model.",
      demo = Nothing),

    api-entry("slider", ["slider(value, on-change : float64 -> msg, lo = 0.0, hi = 1.0, step = 0.0)"],
      "A horizontal slider over `[lo, hi]`, snapped to `step` (0.0 means "
      ++ "no snapping). Like `text-input`, `on-change` needs an app "
      ++ "message this page doesn't have, so there's no live `slider` "
      ++ "demo — the mechanism is the same as `text-input`'s: the app "
      ++ "model holds the current value, `on-change` updates it, the "
      ++ "slider redraws at the new position next render.",
      demo = Nothing),

    api-entry("link", ["link(route-path, child)"],
      "Wraps `child` in a navigation target for `route-path` (no leading "
      ++ "'#') — a real `<a href=\"#/...\">` on the web (right-click, "
      ++ "open-in-new-tab, and deep-linking all work), a click target the "
      ++ "router handles the same way natively. `link` takes no message "
      ++ "of its own, which is why it — unlike the buttons above — can "
      ++ "appear directly on this message-agnostic reference page. The "
      ++ "sidebar you're using right now is built from it, and so is "
      ++ "this:",
      demo = Just(demo-panel(
        ["link(",
         "  \"howto-layout\",",
         "  accented(",
         "    \"Go to the layout how-to\", 15.0))"],
        link("howto-layout", accented("Go to the layout how-to", 15.0))))),

    api-entry("act", ["act(child, on-act : () -> <uistate,ioc> ())"],
      "A click target that runs a thunk instead of emitting an app "
      ++ "message — the door for `ui/state` writes (toggles, uncontrolled "
      ++ "field reads) that never touch the model. The \"Try me\" button "
      ++ "above is built from `act` wrapping a box, but its thunk there "
      ++ "is empty (that demo exists only to show press/click mechanics). "
      ++ "Below, `act` wraps EACH button and bumps a `use-state` counter "
      ++ "on click — this is `live-counter` itself (state & animation "
      ++ "reference), the exact code every live counter on this site "
      ++ "runs, not a simplified stand-in for it:",
      demo = Just(demo-panel(
        ["val (n, set) = use-state(0)",
         "box( row([",
         "  act(box(text(\"−\", 16.0, on-accent), padding = 9.0,",
         "          bg = Just(Fill(theme.accent, 6.0))),",
         "      fn() set(fn(x) x - 1)),",
         "  box(text(n.show, 26.0, theme.fg), padding = 6.0),",
         "  act(box(text(\"+\", 16.0, on-accent), padding = 9.0,",
         "          bg = Just(Fill(theme.accent, 6.0))),",
         "      fn() set(fn(x) x + 1)),",
         "], gap = 12.0), padding = 12.0, bg = ...)"],
        live-counter(here())))),

    api-entry("act-msg", ["act-msg(child, to-msg : () -> <uistate,ioc> msg)"],
      "Like `act`, but the thunk COMPUTES a message from `ui/state` at "
      ++ "click time instead of running a side-effecting write — the "
      ++ "form-submit primitive: read one or more `field`s, build one "
      ++ "message from what they hold. Use `act` when the click's only "
      ++ "job is an `ui/state` write; use `act-msg` when the click needs "
      ++ "to also tell the app model something.",
      demo = Nothing),

    api-entry("field", ["field(name = \"\", placeholder = \"\", width = 220.0,",
                         "      on-enter : maybe<string -> msg> = Nothing)"],
      "An UNCONTROLLED single-line text field: its value lives in "
      ++ "`ui/state`, not the app model, so typing in it causes no "
      ++ "re-render of anything that doesn't read it. Give it a `name` "
      ++ "and a sibling can read its live text with "
      ++ "`field-text(field-key(name))` — the pattern `act-msg`'s "
      ++ "form-submit button uses. `on-enter` optionally maps the Enter "
      ++ "key to a message, the one way a `field` CAN talk to the app "
      ++ "model directly without a submit button. Unlike `text-input`, "
      ++ "reading a `field` back needs no app message at all — "
      ++ "`field-text(field-key(...))` is a plain `ui/state` read, so "
      ++ "this page CAN show one live, typing into the field below "
      ++ "updates the text beside it on every keystroke:",
      demo = Just(demo-panel(
        ["field(name = \"demo-field\",",
         "      placeholder = \"Type here\")",
         "text(\"-> \" ++",
         "  field-text(field-key(\"demo-field\")),",
         "  14.0, theme.fg)"],
        row([
          field(name = "demo-field", placeholder = "Type here"),
          text("-> " ++ field-text(field-key("demo-field")), 14.0, theme.fg),
        ], gap = 8.0)))),

    api-entry("interactive, interaction", ["interactive(on-click : msg, build : (interaction) -> widget<msg>,",
                                            "            disabled = False, hit-slop = 0.0)"],
      "The primitive `primary-button`/`quiet-button` (and every other "
      ++ "themed clickable in `ui/style/default`) are built on: owns the "
      ++ "click, tracks hover/press/focus by widget identity, and calls "
      ++ "`build` with the LIVE `interaction` state (`hovered`, "
      ++ "`pressed`, `focused`, `disabled` — all `bool`) so your content "
      ++ "can change color, border, even structure on hover/press without "
      ++ "any of that touching the app model. `disabled` blocks the click "
      ++ "and is passed through to `build` so the content can gray "
      ++ "itself out. `hit-slop` widens the CLICKABLE area beyond the "
      ++ "visual one without changing layout — for a small icon that "
      ++ "needs a bigger touch target than it visually occupies. Reach "
      ++ "for `interactive` directly when you're building your own "
      ++ "themed component; reach for `primary-button`/`quiet-button` "
      ++ "when an existing one already does what you need.",
      demo = Nothing),

    api-entry("drag, on-drop (on box)", ["box(child, drag = Nothing, on-drop = Nothing)"],
      "Marks a box a drag SOURCE (`drag = Just(payload)`, an arbitrary string) or a drop "
      ++ "TARGET (`on-drop = Just(fn(payload) msg)`, called with the source's payload when "
      ++ "something is dropped on it) — or both, for a box that's draggable and also "
      ++ "accepts drops. This is the primitive the layout reference's `box` entry points "
      ++ "here from: the same handler bundle every `box` carries, just the two fields a "
      ++ "reorderable list or a drop zone actually uses. `on-click`/`on-click-at`/"
      ++ "`on-context-at` need an app message this page doesn't have, and drag/drop needs "
      ++ "an app message too (`on-drop`'s handler), so there's no live demo here.",
      demo = Nothing) ]
