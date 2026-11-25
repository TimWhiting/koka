# ui: a portable Koka UI framework (experimental)

One `view : model -> widget<msg>` runs on three backends: the browser
(`--target=wasi-web` and `--target=jsweb`) and native macOS
(`--target=libc`, rendered by Flutter's [Impeller](https://docs.flutter.dev/perf/impeller)
engine). The Elm architecture with Koka's own machinery in place of the
framework's — Flutter-shaped (Koka-native widgets, no web concepts leak into
the API), but with pure `widget<msg>` data and message-valued handlers.

```koka
import ui/widget
import ui/app

type msg { Inc; Dec }

fun view( count : int ) : widget<msg>
  row([ box(text("−"), padding=8.0, on-click=Just(Dec)),
        text(count.show, 32.0),
        box(text("+"), padding=8.0, on-click=Just(Inc)) ])

fun update( count : int, msg : msg ) : dispatch<msg> int
  match msg { Inc -> count + 1; Dec -> count - 1 }

pub fun main()
  app( 0, view, update )
```

## How it fits together

The **same layout pass** runs on every backend — that is the unification
point, not the renderer. `view` builds pure `widget<msg>` data; layout runs
Flutter-style (constraints flow down, sizes flow up, the parent positions
its children), producing a laid-out tree; then each backend realizes that
tree its own way:

- **web** (`ui/api/web`): the laid-out tree lowers to absolutely-positioned
  DOM (`position:absolute` divs; real `<input>`/`range` elements for
  TextInput/Slider). The browser paints; DOM listeners emit messages.
  html/vdom/dom from `lib/web-ui` are the internal machinery (value sync,
  keyed reconciliation, drag wiring, listener lifecycle, and — on wasi-web —
  the Perceus externref table). Text is measured by the host canvas.
- **native** (`ui/api/impeller`): the laid-out tree paints to one Impeller
  display list per frame; a GLFW window presents it. Input is polled by a
  `pump` strand and hit-tested against the tree. Text is measured (and drawn)
  by Impeller's typography engine.

The backend is selected per host exactly like `std/async`'s event loop
(`ui/backend.kk`). The **app loop is identical everywhere** (`ui/app.kk`):
one message channel, `dispatch`/`spawn` for async (the loop, the platform
input pump, subscriptions, and spawned tasks are all strands of one
`forking` interleaving), so `spawn` works natively via `std/async`'s libuv
host — no per-backend loop.

## Files

| file | what |
|---|---|
| `widget.kk` | the portable, **style-agnostic** vocabulary + `color`/`fill` + `font` + the `measure` effect + the shared layout and hit-testing |
| `router.kk` | hash routing: `parse`/`print`, `route-sub`, `navigate`, `link` sugar |
| `nav.kk` | host-selected hash façade (web `location.hash`; native in-memory) |
| `style/default/` | the **default style library** (one swappable layer): `theme` (palette + `effect val theme`), `components` (`button` + `primary-button`/`quiet-button`/`card`/`page`/`body`/`accented`), `system` (`system-dark`) |
| `app.kk` | the Elm loop: channel, `dispatch`/`spawn`, `map-dispatch`, `every`, subs |
| `backend.kk` | per-host selector of the platform backend |
| `api/web/backend.kk` | widget → absolutely-positioned DOM lowering (uses `lib/web-ui`) |
| `api/impeller/` | native fringe (impeller.h bindings, GLFW/Metal host, input pump); `get-sdk.sh` fetches the SDK |

## Widget vocabulary

**Layout**: `row`, `column`, `spacer`, `stack` (absolute), `box` (padding,
`fill` background, `on-click`/`on-click-at`, `drag`/`on-drop`), `rect`
(fixed-size cell), `scroll` (a viewport over a taller child). **Content**:
`text` (single line), `paragraph` (wraps to the available width), `code`
(monospace), `text-input` (controlled), `slider`, `keyed` (list identity),
`link` (navigate to a route). **Typography**: a
`font` (family stack + size + weight + italic) with `sans`/`serif`/`mono`
helpers and `bold`; `text`/`paragraph` are overloaded to take either a size
(system sans) or a whole `font`. **Styling**: typed `color`/`rgb`/`fill` in the
core; themed components in the swappable `ui/style/default` library (below).

Text measurement is the ambient **`measure` effect** (`measure-text(content,
font, max-w)`); each backend installs the handler (native shapes an Impeller
paragraph, web measures via the host canvas / a hidden reflowed div). Layout
never mentions a backend, and a future caching / batching / line-breaking
measurer is a handler swap with no layout change.

### Routing (`ui/router`, `ui/nav`)

An app supplies `parse : string -> route` and `print : route -> string`; the
router turns the location hash into messages and back:

- `route-sub(ch, parse, to-msg)` — a subscription emitting `to-msg(parse(path))`
  on start (**deep-link**) and on every hash change (**back/forward**).
- `link(path, child)` — a real `<a href="#/path">` on the web (right-click /
  open-in-new-tab work; the hash change fires with no reload); a
  click-to-navigate target natively.
- `navigate(print, route)` — set the hash from `update`.

`ui/nav` is the host-selected hash façade (web = `window.location.hash` +
`hashchange`; native = an in-memory hash + change channel). Swapping the hash
for the History API later is a change behind this façade — apps and `link` are
unchanged.

### Styling (`ui/style/default`)

The core (`widget.kk`) is **style-agnostic** — it only knows typed
`color`/`fill`, never a theme. Styled widgets live in a **swappable style
library**; `ui/style/default` is the first one, and an alternative design
language (a future `ui/style/material`) is a sibling exposing the same
component names with its own palette and painting. There is deliberately no
universal token schema (each style library owns its own).

Two patterns run through the default library:

- **Static overloading** — `simple/foo` takes a string label, `widget/foo`
  takes any child; an unqualified `foo(x)` resolves by the type of `x`. So
  `primary-button("Save", Save)` and `primary-button(row([icon, label]), Save)`
  are the same call.
- **Hybrid token delivery** — *leaf* components (`button`) take pure **implicit
  tokens** (`?bg`/`?fg`), overridable per call
  (`button(text("Delete"), Del, ?bg = rgb(0.8,0.2,0.2))`) and adding nothing to
  the effect row. *Large / convenience* components (`primary-button`, `card`,
  `page`) read the ambient **`theme` effect** and bridge it to the leaves by
  binding tokens as vals in scope. So deep signatures stay clean (just `theme`),
  while leaves stay overridable. (Koka implicits can't carry a default, so the
  bridge — not an implicit default — is what supplies a leaf's token.)

`system-dark()` (host-selected: browser `prefers-color-scheme` on jsweb,
default dark elsewhere) lets an app start in the OS light/dark preference; a
manual toggle still overrides. The theme is switched by handling the view with
a different palette (`with val theme = if dark then dark else light`).

`scroll` puts its child at the viewport width with unbounded height, so it
scrolls when taller. The browser scrolls (an `overflow:auto` container);
native paints from the top (scroll offset + Impeller clip are a follow-up).
Because our flex has no "expand-to-fill" child yet, place `scroll` where the
parent already bounds its height (the app root, a fixed region), not as a bare
flex child that would over-consume — a flex-grow/`expanded` widget is the
natural companion (a follow-up).

Deliberately out of scope for now (documented divergences): text selection,
IME, CSS transitions; native scroll offset/clip; a flex-grow (`expanded`)
child; the History API (hash routing today); custom font-file loading (system
/ web-safe families today); native fonts honor size but not yet
family/weight/italic (needs an Impeller paragraph-builder shim). Native text
input is minimal (append / backspace / Enter / Escape-to-blur, cursor at end).

## Performance: reconcile (FBIP tree reuse)

Each frame `view` builds a fresh `widget<msg>` tree and layout produces an
`ltree`. Rather than rebuild the laid-out tree from scratch, the native
backend **reconciles** the new widget tree against the *previous* laid-out
tree (`ui/widget/reconcile`): matching constructor shapes reuse the old node
cell in place (the FBIP mechanism), and for flex/stack children a fast path
also reuses the list `cons` cells and `(dx, dy, ltree)` position tuples — a
reconcile+measure pass and a reposition pass, each consuming and reusing its
unique input list. Shape mismatches (or spacer-bearing / count-changed flex
lists) fall back to a fresh layout of that subtree.

The old tree must be *uniquely owned* when reconcile runs, so the backend
takes it out of its ref (swapping in a placeholder) before reconciling — see
`take-tree` in `api/impeller/backend.kk`.

Measured (`bench/`, 20k frames re-laying-out a changing 400-cell grid):
**~46% fewer bytes (2.8 → 1.5 GiB), ~25% faster**, and a structural check
confirms reconcile produces byte-identical layout to a fresh pass. Node
cells (8.0M → 400) and the list spine (24B cells 25M → 8.4M) both reuse. The
remaining allocation is the `widget` tree that `view` rebuilds each frame.

The web backend lays out fresh and lowers to DOM each frame; its reuse
happens at the DOM layer (vdom reconciliation reuses elements), so it does
not retain an ltree to reconcile.

### Future optimizations (not yet done)

- **Text-measure cache**: every `Text` builds a paragraph just to measure it
  (native rebuilds it again to paint). Caching metrics by `(content, font,
  max-w)` would skip reshaping unchanged text — likely a larger native win than
  the tree churn, since Impeller paragraph shaping dominates. The `measure`
  effect already makes this a **drop-in handler** (wrap the raw measurer in a
  caching one) with no change to layout.
- **View memoization**: skip rebuilding a subtree whose `widget` is unchanged
  from the previous frame — this reclaims the remaining per-frame `widget`
  allocation (the 8M cells reconcile can't touch). `keyed` could double as
  the memo token; the path toward dirty-tracking without a full signal
  system.

## Relationship to `lib/web-ui`

`web-ui` remains a permanent, first-class **web-only** library (`html<msg>` +
DOM): the right choice for apps that want the full DOM — forms, real
inputs, arbitrary attributes, dip-into-web escapes. `ui` keeps interface
names aligned with it (`app`, `row`/`column`/`spacer`, `primary-button`,
`card`, `page`, `theme`), so a portable app can often swap `web-ui/*`
imports for `ui/*` as long as it isn't using DOM-specific features.

## Building

Projects are three files (`main.kk`, `index.html`, a two-line `build.kk`);
`koka -e build.kk [-- jsweb | native | all]` stages each target. Native
needs the Impeller SDK (`lib/ui/api/impeller/get-sdk.sh`, macOS arm64) and
`brew install glfw`. See `samples/ui/readme.md`.
