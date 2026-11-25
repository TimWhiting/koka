# web-ui: a Koka-native web framework (experimental)

> **See also `lib/ui`** — a portable widget framework that runs the same
> `view` on the browser *and* native (Impeller). Its web backend is built on
> this library (html/vdom/dom below are its internal machinery). Use `web-ui`
> directly when you want the full DOM: forms, real inputs, arbitrary
> attributes, and dip-into-web escapes. Use `ui` for portable apps.


A small, functional-reactive UI library for the browser: the Elm
architecture with the machinery deleted where Koka's effects and Perceus
make it unnecessary. Views are pure data, handlers are message values,
async is an effect, and DOM lifetime is reference counting.

Two backends share everything except the DOM fringe (selected per host in
`dom.kk`, the same way `std/async` selects its event loop):

- `--target=wasi-web` — a wasm32-wasip1 core module built with wasi-sdk
  clang; DOM objects cross as externrefs owned by a Perceus-managed table
  (`api/wasiweb`, with the release-debugging machinery).
- `--target=jsweb` — the javascript backend; the compiled Koka runs in the
  page and calls the DOM directly (`api/jsweb`).

Demos live in `samples/web-ui/` (a routed SPA, Conway's game of life, and a
port of the v1 flying-divs demo); `samples/web-ui/readme.md` is the guide to
starting a project of your own.

## Quickstart

A complete app is a model, a `view`, and an `update`:

```koka
import html
import app

type msg
  Increment
  Decrement

fun view( count : int ) : html<msg>
  div([], [
    button([on-click(Decrement)], [text("−")]),
    span([class_("count")], [text(count.show)]),
    button([on-click(Increment)], [text("+")])
  ])

fun update( count : int, msg : msg ) : dispatch<msg> int
  match msg
    Increment -> count + 1
    Decrement -> count - 1

pub fun main()
  app( 0, view, update )   // mounts under <div id="app">
```

Add an `index.html` with an `<div id="app">` and a `runKoka("./app.wasm")`
call (see `samples/web-ui/readme.md` for the template), plus a two-line
`build.kk`; then `koka -e build.kk` compiles and stages a servable `out/`.

Async work never happens in `update` itself — `spawn` a task and its result
comes back around as an ordinary message:

```koka
    AddSlowly ->
      spawn fn()
        wait(500.milli-seconds)   // runs interleaved, outside the UI path
        Added(10)                 // ...re-enters as a message
      m(pending = True)
```

## Design in five lines

- **`html<msg>` is pure data; handlers are message values** (`on-click(Add)`),
  never callbacks. Every DOM event funnels into the app's one message channel.
- **No `Cmd` type**: `update : (model, msg) -> dispatch<msg> model` requests
  async work through the `dispatch` effect's `spawn(task)`; the loop runs the
  task `interleaved` *outside* the UI path and feeds its result back as a
  message. The UI path (view/update/diff) is continuation-free by type — the
  model and mounted tree stay uniquely owned (the future FBIP diff depends on
  this).
- **No `Sub` machinery**: a subscription is any strand emitting into the
  channel (`subs = [hash-sub]`; see `every` in app.kk).
- **Detach is a call, release is a drop**: the diff makes the only structural
  DOM changes (append/remove/replace); dropping mounted-tree values releases
  the wasm-side references (externref table slots, see jsobj.c) so the
  browser GC can reclaim detached nodes. Listener registrations are droppable
  values too (`sub`), with eager deregistration in the patcher and an
  idempotent drop as the safety net.
- **Controlled form inputs**: `value(..)`/`checked(..)`/`disabled(..)` sync
  the live element *properties* (guarded, so an unchanged value never
  disturbs the cursor) — the input always shows what the model says.

## Files

| file | what |
|---|---|
| `html.kk` | `html<msg>`/`attr<msg>` vdom data + element/attribute/event helpers + `map-msg` (component embedding) |
| `vdom.kk` | mount / one-pass diff+patch; keyed reconciliation when children carry `key(..)`: LIS-minimal moves (unchanged order ⇒ zero DOM relocations), index-zip otherwise |
| `app.kk`  | the app loop, `dispatch` effect, `every` |
| `dom.kk` | the DOM interface, selecting a backend implementation per host |
| `api/wasiweb/` | wasi-web fringe: `koka:dom` core-module imports (dom.c), Perceus-owned externref-table slots + debug exports (jsobj.c) |
| `api/jsweb/` | jsweb fringe: direct DOM calls as inline javascript (dom.js) |
| `theme.kk` / `ui.kk` | theming as a reader effect + styled components and layout utilities on top of it |
| `project.kk` | `build-web-app()`: the whole build/stage step behind a project's `build.kk` |
| `bench/` | allocation/timing micro-benchmarks of the diff |

The browser side is `support/wasi-web/web-ui-host.js` (staged automatically
into every `--target=wasi-web` build directory): WASI bootstrap, the
`koka:dom` imports, and the `kokaDebug` release-debugging API.

## API sketch (html.kk)

**Elements** — `div span p h1 h2 ul ol li button input textarea label form
select option nav section header footer table thead tbody tr td th img
strong em pre code small anchor br() hr()`, all
`(attrs = [], children = []) -> html<msg>`; anything else via
`elem("tag", attrs, kids)`.

**Attributes** — `class_ id_ value placeholder style type_ name_ for_ title_
src alt href key` (strings); `disabled checked selected autofocus` (bools:
present when true, absent — and property-cleared — when false);
`classes([("done",it.done), ...])` for conditional class lists; anything
else via `attr("name","value")`.

**Events** — messages, never callbacks:

| helper | message carries |
|---|---|
| `on("ev", Msg)`, `on-click`, `on-double-click`, `on-blur`, `on-focus` | nothing (a plain message value) |
| `on-input(ToMsg)` / `on-change(ToMsg)` | the element's current value (`string`) |
| `on-key(ToMsg)` | the key name (`"Enter"`, `"ArrowUp"`, ...) — filter in `update` |
| `on-click-at(ToMsg)` | pointer client coordinates (`float64,float64`) |
| `on-drop(ToMsg)` + `draggable(data)` | the dragged payload (declarative drag & drop) |
| `on-event("ev", fn(ev) ...)` | anything read off the live event (`ev.key`, `ev.prop(name)`, `ev.num-prop(name)`) at fire time |

## Theming with algebraic effects (theme.kk, ui.kk)

The theme is a **reader effect**, not a parameter and not a global:

```koka
pub effect val theme : palette          // theme.kk: views read it...

fun view( m : model ) : html<msg>       // main.kk: ...the shell binds it
  with val theme = if m.dark then theme/dark else theme/light
  themed-view(m)
```

Styled components are functions that consume the effect — their types say
so (`theme html<msg>`) — defined once in `ui.kk` and used throughout:
`primary-button`, `quiet-button`, `text-input`, `card`, `page`, plus
flexbox layout utilities (`row`, `column`, `centered`, `spacer`) so views never
hand-write `display:flex`. Switching themes is just re-handling the same
views with the other palette; nothing threads through models or props, and
deeply nested components (the todos rows, the counter card) restyle
together. The demo asserts the toggle works (`theme=yes` in the title).

## Debugging resource release

`live-slots` says how many externref slots are live; the release-debugging
exports in jsobj.c (`slot-high-water`, `slot-ref`, allocation counters) let
the host enumerate them and say WHAT each one still references. The host
runtime has two modes: by default (release) the hot paths carry no
bookkeeping; pass `runKoka(url, { debug: true })` — or open any deployed
page with `?kokaDebug` — to enable the instrumentation, which exposes
`kokaDebug` in the browser console:

- `kokaDebug.dump()` — console.table of every live slot (`<li#items.done>`,
  `listener:click on <button#add>`, ...), with a `detached` flag
- `kokaDebug.detached()` — live slots referencing DOM that is no longer
  connected to the document: a Koka value still owns DOM the page cannot
  show. Outside of a patch this list must be EMPTY; the driver asserts it
  (`detached=0` in the title).
- `kokaDebug.gcCount()` — created nodes are registered with a
  `FinalizationRegistry`, so you can watch the browser actually reclaim
  them after slot release + detach (end-to-end proof, GC-timing permitting).

This detector immediately earned its keep: it found the replace/removal
paths of the patcher discarding subtrees by *drop only* — which releases
slots and host listeners but leaves the Koka-side listener-registry entry
(and the element captured by its closure) alive. `unsubscribe-tree` in
vdom.kk is the fix; the regression is pinned by `detached=0`.

Program stdout/stderr (`println`, `trace`) goes to the browser console.

## Composition & routing (shown in the demo)

- Components own **closed** msg types; parents embed views with
  `map-msg(child/view(m), WrapMsg)` and updates with
  `map-dispatch(WrapMsg) fn() child/update(...)` — child `spawn`s wrap into
  parent messages automatically (counter's async "+10" works this way).
- Routing is just messages: `window().events("hashchange")` + `get-hash()`
  in a subscription strand emitting `HashChanged` — no router object.
  Navigating away unmounts the page and Perceus frees its DOM slots (the
  demo's verify hook asserts `routefreed=yes`).

## Run the SPA demo

```sh
export WASI_SDK_PATH=~/wasi-sdk-34.0-rc.1-arm64-macos   # >= 34
cd samples/web-ui/todos && koka -e build.kk
cd out && python3 -m http.server 8080
# open http://localhost:8080 — the page drives itself (routes to todos,
# adds/toggles/deletes; routes to counter, clicks + fires the async +10;
# routes away and back; reorders and drags) and mirrors the assertions
# into the title:
#   <title>spa:todos=1/2 done;counter=12;routefreed=yes;back=1/2 done;keyed=yes;drag=yes;coords=yes;stable=yes;theme=yes;detached=0</title>
```

`util/test-wasi.sh` (repo root) runs this headlessly as part of the wasi
smoke suite, alongside the wasmtime/node checks.

## Koka gotchas encountered (useful for the next module)

- Type declarations need single-letter type parameters (`type html<a>`);
  multi-letter names don't bind in nested applications. Functions can use
  `fun f<msg>(...)` binders fine.
- `ioc` already contains `div` and `ndet` — repeating them in a row makes
  duplicate labels that fail to unify with closed rows (the main wrapper's).
- Tree recursion through `map` closures needs `std/core/undiv`'s
  `pretend-decreasing`; mutual recursion (patch/patch-kids) still infers
  `div` — fine, `ioc` includes it.
- Local `val`/inner `fun` annotations cannot reference the enclosing
  function's type parameters; omit them and let inference work.
- A struct field named like a lambda binding or a std function needs
  qualified access (`it.item/id`, `s.sub/id`).
- The `iev` C-codegen bug originally found here (local `var` vectors +
  nested `for` under an effectful context) was fixed at the root in type
  inference — see koka-lang/koka#907.

## Staged next (spec's v2 experiments)

FBIP fused diff, partial dirtying / signal leaf bindings, `view` effect for
component state, open-type messages for app-level routing, Concur-style
widgets. Promotion of `jsobj`/`dom` to `lib/std` once the API stops moving.
