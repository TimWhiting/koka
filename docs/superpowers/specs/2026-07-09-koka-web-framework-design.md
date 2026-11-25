# A Koka-native web UI framework — Design

Date: 2026-07-09
Branch: `clang-wasm`
Status: draft, awaiting approval
Prereq: the `wasi-web` target (core modules + externref `jsobj` table), see
`2026-07-07-wasi-native-clang-design.md` rev 3 and `samples/wasi-web/dom/`.

## Goal

A light, Koka-idiomatic UI framework for the browser: functional-reactive in
style, a small virtual dom hiding the mutable external DOM, exploiting what
Koka uniquely has — algebraic effect handlers, Perceus reference counting with
deterministic drops, and `std/async` channels. Explicitly NOT a port of
React or Elm: where effects or Perceus make one of their concepts unnecessary,
we delete the concept rather than reimplement it.

## Design principles (from the maintainer)

- C only at the fringe; all logic/state in Koka.
- No raw callbacks in any public API — event sources are async values
  (channels), consumed with `receive`.
- kklib stays configuration-neutral.
- Light: an experimental-language demo framework, not production React.

## Architecture: the Elm loop, minus Elm's machinery

```koka
pub effect dispatch<msg>
  fun spawn( task : () -> <async,ndet> msg ) : ()   // async OUTSIDE the UI path

pub fun app( init : model,
             view : model -> html<msg>,
             update : (model, msg) -> dispatch<msg> model ) : <async,dom,ndet> ()
```

One message channel per app. The runtime: mount `view(init)`, then loop —
`receive` a msg, `update`, re-`view`, diff, patch. Two Elm concepts are
deleted outright:

1. **No `Cmd` *type***: `update` requests async work via the `dispatch`
   effect's `spawn`; the loop's handler runs spawned tasks `interleaved`
   outside the UI path and feeds each result back in as a message. No command
   data structure to construct or interpret — but see the style rule below.
2. **No `Sub`**: a subscription is any async strand that emits into the msg
   channel, composed with `interleaved`. `every(1.secs, Tick)` is a
   three-line user function, not framework machinery.

**Style rule — the UI path is continuation-free.** `view`, `update`, and
`diff` must not use `async` (no `await`/`receive` inside them): a captured
continuation would retain the model and vnode tree, destroying the unique
ownership that the v2 FBIP diff depends on — and an awaiting `update` would
block the message loop besides. `dispatch`'s `fun spawn` operation enforces
this by type: the task runs `async`, `update` itself never does. All
continuation capture happens at the loop boundary, where nothing holds the
tree.

### `html<msg>`: pure data, handlers are messages

```koka
pub type attr<msg>
  Attr( name : string, value : string )
  On( event : string, msg : msg )            // on("click", Increment)
  OnInput( to-msg : string -> msg )          // input value read at fire time

pub type html<msg>
  Elem( tag : string, attrs : list<attr<msg>>, children : list<html<msg>> )
  Text( text : string )
```

Handlers carry `msg` *values*, not closures: comparable during diff, and every
DOM listener funnels into the single `channel<msg>`. (Typechecked sketch:
scratchpad `vdom-sketch/vdom.kk`. Note: Koka needs explicit `<msg>` binders on
generic functions — multi-letter type vars aren't implicitly quantified.)

`OnInput` reads the input's value at fire time via a `get-value` fringe call —
the first JS→Koka string (see Fringe below).

### The mounted tree: detach is a call, release is a drop

Two distinct acts, never conflated:

- **Structural detach** — an explicit `remove-child` emitted by the diff for
  the removed subtree's root. This is the ONLY thing that changes the visible
  DOM. Dropping a Koka `element` never removes anything from the tree (the
  parent element still references it JS-side).
- **Reference release** — the Perceus drop of the mounted-subtree value nulls
  each element's table slot, un-pinning the JS objects so the browser GC can
  reclaim the detached subtree. A detached-but-still-held node stays alive
  until we drop; a dropped-but-attached node stays in the DOM.

Both must happen to free memory; the diff does the detach, the drop does the
release, and the drop cannot be forgotten (it's value lifetime, not a
remembered call).

**Destructor discipline** (avoiding the finalizer trap): jsobj free functions
run at a deterministic program point (refcount zero — Perceus, not GC), with
no resurrection and no ordering hazards. We keep it that way by rule: *a free
function may only make idempotent fringe calls — null a table slot, at most
`removeEventListener` — and must never run user Koka code.* Anything
user-observable happens explicitly in the patcher.

**Subscriptions are droppable values too** (idea from the design-exploration
report): a listener registration is an externref-table slot of its own whose
free function calls `removeEventListener` (idempotent, detached-safe, within
the discipline above) — a second use of the exact jsobj mechanism. This
replaces `dom.kk`'s current grow-only listener list: deregistration becomes
structural.

### Diffing: v1 plain, v2 FBIP

v1: pure `diff(old, new) : list<patch>` with index-based child matching plus a
`key` attr for keyed lists (consume the old keyed children into a map, drain
matches, drop the map — leftovers unmount by the drop). Patches applied
through the fringe.

v2 experiment (staged, not in v1): the old tree is uniquely owned at diff
time, so diff can be a fused traverse-and-mutate that consumes it — Perceus
reuse recycles vnode cells and element handles in place (FBIP). Needs a small
benchmark to confirm reuse fires on the match shapes before betting on it.

### Render pump and coalescing

`update` marks a dirty flag; a separate strand (raf tick via the fringe, or a
16ms timer initially) diffs+patches only when dirty — message rate decoupled
from render rate. A `latest()` combinator (drain-to-newest over a channel)
pre-coalesces high-frequency sources like mousemove/input. Both are userland
Koka over existing channels; no new primitives.

## Fringe additions (all thin, same attribute-import pattern as dom.c)

- `create-element(tag) : element`, `create-text(s) : element`
- `append-child(parent, child)`, `insert-before(parent, child, anchor)`,
  `remove-child(parent, child)`
- `set-attribute(el, name, value)`, `remove-attribute(el, name)`
- `get-value(el) : string` — JS→Koka string: import reports byte length, C
  allocates the `kk_string`, second import copies in (or one import writing
  into a C-allocated buffer after a length query)
- `remove-event-listener` via subscription slots (above)
- `raf : () -> <async> ()` frame tick (or defer; 16ms timer suffices for v1)
- Hardening folded in: `table.grow` failure guard in jsobj; multi-timer and
  cancel regression tests; the `nodebug` note documented where the table
  pattern is reused.

## Module layout (sample-scoped until proven, then lib/std promotion)

```
samples/wasi-web/framework/
  jsobj.{kk,c}      -- moved up from dom/ (shared primitive)
  dom.{kk,c}        -- fringe externs (grown per above)
  html.kk           -- html<msg>, attr<msg>, smart constructors
  vdom.kk           -- mounted tree, diff, patch application
  app.kk            -- the app loop, render pump, latest()
  todo/             -- the larger example (below)
```

## The larger example: a todo app on the framework

Add/complete/delete items, text input, count footer — exercises element
creation/removal (slot churn at scale), keyed lists, JS→Koka strings,
listener lifecycle via drops, multiple event kinds. Automated verify like the
counter demo: synthetic events + state mirrored into `document.title` +
`live-slots` assertions that deleted rows actually released their JS refs.

## Typed messages and components

v1: each component owns a **closed** msg type and `html<msg>` is a functor —
parents embed children with `map-msg(child/view(m.child), WrapChild)`, so the
compiler checks per-component match coverage (Elm's `Html.map`, kept because
exhaustiveness is worth the wrapping constructor).

Parallel exploration (not v1): `open type msg` (as `std/core/exn` does) +
implicit parameters to route handling — extensible across modules without a
central msg type, at the cost of exhaustiveness feedback. Prototype both on
the todo app and compare ergonomics.

## Staged v2 experiments (explicitly out of v1)

- FBIP fused diff (above)
- **Partial dirtying** (Flutter-style): mark dirty components and re-view only
  those subtrees. Needs component identity + local state, i.e. `ref`s (shared,
  not unique) or continuation checkpointing (captured, not unique) — both
  trade FBIP away where used. Signals (below) are its per-binding limit case;
  Flutter-style is per-component. Decide AFTER measuring whole-app re-render
  on the todo example.
- Solid-style signal leaf bindings (`bind-text(el, sig)`) bypassing diff for
  the text/attr 90% case — deliberately shared/ref-based, not unique
- `view` effect for component-local state (hook-like, but addressed by tree
  identity — kills call-order bugs by construction)
- Resumable `render-error` boundaries (`ctl`, can resume with a fallback)
- Concur-style widgets-as-control-flow (`button()` returns when clicked) —
  most Koka-native idea on the table, but the multi-strand render-merge
  problem is unsolved design; keep as research track (judicious continuation
  checkpointing may fit here)

## Risks

1. Reuse analysis actually firing on the v2 diff shapes — benchmark first.
2. The unique-old-tree invariant surviving contact with signals/boundaries if
   those v2 pieces land — nothing may retain a previous vnode.
3. `get-value`'s two-call string read racing DOM mutation — acceptable
   (single-threaded event dispatch), document it.
