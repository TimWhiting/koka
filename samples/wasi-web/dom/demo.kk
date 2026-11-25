/* DOM interop demo for `--target=wasi-web`.

   Koka code fetches `#counter` and `#btn` from the real browser DOM (through
   the `koka:dom` plain-wasm-import bindings, see `dom.c`/`dom.kk`), sets the
   counter's initial text, then subscribes to the button's `click` event as
   an async `channel<()>` (see `dom.kk`'s `events`) and loops `receive`-ing
   from it -- driven entirely by the host's real DOM events, dispatched back
   into this wasm instance through the `dispatch-event` export (see dom.c).
   `main`'s inferred effect includes `:async`, so the compiler installs
   `std/async`'s `@default-async` handler automatically (see
   `lib/std/async/async.kk`) -- same as `test/wasiweb/sleep1.kk`, no handler
   is invoked by hand here.

   Build + run: see build.sh and readme.md in this directory.
*/
module demo

import std/async
import dom

// Slot-recycling proof (Core Task 2's payoff -- see jsobj.c's `live-slots`
// export and ../readme.md, "Slot-recycling proof"): looks up the page's
// throwaway `#tmp` element, uses it once, and returns. `tmp`'s `element`
// value (and the `any` box/table slot it wraps, see dom.kk) is never
// referenced again after `set-inner-text` here -- Perceus emits a drop for
// it before this function returns, which fires jsobj.c's
// `kk_js_obj_free_fun` (table.set(slot,null) + free-list push) *before*
// index.html's verify hook ever runs (this function is called synchronously
// from `main`, which is itself called synchronously to completion up to its
// first suspend point -- see below). This is the actual proof that Perceus
// drop drives JS release: if it didn't fire, `live-slots` would read one
// higher than the baseline after this returns.
fun touch-tmp()
  val tmp = get-element-by-id("tmp").unjust
  set-inner-text(tmp, "touched")

pub fun main()
  val counter = get-element-by-id("counter").unjust
  val btn     = get-element-by-id("btn").unjust
  set-inner-text(counter, "0")
  // `events` registers the listener (forwarding `btn`'s table slot into the
  // `koka:dom/add-event-listener` import, see dom.c/dom.kk) and returns a
  // fresh `channel<()>` keyed by a plain Koka-side listener id -- `btn`
  // itself is never referenced again after this call, so its slot is freed
  // immediately (see ../readme.md's "slot math" section: only `counter` -
  // reused on every loop iteration below - stays live for the program's
  // lifetime; `btn`'s element is a one-shot value, not retained by the
  // receive-loop closure).
  val ch = btn.events("click")
  touch-tmp()
  // The page lives until the tab closes; there is no natural "done" for a
  // page with a live listener, so this loop runs forever (matching the
  // brief: `loop-done` staying false is correct here, unlike a batch
  // program that exits after doing fixed work). Order matters: show the
  // *current* count, then wait for the next click, then increment -- so
  // the counter text reflects "clicks received so far" (0 initially, then
  // 1 after the first click, 2 after the second, ...) rather than counting
  // one click ahead of what has actually been received.
  var count := 0
  while { True }
    set-inner-text(counter, count.show)
    ch.receive()
    count := count + 1
