// Reference: async.
module pages/reference-async

import ui/keytrie   // ?key implicits (text/link now key their leaves)
import ui/widget
import ui/style/default
import ui/async
import ui/dispatch
import std/async
import std/time/duration
import blocks

pub fun ref-async-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  val fg = theme.fg
  [ api-entry("future-boundary", ["future-boundary(run, ready, placeholder = default-placeholder(),",
                                   "                failed = default-error, min-load = zero)"],
      "The general async primitive: `run` kicks off async work, `ready` "
      ++ "builds the widget once it resolves. While pending, shows "
      ++ "`placeholder`; `min-load` holds the placeholder at least that "
      ++ "long even if `run` finishes sooner, so a fast local resolve "
      ++ "doesn't flash. If `run` throws, `failed` gets the exception and "
      ++ "a retry thunk — clicking retry bumps an internal generation and "
      ++ "re-kicks `run`; a stale in-flight result from a PRIOR "
      ++ "generation is discarded rather than racing the new one. "
      ++ "`image`/`image-path` (text & content reference) are built on "
      ++ "this — see that page for the specific image-loading case. One "
      ++ "run below, that resolves after a wait:",
      demo = Just(demo-panel(
        ["future-boundary(",
         "  fn() {",
         "    wait(400.milli-seconds)",
         "    \"done\"",
         "  },",
         "  fn(v) text(",
         "    \"Answer: \" ++ v,",
         "    15.0, theme.fg),",
         "  placeholder = text(",
         "    \"loading...\",",
         "    15.0, theme.fg))"],
        future-boundary(
          fn() { wait(400.milli-seconds); "done" },
          fn(v : string) text("Answer: " ++ v, 15.0, fg),
          placeholder = text("loading...", 15.0, fg),
          ?key = scope("fb-demo"))))),

    api-entry("retry-async", ["retry-async(id : int)"],
      "A lower-level primitive: bumps the async entry at `id`'s "
      ++ "generation directly. `future-boundary`'s own retry button does "
      ++ "NOT call this — it inline-implements the fuller sequence (a "
      ++ "generation bump, a fresh want, and a render request), because a "
      ++ "bump alone re-renders but starts nothing. Reach for "
      ++ "`retry-async` directly only if you're building an async "
      ++ "boundary from scratch, outside `future-boundary`.",
      demo = Nothing),

    api-entry("async images", ["image-path(src, load = Async, ...)"],
      "`image`/`image-path`'s `load = Async` mode is `future-boundary` "
      ++ "under the hood — see the text & content reference's `image, "
      ++ "image-path` entry for the full picture (fit modes, "
      ++ "placeholder, `min-load`, the Sync escape hatch).",
      demo = Just(doc-link("reference-text-content#text-and-content",
                            "image, image-path (text & content reference)",
                            ?key = scope("img-link")))),

    api-entry("dispatch", ["effect dispatch<a>", "  fun spawn( task : () -> <async,ioc> a ) : ()"],
      "An effect `update` can use to request async work WITHOUT doing "
      ++ "async work inside `update` itself: `spawn` hands the runtime a "
      ++ "task; the runtime runs it interleaved at the render-loop "
      ++ "boundary, and its result comes back around as an ordinary "
      ++ "message through `update`, same as a click. This is how "
      ++ "`update` stays a plain, testable function — no async threading "
      ++ "through your message-handling code — while still kicking off "
      ++ "real work (an HTTP-style call, a timer) in response to a "
      ++ "message. No live demo here: `dispatch` is only meaningful "
      ++ "inside an app's real `update` function, which this "
      ++ "message-agnostic reference page doesn't have.",
      demo = Nothing) ]
