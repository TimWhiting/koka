// Reference: app & routing.
module pages/reference-app-routing

import ui/keytrie   // ?key implicits (text/link now key their leaves)
import ui/widget
import ui/style/default
import blocks

pub fun ref-app-routing-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ api-entry("app", ["app(init, view, update, config = App-config(),",
                       "    subs = [], threads = Single)"],
      "The entry point: runs the model/update/view loop until the window "
      ++ "closes. `init` is the starting model; `view`/`update` are your "
      ++ "app's two pure functions. `subs` are background subscriptions "
      ++ "(below); `threads = Threaded` moves `update` (message handling, "
      ++ "plus subs and spawned tasks) onto its own worker thread, keeping "
      ++ "layout/paint/render on the main thread, on platforms that "
      ++ "support OS threads (falls back to `Single` where they don't, "
      ++ "e.g. web). No live demo here: `app` IS the whole running "
      ++ "program, not a widget — you're inside one right now, reading "
      ++ "this page.",
      demo = Nothing),

    api-entry("app-config", ["App-config(title = \"Koka UI\", width = 480,",
                              "           height = 360, root-id = \"app\")"],
      "The window/canvas settings `app` reads: `title` and `width`/"
      ++ "`height` for a native window; `root-id` for the DOM element the "
      ++ "web backend mounts into. Every field has a default, so most "
      ++ "apps only override `title` and a starting size.",
      demo = Nothing),

    api-entry("subs", ["subs : list<(channel<msg>) -> <async,ioc> ()>"],
      "Background tasks `app` runs alongside the render loop, each with a "
      ++ "channel to post messages back through — a timer, a websocket "
      ++ "listener, or (the case every app with routing needs) the "
      ++ "router's own hash-change listener. This site's `app` call "
      ++ "passes exactly one sub: `anchor-route-sub`, below.",
      demo = Nothing),

    api-entry("route-sub, anchor-route-sub", ["route-sub(ch, parse, to-msg)",
                                               "anchor-route-sub(ch, parse, to-msg)"],
      "A `subs` entry that turns the URL hash into route messages: "
      ++ "`parse` reads the hash path into your route type, `to-msg` "
      ++ "wraps it as an app message. `anchor-route-sub` is `route-sub` "
      ++ "plus fragment handling — `page#slug` splits into a route change "
      ++ "AND a `scroll-to(slug)` (state & animation reference), so a "
      ++ "hash like `#/reference-testing#test-scenarios` both navigates "
      ++ "and scrolls to that heading. This site uses `anchor-route-sub` "
      ++ "for exactly that reason — every cross-page anchor link on this "
      ++ "site depends on it.",
      demo = Nothing),

    api-entry("navigate, route/link, split-fragment", ["navigate(print, route)",
                                                         "route/link(route, print, child)",
                                                         "split-fragment(path)   // -> (page, maybe<slug>)"],
      "`navigate` pushes a route programmatically (from `update`, in "
      ++ "response to a message); `route/link` is `link` (interaction "
      ++ "reference) typed to a route value instead of a raw path string "
      ++ "— pass it your route and its `print` function instead of "
      ++ "building the path yourself. `split-fragment` is the parsing "
      ++ "half `anchor-route-sub` uses internally to separate the page "
      ++ "path from an optional `#slug`.",
      demo = Nothing),

    api-entry("window, compose (multi-window)", ["window(key, content, title,",
                                                   "       width = 480.0, height = 360.0)"],
      "`window` opens a second, OS-level titled window showing `content` "
      ++ "— call it from `view` like any other emitted overlay (closing "
      ++ "it, via the OS close button, is reported through `on-dismiss`). "
      ++ "Under the hood, every open window/overlay is composited "
      ++ "together each frame — that compositing is backend/harness "
      ++ "machinery, not something you call directly, so it isn't "
      ++ "documented as its own entry here. No live demo: a second OS "
      ++ "window can't be shown inside this page's own layout.",
      demo = Nothing) ]
