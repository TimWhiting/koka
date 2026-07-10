# web-ui samples

Browser apps built with the `web-ui` library (`lib/web-ui`) on the
`wasi-web` target — plain wasm32-wasip1 core modules, no emscripten, no npm.

| sample | shows |
|---|---|
| `todos/`  | a routed SPA: two components with closed msg types, async via `spawn`, theming as a reader effect, styled components, drag & drop, keyed reconciliation — plus the self-driving verification hook used by `util/test-wasi.sh` |
| `conway/` | Conway's game of life (ported from Koka v1's `demo/dom/conway.kk`): the world as the model, a timer subscription as the clock, cell clicks as messages |
| `flying/` | the v1 `flyingDivs` demo: sprites hopping to random positions/colors — v1 mutated styles imperatively, here the positions live in the model and the diff moves the spans |

## A project is three files

```
myapp/
  main.kk       -- the app: model, view, update  (import web-ui/html, web-ui/app)
  index.html    -- the page: css + <div id="app"> + runKoka("./app.wasm")
  build.kk      -- the build script (two lines, below)
```

`build.kk`:

```koka
import web-ui/project

fun main()
  build-web-app()
```

`index.html` (minimal):

```html
<!doctype html>
<meta charset="utf-8">
<title>My App</title>
<div id="app"></div>
<script type="module">
  import { runKoka } from "./web-ui-host.js";
  await runKoka("./app.wasm");
</script>
```

## Build & run

```sh
export WASI_SDK_PATH=~/wasi-sdk-34.0-rc.1-arm64-macos   # wasi-sdk >= 34 (wasi-web only)
koka -e build.kk                    # wasi-web -> ./out
koka -e build.kk -- jsweb           # javascript backend -> ./out-js
koka -e build.kk -- all             # both
cd out && python3 -m http.server 8080
```

Every sample runs on both backends from the same `index.html`; the staged
`web-ui-host.js` differs per target (wasm bootstrap vs a module import).

`build-web-app()` compiles `main.kk` with `--target=wasi-web`, then stages
`out/` with the wasm (as `app.wasm`), the shared host runtime
(`web-ui-host.js`, the vendored WASI shim, `timers.js`) and your
`index.html`. Set `KOKA` to override the compiler command (the test suite
uses `KOKA="stack exec koka --"`).

## Debugging

- program `println`/`trace` output goes to the browser console
- debug instrumentation is off by default; enable it with
  `runKoka("./app.wasm", { debug: true })` or by opening the page with
  `?kokaDebug` appended to the URL
- `kokaDebug.dump()` in the console lists every live externref slot and what
  it references; `kokaDebug.detached()` must be empty outside a patch — a
  non-empty result is a leak (a Koka value owning DOM the page cannot show).
  See `lib/web-ui/readme.md`, "Debugging resource release".
