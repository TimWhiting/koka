# ui samples

Portable apps built with `lib/ui`. Each `main.kk` is written once against
`widget<msg>` and runs on all three backends — browser (wasi-web, jsweb) and
native macOS (Impeller).

| sample | shows |
|---|---|
| `counter/` | the minimal app; `Add 10 (async)` proves `spawn` works on every backend |
| `conway/` | Game of Life: a cell grid (`rect`), a self-scheduling timer (`spawn` chain), a Hz `slider` |
| `flying/` | the v1 flying-divs port: `stack` absolute placement, timer chain, typed colors |
| `todos/` | a routed SPA: text input, keyed list, drag-reorder, theme toggle, two embedded components (`map-msg`/`map-dispatch`), plus a `?drive` self-driver used by `util/test-wasi.sh` |

## A project is three files

```
myapp/
  main.kk       -- model, view : model -> widget<msg>, update
  index.html    -- <div id="app"> + runKoka("./app.wasm")   (web targets)
  build.kk      -- import web-ui/project; fun main() build-web-app()
```

## Build & run

```sh
# browser
koka -e build.kk              # wasi-web -> ./out   (needs WASI_SDK_PATH)
koka -e build.kk -- jsweb     # javascript -> ./out-js
cd out && python3 -m http.server 8080

# native (macOS arm64): once, fetch the renderer + window lib
../../../lib/ui/api/impeller/get-sdk.sh
brew install glfw
koka -e build.kk -- native    # -> ./app-native
./app-native                  # KOKA_IMP_FRAMES=n auto-closes (testing)

koka -e build.kk -- all       # every applicable target
```

The web page is identical across the two browser targets (only the staged
`web-ui-host.js` differs). Native shares the exact same `main.kk`.

## Notes

- Same code, two layout engines' worth of pixels: web positions our
  laid-out tree with CSS `position:absolute`; native paints it with
  Impeller. Small divergences (text metrics, sub-pixel rounding) are
  expected.
- Long text clips rather than wrapping (single-line display in v1); native
  text input is minimal (append / backspace / Enter / Escape). See
  `lib/ui/readme.md` for the full list of v1 boundaries.
- For web-only apps that want the full DOM (arbitrary attributes, forms,
  routing), `lib/web-ui` and its `samples/web-ui/*` remain first-class.
