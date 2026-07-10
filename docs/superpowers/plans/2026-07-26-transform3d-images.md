# transform3d + basic images Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Two Tier-1 visual primitives per `docs/superpowers/specs/2026-07-26-transform3d-images-design.md` — `transform3d` (perspective-projected 2D via a 4×4 matrix, accurate hit-testing) and `image` (async-loaded, cross-backend).

**Architecture:** Both are paint+hit-only widgets mirroring `rotated`/`LRotate`, over the stable Impeller C API already vendored (bind `ImpellerDisplayListBuilderTransform`, `TextureCreateWithContents`, `DrawTextureRect`). Hit-testing is ONE shared Koka walk, so 3D hit lands once for both backends. Images: native decodes via vendored `stb_image` on a worker + uploads once to an identity-cached texture freed by the retention machinery; web lowers to `<img>`.

**Tech Stack:** Koka (lib/ui), Objective-C/C (impeller shim), Impeller C SDK, stb_image (single header), web DOM.

## Global Constraints

- Tier 1 ONLY: perspective-PROJECTED 2D — NO depth buffer, meshes, lighting, or runtime shaders. Those are Tier 2/3 (tasks #52 + roadmap), out of scope.
- `mat4` is 16 `float64`, ROW-major, index `[r*4+c]`. Native `ImpellerMatrix` is `float m[16]`; CSS `matrix3d` is COLUMN-major → transpose when emitting web.
- transform3d/image are paint+hit-only: LAYOUT is unchanged (child laid out at natural/box size), exactly like `Rotated`/`LRotate`.
- Hit-testing is the SINGLE shared `hit-go` walk (ui/widget) used by BOTH backends — implement 3D hit once.
- Image native = LOCAL/ASSET PATHS only (`stbi_load` reads files, no native HTTP); URLs work on WEB via `<img src>`. Documented caveat, not a bug.
- GPU textures are frame-budget-expensive: upload ONCE per image, cache by the image's owner identity, free via the retention machinery (`drop-ids`/prune) — never per-frame.
- Every widget/ltree ctor carries `owner : int32` (first field) — stamp `?key.key-id.int32` (transform3d/image are leaves w.r.t. identity).
- Koka gotchas: `?key : key` implicit on widget ctors; named local funs; `ctx`/`use`/`raw` reserved; exhaustive-match errors = the walk checklist; touch owning .kk for bundled .js; koka does NOT rebuild on .c/.m/.h change (clear LOCAL .koka or `-r`); live tier builds -O1; wasi-web needs node≥24.

## File Map

| File | Change |
|---|---|
| `lib/ui/transform.kk` | NEW: `mat4` type + helpers + `invert`/`apply-point`/`unproject` |
| `lib/ui/widget.kk` | `Transform3d`/`LTransform3d` + `Image`/`LImage` ctors; `transform3d`/`image` funs; layout/size/scroll-keys/map-msg/hit-go arms |
| `lib/ui/api/impeller/shim.c` | `kk_imp_transform` (4×4), `kk_imp_texture_create`/`kk_imp_draw_texture_rect`; vendor `stb_image.h` |
| `lib/ui/api/impeller/impeller.kk` | externs: `transform`, `texture-create`, `draw-texture-rect` |
| `lib/ui/api/impeller/backend.kk` | LTransform3d paint; LImage paint + texture cache + async load + retention drop |
| `lib/ui/api/web/backend.kk` | LTransform3d `matrix3d` lowering; LImage `<img>` lowering |
| `test/ui/mat4.kk`, `test/ui/transform-hit.kk` | NEW headless tests |
| `test/ui/basic.kk` or a new test | image lowering + retention-drop assertions |
| `samples/ui/gallery/` | flip-card + images demo |
| `util/test-wasi.sh`, `docs/ui/design-notes.md` | suite wiring + ledger §15 |

Tasks 1–3 are transform3d (1 pure, green standalone). Tasks 4–5 are images (4 web+headless-green, 5 native). Task 6 sample+docs.

---

### Task 1: `mat4` module + unit tests

**Files:** Create `lib/ui/transform.kk`, `test/ui/mat4.kk`.

**Interfaces (produces):**
```koka
pub value struct mat4( m : vector<float64> )   // 16, row-major [r*4+c]
pub fun identity() : mat4
pub fun perspective( depth : float64 ) : mat4   // row-major m[14] = -1/depth
pub fun rotate-x( rad : float64 ) : mat4
pub fun rotate-y( rad : float64 ) : mat4
pub fun rotate-z( rad : float64 ) : mat4
pub fun translate3( x : float64, y : float64, z : float64 ) : mat4  // m[3],m[7],m[11]
pub fun scale3( x : float64, y : float64, z : float64 ) : mat4
pub fun mat4/(*)( a : mat4, b : mat4 ) : mat4   // (a*b) applies b THEN a to a column vector
pub fun invert( a : mat4 ) : maybe<mat4>        // Nothing if singular
pub fun apply-point( a : mat4, x : float64, y : float64, z : float64 ) : (float64,float64,float64,float64)  // homogeneous (X,Y,Z,W)
// screen point -> child-local (x,y) on the z=0 plane through a's inverse
// (2D homography: rows/cols {0,1,3} of a; invert 3x3; dehomogenize); Nothing
// if singular or the point maps behind the camera (w <= 0)
pub fun unproject( a : mat4, px : float64, py : float64 ) : maybe<(float64,float64)>
```

- [ ] **Step 1: failing test** `test/ui/mat4.kk` (standalone self-checking main, like `test/ui/selector.kk` — a `fail` counter, `println("MAT4: n/m passed")`, nonzero exit on fail). Cases:
  - `identity` applied to a point returns it; `apply-point(identity, 3,4,5) == (3,4,5,1)`.
  - `translate3(10,20,0)` moves a point: `apply-point(translate3(10.0,20.0,0.0), 1.0,2.0,0.0)` → `(11,22,0,1)`.
  - compose order: `(translate3(10,0,0) * scale3(2,2,2))` applied to `(1,0,0)` = translate(scale) = `(12,0,0,1)` (scale first, then translate — verify the chosen order and PIN it).
  - `invert(m) * m ≈ identity` (within 1e-9) for `m = perspective(800.0) * rotate-x(0.5) * translate3(30,40,0)`; `invert(scale3(0,1,1)) == Nothing` (singular).
  - `unproject` round-trip: pick a child-local point `(lx,ly)`, forward-project through `M = perspective(800)*rotate-y(0.4)` (as `apply-point(M, lx,ly,0)` dehomogenized to screen `(sx,sy)`), then `unproject(M, sx, sy) ≈ (lx,ly)`.
- [ ] **Step 2:** run `stack exec koka -- -v0 --console=raw -ilib -itest/ui -e test/ui/mat4.kk` — fails (module missing).
- [ ] **Step 3:** implement `lib/ui/transform.kk`. `import std/num/float64` (cos/sin/sqrt). Vectors via `vector`/`vector-init`/`[]`. Multiply: standard row-major `c[r*4+col] = Σk a[r*4+k]*b[k*4+col]`. `invert`: the standard cofactor/adjugate 4×4 inverse (MESA `gluInvertMatrix`); return `Nothing` if `det == 0`. `apply-point`: `(X,Y,Z,W)` where `X = m[0]x+m[1]y+m[2]z+m[3]`, etc. `unproject`: extract the 3×3 `H` from rows/cols {0,1,3} of `a` (the z=0 homography), invert `H` (3×3 adjugate), apply to `(px,py,1)`, dehomogenize by the 3rd component `w` — `Nothing` if `|det H| < 1e-12` or `w <= 0`.
- [ ] **Step 4:** test passes. Also run `test/ui/basic.kk` (nothing else touched — sanity).
- [ ] **Step 5:** commit `git commit -am "ui/transform: mat4 type + helpers + invert/unproject"`.

### Task 2: transform3d widget — visual (both backends), approximate hit

**Files:** Modify `lib/ui/widget.kk`, `lib/ui/api/impeller/shim.c`, `lib/ui/api/impeller/impeller.kk`, `lib/ui/api/impeller/backend.kk`, `lib/ui/api/web/backend.kk`. Import `ui/transform` into widget.kk.

**Interfaces (produces):**
```koka
// widget ctor + ltree ctor (both first field owner:int32)
Transform3d( owner : int32, m : mat4, child : widget<a> )
LTransform3d( owner : int32, m : mat4, w : float64, h : float64, child : ltree<a> )
pub fun transform3d<msg>( child : widget<msg>, m : mat4, ?key : key ) : widget<msg>
// shim: extern transform( b : builder, m : mat4 ) : ioc ()  (concats a 4x4)
```

- [ ] **Step 1:** widget+ltree ctors mirroring `Rotated`/`LRotate` (grep every `Rotated(`/`LRotate(` arm — layout, size, scroll-keys, map-msg, both backends, owner-rect, hit-go — and add a sibling `Transform3d`/`LTransform3d` arm). `transform3d` fun stamps `?key.key-id.int32`. Layout: `Transform3d(o, m, child) -> LTransform3d(o, m, cw, ch, child.layout(c))` where `(cw,ch)=lchild.size` (child unchanged). size → `(w,h)`. scroll-keys/map-msg pass through.
- [ ] **Step 2:** shim `kk_imp_transform(builder, m : kk_vector, ...)`: read 16 doubles from the Koka vector into `ImpellerMatrix mat; mat.m[i] = (float)...;` then `ImpellerDisplayListBuilderTransform(b, &mat)`. Note: ImpellerMatrix expects COLUMN-major — TRANSPOSE our row-major `m[r*4+c]` → `mat.m[c*4+r]` (verify against a visible tilt; if Impeller is row-major here, drop the transpose — test empirically with the sample in Task 6 and document which). extern `transform-raw`/`pub fun transform(b, m : mat4)` in impeller.kk (unbox the vector; pattern off `kk_imp_rotate`).
- [ ] **Step 3:** native paint arm (backend.kk, mirror LRotate ~line 542): `M' = translate3(cx,cy,0) * m * translate3(-cx,-cy,0)` with `(cx,cy)=(x+w0/2, y+h0/2)`; `b.save(); b.transform(M'); b.paint-at(child, x, y, focus, hover, pressed, dc); b.restore()`.
- [ ] **Step 4:** web lowering arm (web backend.kk, mirror LRotate ~line 400): emit `transform: matrix3d(<16 comma floats, COLUMN-major = transpose of our row-major m>)` + `transform-origin: center center` on the positioned div.
- [ ] **Step 5:** hit-go arm — for THIS task, APPROXIMATE: recurse the child untransformed (`child.hit-go(px, py, x, y)`) so clicks on an untilted/small-tilt card still work and the build is green. (Task 3 replaces this with `unproject`.) Add a `// TODO(task 3): unproject` comment.
- [ ] **Step 6:** verify: headless basic 13/13 (untouched behavior); build `samples/ui/counter` native + jsweb (compiles with the new arms). Add a throwaway `transform3d(box(...), perspective(800.0)*rotate-y(0.5))` to a scratch check if needed — but the real visual check is Task 6. Gate here = compiles + existing suites green + a native 30-frame run of an app using transform3d doesn't crash (extend the counter sample temporarily OR rely on Task 6; minimum: `stack exec koka -- -O2 -ilib -e` a 5-line scratch app in /private/tmp that wraps a box in transform3d and lays out — asserts no crash).
- [ ] **Step 7:** commit `git commit -am "ui: transform3d visual (native 4x4 transform, web matrix3d); approximate hit"`.

### Task 3: shared inverse-projected hit-testing

**Files:** Modify `lib/ui/widget.kk` (the LTransform3d `hit-go` arm), `test/ui/transform-hit.kk` (new).

- [ ] **Step 1: failing test** `test/ui/transform-hit.kk` — a `test-scenarios` app with a `transform3d(keyed-or-scoped box, m)` where `m = perspective(800.0) * rotate-y(0.6)` over a known-size box at a known position. Compute (in the test, using `ui/transform`) the screen projection of the box's center and a corner; assert `t.find`/click on the projected center HITS the box's message, and a click just OUTSIDE the projected quad MISSES. (Deterministic metrics → the projection is reproducible.) Use `t.click-at(px,py)` for exact points.
- [ ] **Step 2:** run — fails (approximate hit uses untransformed coords, so the projected-point click misses / an off-quad click wrongly hits).
- [ ] **Step 3:** replace the LTransform3d `hit-go` arm: rebuild `M'` (same center-wrapped matrix as paint), `match M'.unproject(px, py) { Just((lx,ly)) -> child.hit-go(lx, ly, x, y); Nothing -> Nothing }`. (The child was laid out at (x,y) in its own space; unproject returns child-LOCAL coords already offset — verify the coordinate frame: unproject maps to the child's pre-transform screen frame, which is the same (x,y)-based frame the child's hit-go expects. Confirm with the test; adjust the center/offset handling until the projected-center click lands.)
- [ ] **Step 4:** test passes; basic/retain/windows/lazy still green.
- [ ] **Step 5:** commit `git commit -am "ui: accurate inverse-projected hit-testing for transform3d"`.

### Task 4: image widget — web + headless (native placeholder)

**Files:** Modify `lib/ui/widget.kk`, `lib/ui/api/web/backend.kk`, `lib/ui/api/impeller/backend.kk` (placeholder arm only), `test/ui/basic.kk` (or new `test/ui/image.kk`).

**Interfaces (produces):**
```koka
pub type image-fit { Contain; Cover; Fill; ImgNone }
Image( owner : int32, src : string, fit : image-fit, w : float64, h : float64 )
LImage( owner : int32, src : string, fit : image-fit, w : float64, h : float64 )
pub fun image<msg>( src : string, fit : image-fit = Contain, width : float64 = 0.0, height : float64 = 0.0, ?key : key ) : <keytree> widget<msg>
```

- [ ] **Step 1:** ctors + `image` fun (stamps `?key.key-id.int32`). Layout: box = `(width>0 ? width : clamp to constraint max-w, height>0 ? height : a sensible default e.g. min(max-h, width or 100))` — the image does NOT block on decode; the box exists first. Add arms to size/scroll-keys/map-msg/owner-rect/both backends/hit-go (hit = the box is a plain non-interactive region: `Nothing` from hit-go unless wrapped — mirror how a plain LText/rect hit-goes, i.e. contributes no hit).
- [ ] **Step 2:** web lowering (web backend.kk): `LImage(_, src, fit, w0, h0)` → `html/elem("img", [attr("src", src), style(pos-style(x,y,w0,h0) ++ ";object-fit:" ++ fit-css(fit) ++ ";object-position:center")] ++ extra, [])` where `fit-css : image-fit -> string` maps Contain→"contain", Cover→"cover", Fill→"fill", ImgNone→"none".
- [ ] **Step 3:** native placeholder arm (impeller backend.kk paint-at): for now paint a neutral fill box (`b.draw-rounded-rect(x,y,w0,h0,0.0, solid(Color(0.16,0.17,0.24)))`) — the real texture path is Task 5. Add a `// task 5: decode+upload+cache` marker.
- [ ] **Step 4: headless test** (`test/ui/image.kk` as a `test-scenarios` app, OR extend basic.kk): an `image("assets/x.png", fit=Cover, ?key=scope("pic"))` in the tree; assert `t.find("pic").is-just` (it lays out to a box) and, once Task 5 lands, retention (an unmounted image drops its cache entry — but the cache is Task 5, so THIS task asserts only lowering/layout; note the retention assert is added in Task 5). Keep counts stable.
- [ ] **Step 5:** verify: headless green; jsweb build of a sample with an image loads in headless Chrome and the `<img>` element exists (`--dump-dom | grep '<img'`); native build compiles + 30-frame run shows the placeholder (no crash).
- [ ] **Step 6:** commit `git commit -am "ui: image widget -- web <img>/object-fit + native placeholder + layout"`.

### Task 5: native image — decode, upload, identity-cached, async

**Files:** Modify `lib/ui/api/impeller/shim.c` (vendor stb_image + texture bindings), `lib/ui/api/impeller/impeller.kk`, `lib/ui/api/impeller/backend.kk`.

**Interfaces (produces):**
```koka
// impeller.kk externs
extern texture-create( ctx : any, rgba : /* bytes ptr held C-side */, w : int, h : int ) : ioc any  // returns ImpellerTexture (erased); see note
extern draw-texture-rect( b : any, tex : any, sx,sy,sw,sh : float64, dx,dy,dw,dh : float64 ) : ioc ()
// a decode: path -> a C-side RGBA buffer + dims, done on a worker
extern decode-image( path : string ) : ioc maybe<(any /*opaque buf handle*/, int, int)>
extern texture-release( tex : any ) : ioc ()
```

- [ ] **Step 1:** vendor `stb_image.h` into `lib/ui/api/impeller/` (single public-domain header; `#define STB_IMAGE_IMPLEMENTATION` in shim.c once). shim: `kk_imp_decode_image(path)` → `stbi_load(path, &w,&h,&n, 4)` → returns an opaque cptr to the pixel buffer + w + h (or a null/None on failure); `kk_imp_texture_create(ctx, buf, w, h)` builds an `ImpellerTextureDescriptor` (RGBA, w, h) + `ImpellerMapping` over the buffer → `ImpellerTextureCreateWithContentsNew`, then `stbi_image_free(buf)`; `kk_imp_draw_texture_rect(b, tex, src, dst)` → `ImpellerDisplayListBuilderDrawTextureRect`; `kk_imp_texture_release`. Wire externs in impeller.kk (box the ImpellerTexture as `cptr`, like the builder/paint handles).
- [ ] **Step 2:** backend cache: add `imgcache : ref<global, int32-map<img-state>>` to `mounted` (and win-mount if windows need images — punt: main only for MVP, note it), `type img-state { ImgLoading; ImgReady(tex : any); ImgFailed }`. Set-helpers like the other refs.
- [ ] **Step 3:** LImage paint arm (replace the placeholder): look up owner in `imgcache`:
  - absent → insert `ImgLoading`, `spawn` a worker (`std/async/thread`) that calls `decode-image(src)` off the render thread and emits the result back through a channel/`request`; on the render thread, `texture-create` → `ImgReady(tex)` (GPU upload MUST be render-thread) + `request-render()`; failure → `ImgFailed`. (Detail: decode on worker, UPLOAD on render thread — mirror how `samples/ui/threads` offloads work + returns to the main strand. If wiring a worker+upload split is too heavy for the paint path, an acceptable MVP fallback is: decode+upload synchronously on FIRST paint (one-frame hitch), cached thereafter — but PREFER async; if you fall back, log it as a concern.)
  - `ImgLoading`/`ImgFailed` → the placeholder box (Task 4's fill).
  - `ImgReady(tex)` → compute the dst rect from `fit` (Contain: scale-to-fit letterboxed centered; Cover: scale-to-fill center-cropped via src-rect; Fill: dst=box; ImgNone: native size centered, clipped to box) and `draw-texture-rect(tex, src, dst)` (clip to the box with save/clip-rect/restore for Cover/None).
- [ ] **Step 4:** retention drop: where the renderer prunes identities (the `drop-ids` path / a per-frame sweep of live owners), release textures for owners no longer present: `ImgReady(tex) -> texture-release(tex)` and drop the cache entry. Wire it so an unmounted image frees its GPU texture (the spec's improvement). Add the retention assert to `test/ui/image.kk` (Task 4) now that the cache exists: bump a model flag to unmount the image, settle, assert its cache entry is gone (expose a test-only `image-cache-size()` or assert indirectly via no crash + a re-mount reloading).
- [ ] **Step 5:** verify: native sample (Task 6 or a scratch) shows a real decoded image (manual eyeball note — headless can't verify pixels); native 60-frame run exits 0; the async load doesn't block the frame (the FPS/anim keeps running — reuse the threads-sample pattern to sanity check); headless + web still green.
- [ ] **Step 6:** commit `git commit -am "ui/impeller: native image decode (stb_image) + identity-cached textures + async load"`.

### Task 6: gallery sample + suite wiring + ledger

**Files:** Create `samples/ui/gallery/{main.kk,build.kk,.gitignore,readme.md}` + an `assets/` image; modify `util/test-wasi.sh` (native smoke list), `docs/ui/design-notes.md` (§15), `docs/ui/paper-outline.md`.

- [ ] **Step 1:** `samples/ui/gallery/main.kk`: a flip-card (`transform3d(card, perspective(800.0) * rotate-y(animate(...)))` toggling front/back on click) + a row of 2–3 `image("assets/…", fit=Cover)` + one `image("https://…")` (web-only note). Style with `ui/style/default`. build.kk = copy of `samples/ui/threads/build.kk`; `.gitignore` = `app-native`, `out*/`, `.koka/`. Include a small committed `assets/logo.png` (a tiny real PNG). Determine the paint transpose empirically here (the card must flip visually correctly — if mirrored, fix the row/col-major transpose in Task 2's shim and note it).
- [ ] **Step 2:** smoke: native `KOKA_IMP_FRAMES=90 ./app-native` exit 0 (flip animates, image decodes); jsweb build loads in headless Chrome, `<img>` present, no console errors.
- [ ] **Step 3:** add `gallery` to util/test-wasi.sh's native sample list.
- [ ] **Step 4:** ledger §15 (terse): transform3d (4×4, projected-2D, one-shared-walk inverse-hit via unproject, the row/col-major transpose finding); images (stb_image decode, identity-cached textures freed by retention — the improvement, async worker load, native-paths-only caveat, web `<img>`); Tier-1 boundary + task #52 pointer. Outline claims row.
- [ ] **Step 5:** full suite `./util/test-wasi.sh` green (known kklib first-run flakes rerun). No binaries committed except the tiny asset PNG. Commit `git commit -am "samples/ui/gallery + ledger 15: transform3d + images land"`.

## Self-review notes
- Spec coverage: mat4 (T1), transform3d visual+API (T2), accurate hit (T3), image API+web+layout (T4), native decode/upload/cache/async/retention (T5), sample+caveat+docs (T6). Native-paths-only + web-URL caveat carried in T4/T5/T6.
- Green-between-tasks: T2 ships approximate hit so the build is green before T3's unproject; T4 ships web+placeholder-native so images render on web before T5's native texture path.
- Type consistency: `mat4`/`unproject`/`transform3d`/`Transform3d`/`LTransform3d` and `image-fit`/`Image`/`LImage`/`image`/`img-state` names identical across tasks; `owner:int32` first field everywhere.
- Two empirical unknowns flagged for the implementer to pin (not guess): the ImpellerMatrix row/col-major transpose (T2/T6) and the exact child coordinate frame after unproject (T3) — each has a test/visual that decides it.
