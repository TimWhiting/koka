# transform3d + basic images (lib/ui visual primitives, Tier 1)

Status: approved design (Tim, 2026-07-26). Two paint-time visual primitives
that need no GPU subsystem beyond the stable Impeller C API we already
vendor. Explicitly Tier 1 of the 3D/texture roadmap: perspective-PROJECTED
2D (no depth buffer / meshes / lighting) + image display. Tier 2 (runtime
fragment shaders via impellerc) and Tier 3 (true 3D — see task #52,
flutter_scene may now run anywhere Impeller does) are out of scope.

## Grounding

`ImpellerMatrix` is `float m[16]` (4×4); `ImpellerDisplayListBuilderTransform`
concatenates one — both already in the SDK, unbound in our shim.
`ImpellerTexture` (`TextureCreateWithContentsNew`) + `DrawTextureRect` are
present-but-unbound. `rotated`/`LRotate` is the exact template (paint+hit
node, layout unchanged; save/translate/rotate/restore native, CSS transform
web). Hit-testing is ONE shared Koka walk (`hit-go` in ui/widget) used by
BOTH backends, so 3D hit-testing is implemented once.

## Part A — transform3d

**API (ui/widget, or a new ui/transform module):**
```
pub value struct mat4( m : vector<float64> )   // 16 floats, row-major

pub fun identity() : mat4
pub fun perspective( depth : float64 ) : mat4          // depth>0; classic 1/-d in [3][2]
pub fun rotate-x( rad : float64 ) : mat4
pub fun rotate-y( rad : float64 ) : mat4
pub fun rotate-z( rad : float64 ) : mat4
pub fun translate3( x : float64, y : float64, z : float64 ) : mat4
pub fun scale3( x : float64, y : float64, z : float64 ) : mat4
pub fun mat4/(*)( a : mat4, b : mat4 ) : mat4          // compose (a then b = a*b applied right-to-left, document the order)
pub fun invert( a : mat4 ) : maybe<mat4>               // Nothing if singular; needed for hit-testing
pub fun apply-point( a : mat4, x : float64, y : float64, z : float64 ) : (float64,float64,float64,float64) // returns (x',y',z',w') homogeneous

pub fun transform3d<msg>( child : widget<msg>, m : mat4, ?key : key ) : widget<msg>
```
Common cases read well: card flip `rotate-y(a)`, tilt
`perspective(800.0) * rotate-x(a)`.

**Widget/ltree:** `Transform3d(owner, m, child)` widget →
`LTransform3d(owner, m, w, h, child)` ltree. Layout: lay the child out
UNCHANGED at its natural size (paint+hit-only, exactly like `Rotated`);
`size` = child size; `scroll-keys`/`map-msg` pass through.

**Native paint (impeller backend):** build the effective matrix
`M' = translate(cx,cy) * m * translate(-cx,-cy)` (about the child's center
`(cx,cy) = (x + w/2, y + h/2)`), then `b.save(); b.transform(M'); paint child
at (x,y); b.restore()`. New shim binding `kk_imp_transform(builder, m16)`
→ `ImpellerDisplayListBuilderTransform`; Koka extern `transform(b, mat4)`.

**Web lowering:** `transform: matrix3d(<16 floats>)` + `transform-origin:
center center`. CSS matrix3d is COLUMN-major, our `m` is row-major →
transpose when emitting. The `<div>` positions unrotated (like LRotate).

**Hit-testing (shared `hit-go`, both backends):** add an `LTransform3d`
arm. The node maps child-local (lx,ly,0) → screen via `M'`. To hit-test the
incoming screen point (px,py): compute `M'⁻¹` (via `invert`; if singular,
miss), treat (px,py) as a ray from the camera, intersect the child's z=0
plane, perspective-divide, reject `w' ≤ 0` (behind camera) → child-local
(lx,ly); recurse `hit-go(child, lx, ly, x, y)`. Nested transform3d compose
because each node re-maps the point. Document the projection derivation in
a comment (it is the one piece of real math here).

## Part B — basic images (async load)

**API (ui/widget):**
```
pub type image-fit { Contain; Cover; Fill; ImgNone }
pub fun image<msg>( src : string, fit : image-fit = Contain,
                    width : float64 = 0.0, height : float64 = 0.0, ?key : key ) : <keytree> widget<msg>
```
`width`/`height` 0 = size to the box the parent gives (fit maps the decoded
pixels into it); nonzero fixes the box. `image` mints/uses `?key` as owner
so it's addressable and its texture keys off that identity.

**Widget/ltree:** `Image(owner, src, fit, w, h)` widget →
`LImage(owner, src, fit, w, h)` ltree. Layout gives it the requested/available
box (it does NOT block on decode — the box exists before pixels do).

**Native (impeller backend) — the async resource lifecycle:**
- A per-owner texture cache `int32-map<img-state>` in the backend, where
  `img-state = Loading | Ready(texture) | Failed`.
- On paint of an `LImage` whose owner is not in the cache: mark `Loading`,
  `spawn` a worker (existing `std/async/thread`) that calls `stbi_load(path)`
  off the render thread → RGBA pixels + (w,h); hand the pixels back; the
  render thread (the only one that may touch the Impeller context) uploads
  once via `TextureCreateWithContents` → `Ready(texture)`, and
  `request-render()`. Decode failure → `Failed` (+ a one-line log).
- Paint: `Loading`/`Failed` → a placeholder (a neutral fill box; themeable
  later). `Ready(tex)` → `DrawTextureRect(tex, src-rect, dst-rect)` with the
  dst computed from `fit` (Contain letterboxes, Cover crops, Fill stretches,
  ImgNone centers at native size, clipped to the box).
- Lifecycle: when the image's owner is pruned (unmount, `drop-ids`), its
  cached texture is released — GPU memory follows the widget tree via the
  EXISTING retention machinery (the improvement over an imperative LRU
  cache). Add a backend hook the renderer already calls on prune, or a
  sweep keyed off the live owners each frame.
- Vendor `stb_image.h` (single header, public domain, no dep tree) at the
  impeller fringe; `stbi_load` reads AND decodes a file path, so NO Koka
  bytes-read or HTTP plumbing is needed.

**Web (web backend):** `LImage` lowers to a real `<img src=...>` styled with
`object-fit` (Contain→contain, Cover→cover, Fill→fill, ImgNone→none) +
`object-position:center`, absolutely positioned in its box. The browser
fetches + decodes (paths AND URLs) asynchronously and paints progressively;
no texture code, no worker.

**Scope caveat (documented, deliberate):** native loads LOCAL/ASSET PATHS
only (`stbi_load` reads files, not URLs — no native HTTP client in-tree).
URLs work on WEB now; native URL fetch is a follow-up (needs an async HTTP
client). So `image("assets/logo.png")` is cross-backend; `image("https://…")`
is web-now / native-later.

## Testing

- Headless (ui/test): `mat4` unit tests (compose associativity vs a hand
  matrix; `invert(m) * m ≈ identity` for perspective+rotate; apply-point
  round-trips) in a standalone `test/ui/mat4.kk`. A transform3d HIT scenario:
  a `transform3d`-tilted target, assert `t.click` on its projected center
  reaches it and a click outside the projected quad misses (the inverse-hit
  is pure Koka → fully deterministic headless). Image: assert `LImage`
  lowers with the right src/fit; assert an unmounted image's texture id is
  dropped from the cache (retention).
- Live: `samples/ui/gallery` — a flip-card (`rotate-y` animated) + a couple
  of `image("assets/…")`s + one `image("https://…")` (web only); native +
  jsweb 30/60-frame smoke in util/test-wasi.sh. Native asset paths resolve
  relative to the sample dir.

## Cuts

True 3D (depth/mesh/lighting/glTF — Tier 3, task #52); runtime fragment
shaders (Tier 2, impellerc build integration); native URL fetch; image
animation/GIF/srcset; image tint/filter (compose with the existing
`ImageFilter` API later); non-uniform texture sampling/tiling beyond `fit`.
