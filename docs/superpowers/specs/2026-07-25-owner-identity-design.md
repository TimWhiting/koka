# Owner identity everywhere + selector addressing (task #49)

Status: approved direction (Tim, 2026-07-25). Supersedes the interim
"find-scope + LScoped wrapper" sketch — the fused design won on Tim's
argument: identity is essential to state correctness, the required-key
discipline (probe 1b/1c) exists to force it, and an int field everywhere is
cheap. PRE-PUBLICATION POLICY (Tim): superseded APIs are REMOVED outright —
no deprecation shims — until publication is announced.

## Goal

Every layout-tree node knows which identity built it. Addressing — tests,
anchoring, and the future semantics/devtools/FLIP consumers — becomes
selector queries over the keytrie's path table resolved to owner-tagged
geometry. `keyed`/`anchored` string tags and `Region(string)` targets are
REMOVED; one identity system remains.

## Identity representation (settled)

Keytrie ids are dense **int32** integers minted by the handler's monotonic
counter (int32 was already required for the web-performant keytrie maps) —
never memory addresses, so FBIP node reuse cannot perturb them, and never
recycled, so a stale id in a closure misses harmlessly (the designed
Transient semantics; refcounting ids would fight retention). 2^31 mints is
beyond any app lifetime; no rollover handling. The owner field costs 4
bytes per ltree node.

**Why the id must be STORED, not derived (settled during review).** A
tempting cheaper design derives a node's identity by walking to its nearest
id-bearing ancestor at query time. It is UNSOUND: addressing queries run
over the laid-out **ltree**, in the backend/tester, in a context with **no
keytree handler** (the keytrie maps id→path, and cannot map an arbitrary
ltree node back to an id); and a stateless mint point (a plain `column`
built under `idx(i)`) produces no id-bearing ltree node, so there is
nothing in the tree to walk to. The ambient identity is known ONLY at
widget-build time (under the keytree effect, `?key` lexically in scope),
BEFORE layout. Therefore `owner` must be captured at widget construction
and flowed through layout onto the ltree — which also means the field lives
on the **widget** ctors (stamped by smart constructors) AND the **ltree**
ctors (copied by `layout`; `layout` has no keytree so it cannot re-derive).
Content-addressed ids make this stable: `idx(i)`/`Named(n)` segments keep
their id across renders regardless of siblings (verified in the #50 hunt),
so a sibling appearing never renumbers a node's owner.

## Design

1. **`owner : int32` on every ltree ctor** (and the id-bearing widget ctors
   keep their existing key fields — they ARE the owner at those points).
   The owner is the AMBIENT key id at widget construction: smart
   constructors (`text`, `box`, `column`, `stack`, `rect`, `spacer`, …)
   gain implicit `?key : key` and stamp `?key.key-id` — a plain int copy,
   NO trie traffic (stateless nodes share their parent context's identity,
   exactly probe 1's minting discipline, now recorded). Id-carrying nodes
   (`LInteractive`, `LField`, `LInput`, `LScroll`, `LMemo`) stamp their own
   minted id as owner. This finishes the 1c convention: any function that
   builds widgets declares `?key : key` or does not compile — the
   compiler's missing-implicit errors are the migration checklist.
2. **Component root geometry**: the rect of identity `k` = the shallowest
   ltree node with `owner == k` (a component's outermost widget is built
   under its key). No wrapper node; `LScoped` is not introduced.
3. **Naming a leaf** (the old `keyed("count", text(...))`) = minting at the
   call site: `text(..., ?key = scope("count"))` — the leaf gets its own
   identity, addressable by name, one mint, no wrapper. This is the
   migration idiom for every current `keyed` use.
4. **Selector queries — the primary addressing API.** The trie handler's
   id→path table is the database; a selector is a path pattern:
   - grammar (MVP): whitespace-separated DESCENDANT steps; a step is
     `name` (matches `Named(name)`), `:i` (matches `Index(i)`), or
     `name:i` (both, adjacent segments). Examples: `"todos row:3 bump"`,
     `"inspector count"`, `"tl :2"`.
   - resolution: `kt-find( selector ) : list<int>` — new keytree op; scans
     the path table for paths matching the steps in order (gaps allowed
     between steps, adjacency only within `name:i`). Multiple matches are
     returned; consumers decide (tester errors on ambiguity, listing the
     matching paths rendered via segment/show).
   - tester: `t.find(sel)` (rect via owner-geometry), `t.click(sel)`,
     `t.texts(sel)` (texts under the resolved subtree = nodes whose owner
     is the id or a descendant identity — path-prefix test), plus the
     existing coordinate/scroll actions unchanged. The old string-name
     find/texts/click REPLACED (same function names, selector semantics —
     a bare name selector degenerates to the old behavior for unique
     names, so most test call sites survive verbatim).
5. **Anchoring**: `target` type becomes `Display | Scope( sel : string )`;
   `Region` REMOVED. The composer resolves `Scope` via kt-find + the
   owner-geometry walk against the CURRENT tree (no more previous-frame
   string registry for view targets; scroll-region auto-scrollbars keep
   their id-keyed metrics path, now plain int ids — the `id.show` string
   bridge dies). The anchor-rect registry survives only as the id-keyed
   rect store the backends publish for scrollbars/Panels; `anchored()` and
   the string registry surface are REMOVED.
6. **`kk:layer`**: the reserved LKeyed marker (web pointer-transparency)
   is replaced by a dedicated `LLayer( w, h, kids )` ltree node (identical
   to LFlex in every walk; the web lowering styles it pointer-transparent)
   — LKeyed is deleted with `keyed`.
7. **Reconcile/FBIP**: `owner` participates in node identity for reuse
   exactly as existing fields do; it changes only when structure changes,
   so no reuse regression. All walks (layout, reconcile, paint, hit,
   hover, scroll, each-anchor→now owner-aware, bake, both backends' 
   lowerings) thread the field mechanically.

## What is REMOVED (pre-publication policy — delete, don't deprecate)

`keyed`, `anchored`, `LKeyed` (replaced by `LLayer` for the marker case),
`Region(...)` targets, the string anchor registry surface
(`publish-anchor-rect`/`all-anchor-rects` become id-keyed internals), the
tester's string-name addressing internals (`each-anchor`'s name-walk).
Every in-repo user (tests, samples, docs) migrates in the same plan.

## Migration map (in-repo)

- Tests (basic/retain/windows/lazy/lazy-oversize, live scenarios): `keyed`
  wraps become `?key = scope(name)` mints or disappear where a component
  scope already exists (the double-tag cases this design exists to kill);
  find/click/texts call sites keep their names (bare-name selectors).
- Samples: same; lazy rows drop `keyed("row-"++i.show)` for the trie's own
  `idx(i)` (selector `"rows :5"`) — the per-row string allocation dies.
- Scrollbar linking (`scroll(name=...)` + themed bars) is already id-based
  internally; the name remains the scroll region's `Named` segment —
  unchanged surface.
- style libs / helpers gain `?key : key` where the compiler demands it.

## Testing

- Unit: selector resolution (kt-find) — names, indices, descendant gaps,
  ambiguity; owner-geometry (shallowest-node rect; leaf-mint rect).
- The full existing matrix re-passing after migration IS the acceptance
  test (headless x4 runtimes, native live x2, web live pass:9) — same
  counts, selector-addressed.
- New checks: a list-row click via `"name :i"` with no per-row strings
  (lazy tests); an anchor `Scope` popover in the overlay sample's headless
  probe.
- Ledger measurement note: build-time cost of the ?key threading (bench
  reuse.kk before/after — the stamp is an int copy; expect noise).

## Cuts

Selector kinds beyond name/index (`:input` etc.), attribute predicates,
sibling/child (`>`) combinators — grammar grows later over the same op.
Stored-owner uses beyond addressing (semantics tree, FLIP, devtools) are
consumers of this foundation, not part of it.
