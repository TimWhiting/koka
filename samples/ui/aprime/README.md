# A-prime: the memoization architecture probe (decision artifact)

`main.kk` materializes the proposed lib/ui memoization design as a
self-contained console program: reactive cells behind dynamic ops with
AUTO-TRACKED reads, memo boundaries keyed by TREE paths, and SUBTREE
dirtiness (a memo misses when its key or any descendant key is dirty), so a
change re-runs exactly the dirty spines top-down -- re-installing every user
handler on the path. Run it:

    koka -e main.kk

The centerpiece is frame 3: `grandchild` reads the theme but its memoized
parent `child` does not -- on a theme change the parent still misses (its
subtree contains a dirty reader), descends, and the grandchild rebuilds under
the fresh theme and a freshly re-installed mid-tree user ambient. A naive
self-only dirty check starves that grandchild forever.

`research/` holds the probes that shaped the design, in order:

1. combined-pass memo -- the win exists (2100 -> 120 text measures, 17.5x)
2. two-pass (view then reconcile) -- pointer-stable memo + unsafe-ptr-eq
   short-circuit works across lib/ui's real pipeline shape
3. ambient staleness + the epoch mitigation for untracked `val` environments
4. THE KEYSTONE: a stored continuation FREEZES `effect val` evidence
   (resume replays the old theme) while `fun` ops over live handler state
   read fresh -- continuations do not solve ambient invalidation, and both
   designs need "changeable state behind live ops" anyway
5. auto-tracked deps + top-down dirty re-run under a mid-tree user handler

Key rules the design commits to (pending sign-off):
- changeable ambient state lives behind dynamic ops over the root store
  (uistate); `with val` is for constants; untracked user `val` envs need an
  epoch or a `provide`-style reactive wrapper
- dirtiness is subtree dirtiness over the key tree (the keytrie in lib/ui)
- rebuilds are top-down inside the view pass (correct for arbitrary user
  effects); storing builders/continuations for out-of-pass re-run is only
  admissible under the CLOSED-ROW rule: the builder's effect row must be
  closed over framework effects (all dynamic ops) -- the type checker
  polices capture scope. Animation-leaf splicing (option B) is the
  disciplined special case of that rule.

## Performance (research/bench.kk, -O2, 30 components x 30 items, 2000 frames)

Two families that differ in the CELL-READ path -- compare only within a
family (the cross-family gap is the read path, not memoization):

assoc-op store (reads via effect op + dep tracking + assoc lookup):

| variant                  | ms/frame | vs A            |
|--------------------------|----------|-----------------|
| A  no-memo full rebuild  | 0.25     | baseline        |
| B  memo, 1 dirty/frame   | 0.043    | 6x faster       |
| C  memo, ALL dirty       | 0.38     | ~52% OVERHEAD   |

O(1) vector store (reads by index; emulates keytrie-attached bits):

| variant                  | ms/frame | vs F            |
|--------------------------|----------|-----------------|
| F  no-memo full rebuild  | 0.088    | baseline        |
| D  memo, 1 dirty/frame   | 0.0045   | 20x faster      |
| E  memo, ALL dirty       | 0.091    | ~2-4% overhead  |

Readings:
- Memo with everything dirty is ALWAYS slower than its own baseline -- by
  ~52% with naive assoc bookkeeping, by ~2-4% (noise-adjacent) with O(1)
  bookkeeping. Hence trie-attached cache/dirty bits are an integration
  REQUIREMENT: they shrink the worst case (a theme flip) to noise while the
  steady-state animation frame is ~20x cheaper.
- F vs A isolates a separate finding: cell reads through the effect op +
  assoc store cost ~3x vs direct vector access on this read-heavy
  microbench (real frames are layout/paint-dominated, so less pronounced).
  The ops-as-interface design absorbs the fix: the handler can move hot
  stores to int-keyed vectors without touching callers.

## Store shoot-out: vector vs Patricia trees (std/data/int-map + int-set)

Same memo semantics, three stores (deep=10, 500 frames; G-I use int-map for
cells+cache, int-set for dirty):

| wide | steady state (1 dirty) | worst case (ALL dirty) vs own baseline |
|------|------------------------|----------------------------------------|
| 30   | vector 0.0045 = int-map 0.0045 | vector +2% -- int-map +10% |
| 100  | vector 0.006 = int-map 0.006   | vector +6% -- int-map +35% |
| 1000 | vector 0.048 vs int-map 0.080  | vector +6% -- int-map +49% |

Readings:
- STEADY STATE (the case that matters -- animation frames): identical up to
  100 components; at 1000 the vector's O(1) hit check pulls 1.7x ahead of
  int-map's two tree walks (member + lookup) -- but both are far below any
  frame budget (0.05-0.08 ms for a THOUSAND memo boundaries).
- WORST case: int-map pays two persistent O(log n) updates per rebuilt
  component (cache.set + dirty.remove); mergeable into ONE structure (a
  dirty flag inside the cache entry) to halve it -- integration detail.
- Oddly consistent: int-map no-memo READ baselines edge out the vector's
  (~10%) -- the var<vector> access path (bounds check + local-var machinery)
  is not free either.
- CONCLUSION: int-map/int-set are the right DEFAULT stores -- keytrie ids
  are sparse (vectors need dense indices + growth management) and the
  steady-state difference is nil at realistic sizes. The subtree-dirty BIT
  still belongs on keytrie nodes (O(1) prefix answer); int-map carries the
  memo cache and cells.

## Integration spec (settled design details)

The keytrie node grows fields ordered by access temperature -- the hot path
(descend's child scan, memo-enter's dirty check) never touches cold data:

    pub struct knode
      nid      : int
      dirty    : bool                       // HOT: subtree-dirty (memo-enter reads,
                                            //      writes flip ancestors via the zipper)
      children : list<(segment, knode)>     // HOT: live children (descend scans)
      payload  : maybe<knode-state>         // WARM: cells + memo cache at this identity
      retained : list<(segment, knode)>     // COLD: kept-alive unmounted subtrees

Keep-alive is a property OF THE KEY: each minting helper takes an optional
drop policy (`here(keep = ..)` / `scope(name, keep = ..)` / `idx(i, ..)`):

    type keep
      Transient    // prune payload + subtree on unmount
      KeepAlive    // move to `retained` on unmount; remount by the SAME path
                   // finds all state intact (tab scroll/expanders/fields)

Unmount detection needs no sweep of hit subtrees: when a memo boundary
RE-RUNS, the handler tracks which child segments were descended during that
build; at memo-exit, unvisited children are unmounted -- Transient ones
drop, KeepAlive ones move to `retained` (out of layout/paint entirely: no
widget references them, reconcile never sees them). A memo HIT's subtree is
by definition still mounted and is never touched. Remount promotes a
retained subtree back to `children` with identity, cells, memo and dirt
intact. Pruning of long-retained subtrees (epoch LRU) is a policy knob on
the handler, not the API.

Side stores (dep edges, scroll metrics, anchors) stay id-keyed int-maps in
the handler with @byref/swap uniqueness discipline; their entries die (or
survive) with their node's policy, applied at the same memo-exit point.

## Late spec additions (settled in review)

- **int32 stores**: `std/data/int32-map` / `int32-set` (int32-keyed Patricia)
  -- int64 keys are BigInt-costly on the JS backend (6x: 101 -> 17 ms on the
  lookup bench; native also improves 24 -> 14 ms). Runtime ids fit int32 with
  room to spare. The keytrie's id->path map uses int32-map.

- **LCA re-rooting** (in lib/ui/keytrie): walk-to ascends only to the
  divergence point with the target's path and descends the suffix -- not a
  full to-root + replay. Deep-parent sibling minting (depth-12 parent):
  308 -> 259 us/frame; flat traffic unchanged (LCA == root there). The
  prefix compare costs ~6% where it cannot help; an is-parent-of-focus fast
  path can remove that later.

- **Fan-out threshold**: when the dirty count crosses a threshold the
  handler declares a DIRTY STORM: writes stop recording readers (bump a
  counter only) and every memo boundary misses -- the frame becomes a plain
  full rebuild, whose measured overhead is the ~2-4% floor. Bounds both
  sides of a theme-flip-with-500-readers frame: no O(readers) dirty-set
  churn on write, no per-boundary checks worth anything on read.

- **Unmount detection by CONSUMPTION, not a diff pass**: during a memo
  boundary's rebuild, descend already SPLITS the old children list (the
  zipper's before/after); claimed children accumulate into the new list, so
  at memo-exit whatever REMAINS of the old list is exactly the unmounted
  set -- apply keep policy to the remainder in the same pass. Zero cost
  when every child revisits; O(unmounted) otherwise; no visited-set, no
  second walk.
