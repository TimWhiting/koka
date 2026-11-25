# ui layout/reconcile microbenchmark

Isolates the tree passes (`ui/widget` layout and `reconcile`) from the
backends: a stub text measurer, no window, no Impeller. Measures the
per-frame allocation of laying out a 20×20 grid, 20 000 times.

## Method

`--fallocstats` compiles with mimalloc `MI_STAT=2`; `MIMALLOC_SHOW_STATS=1`
prints a heap-stats table at exit. Read the `total#` column (cumulative
allocation **count**) across all size-class rows, and the `total:` byte row.
mimalloc v3 hides the per-size-class `bin` rows by default — add
`MIMALLOC_VERBOSE=1` to get them back (otherwise you only see the aggregate
`binned` row).

```sh
koka -O2 --fallocstats -i../../.. -o bench reuse.kk
MIMALLOC_SHOW_STATS=1 MIMALLOC_VERBOSE=1 ./bench fresh      # fresh ltree each frame
MIMALLOC_SHOW_STATS=1 MIMALLOC_VERBOSE=1 ./bench reconcile  # reconcile vs the previous ltree
koka -O2 -i../../.. -e reuse.kk -- check                    # correctness
```

**What "fresh" vs "reconcile" enforce** (this is the whole method): `fresh`
builds a new widget tree and calls `layout` each frame with NO retained
ltree, so every node is allocated from scratch — nothing to reuse.
`reconcile` retains the prior ltree in a ref and takes it out UNIQUELY
(`r := placeholder` → refcount 1) before `reconcile(old, …)`; refcount 1 is
Perceus's precondition for in-place cell reuse (the same take-tree/set-tree
swap the native backend uses). This measures allocation **traffic**
(malloc/init/free work), NOT footprint: mimalloc recycles freed pages, so
peak RSS is a few MiB in BOTH modes. And FBIP is isolated by SUBTRACTION —
both modes rebuild the `widget<msg>` tree every frame, so the bins that stay
equal are the widget tree and the bins that DROP are the ltree allocation
reuse avoids.

`check` reconciles a changing grid across 30 frames and compares each
reconciled tree's structural fingerprint (kind + geometry at every node)
against a fresh layout of the same widget — they must be identical.

## Results (2026-07-26, this machine — WITH `owner : int32` on every node)

Total heap requested (mimalloc `total:` row) and wall time, same binary,
both modes, 20×20 grid × 20 000 frames:

| mode | bytes (total) | wall time |
|---|---|---|
| fresh     | 11.6 GiB | 6.5 s |
| reconcile | 1.5 GiB  | 0.9 s |

Net: reconcile requests **~7.7× fewer bytes** and runs **~7× faster** than a
fresh layout each frame, and `check: ok` (reconciled == fresh structural
fingerprint over 30 changing frames — and the fingerprint now includes each
node's `owner`, so reuse provably preserves identity, not just geometry).

Per size class (`total#` allocation count, reconcile vs fresh — the drops
are the ltree, the equal rows are the widget tree both modes rebuild):

| block | fresh | reconcile | what |
|---|---|---|---|
| 24 B | 394.8 M | **8.4 M** | list spine + `(dx,dy,ltree)` position tuples — reused in place by the flex fast path (~47×) |
| 80 B | 8.0 M | **400** | ltree node cell — reused in place (400 = a handful of fall-back subtrees) |
| 96 B | 8.0 M | **400** | ltree node cell — reused in place |
| 16 B / 40 B | 8.4 M / 8.8 M | 435 / 860 K | small layout intermediates, mostly reused |
| 48 B / 64 B | 8.0 M | 8.0 M | the `widget<msg>` tree — UNCHANGED (rebuilt every frame; only view memoization reclaims it, see `../readme.md`) |
| 32 B | 8.8 M | 17.2 M | reconcile's OWN walk overhead (the one bin reconcile pays more on) |

The node-cell 8.0 M → 400 story holds under `owner : int32` — owner just
nudged those cells from the old 128 B bin into the 80/96 B bins. The
dominant term is the 24 B spine/tuples (394.8 M → 8.4 M): the flex fast path
consuming and reusing its unique input lists is what makes reconcile's whole
`total:` land at 1.5 GiB.

**Note vs the earlier (2026-07) writeup.** The absolute `total#` figures are
higher than the old table (fresh 24 B 25 M → 394.8 M); the ratio and the
reuse structure are the same or stronger. The drift is a mimalloc-version +
counting change (v3.3.1), not a regression — do a controlled A/B on ONE
mimalloc build before quoting an absolute in the paper; the same-binary
ratio, the per-class DROP pattern, and `check: ok` are the solid claims. The
correction note below is exactly why we distrust cross-build absolutes.

The fast path applies to flexes with a matching child count and no spacers
(grids, rows, most lists — conway's grid at up to 60 Hz is exactly this).
Spacer-bearing or count-changed flexes fall back to a fresh layout of that
subtree (correctness over reuse).

### Correction note

An earlier writeup claimed a 95% reduction from a *naive* reconcile that
reused only the leaf node cells. That was doubly wrong: (1) the number came
from a **bin-misattribution error** — two separately-compiled harnesses put
the `LBox` cell in different size classes, so comparing one bin between them
compared "LBox in fresh" against "structural-only in reconcile," and the
totals were never summed; and (2) that naive reconcile rebuilt the list
spine fresh, so it was actually a *net loss* (2× slower). Preserving this
harness, summing all bins, and running both modes from one binary is what
surfaced both errors — and motivated the spine-reusing fast path measured
above.
