# Builder lists: lazy/virtualized scrolling (`lazy-column`)

Status: approved design (Tim, 2026-07-25). Task #47; prerequisite (#48,
koka-owned web scrolling) landed. Motivation: everything in a scroll region
today is built/laid-out/retained — no on-demand item building, no infinite
lists, no bounded state for off-screen items (the ListView.builder gap).

## Goal

A list that treats its children as a function of index: only the visible
window (± a cache margin) is built, laid out, and stateful; scrolled-out
items unmount through the EXISTING key-retention machinery; infinite lists
work from day one. One implementation for every backend, riding the unified
scroll model.

## API (lib/ui, portable)

```
pub fun lazy-column<msg>( item : (int, key) -> <keytree,uistate,ioc> widget<msg>,
                          count : maybe<int> = Nothing,   // Nothing = infinite
                          item-extent : float64 = 40.0,   // the item extent: EXACT in this
                                                          // MVP; becomes an ESTIMATE when
                                                          // variable extents land (same API)
                          cache : int = 4,                // extra items past each edge
                          keep : keep = Transient,        // scrolled-out item state policy
                          name : string = "",
                          ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc> widget<msg>
```

- `item-extent` is documented as the extent ESTIMATE from day one; the MVP
  treats it as exact (items laid out tight at it). Variable extents change
  internals only (measure materialized items, correct the window), never
  the signature — the "room for both" requirement.
- `count = Nothing` = infinite: content extent stays one viewport ahead of
  the scroll position; the scrollbar thumb keeps shrinking. `Just(n)` gives
  exact content height `n * item-extent`.
- `keep` is UNIFORM PER LIST and baked into each item's `idx(i)` key at
  first mint (a keytrie invariant: policy fixes at first mint). It is NOT
  per-item in this MVP, and nesting an inner KeepAlive under a Transient
  item does NOT survive scroll-out (pruning is subtree-rooted at the
  unmounted key — the top unclaimed key's policy decides). Designed
  follow-up, additive: `keep-of : int -> keep` plus DYNAMIC keep (a
  claiming descend refreshes the node's policy — "last claim wins" — the
  Flutter updateKeepAlive analog for state-dependent retention).
- `name` names the scroll region (scrollbar linking / tests), like `scroll`.

## Mechanics — a pure combinator, zero new ltree nodes

1. **Windowing off last-frame metrics.** `lazy-column` reads its region's
   `scroll-state(k)` (offset + viewport published by the previous frame's
   render — the same self-healing pattern as anchor rects and scrollbar
   metrics). `first = max(0, floor(offset / item-extent) - cache)`,
   `n = ceil(viewport / item-extent) + 1 + 2*cache` (the `+1` is a visible-margin
   row so a partial trailing row at the viewport edge is never left
   unmaterialized; clamped to `count`).
   First frame (viewport 0): materialize from index 0, `n = 1 + 2*cache`;
   the next render corrects. A materialization-window change requests a
   render the same way metrics changes do (settles once the window is
   right).
2. **Lowering.** Build items `first .. first+n-1` under `idx(i)`
   identities, then compose with the EXISTING machinery:
   `scroll( column([ top-spacer ] ++ items ++ [ bottom-spacer ]), name )`
   where top-spacer = `first * item-extent` tall, bottom-spacer brings the
   total to `count * item-extent` (bounded) or
   `(first + n + viewport/item-extent) * item-extent` (infinite: one page
   ahead). Offsets, clamping, hit-testing, scrollbars (auto + manual),
   wheel input, and web/native parity all come from the unified scroll
   model unchanged. Spacers are plain fixed rects (`rect(0, h)`), not flex
   growers.
3. **State recycling = the consumption boundary.** The item builds are
   bracketed with `kt-open(list-key)` / `kt-close(list-key)` (the memo-run
   protocol): materialized indices claim their `idx(i)` nodes; unclaimed =
   scrolled out — Transient prunes (ids handed to `drop-ids`, exactly like
   memo boundaries), KeepAlive retires to the retained store and remounts
   with state intact on scroll-back. The lazy list is the retention
   system's third client (memo, windows, lists) — no new machinery.
4. **Interaction.** Items are ordinary column children at real positions:
   clicks/hover/focus/drag walk normally; memo boundaries inside items
   compose normally; the keyed FBIP reconcile reuses the window's stable
   middle so a one-notch scroll rebuilds only the entering/leaving edges.

## Interplay notes (checked at design time)

- `lazy-column` inside a `memo` boundary: fine — the list re-runs when its
  reads (scroll-state) dirty it, which is exactly per-scroll.
- The kt-open/close bracket nests inside enclosing memo brackets the same
  way nested memos do (per-node stale lists).
- Infinite + `keep = KeepAlive` retains every visited item's state forever
  (documented; the epoch-LRU knob remains the parked eviction answer).
- Scroll-to-index is deliberately not an API yet;
  `set-scroll-offset(k, i * extent)` is the escape hatch.

## Testing

- Headless `test/ui/lazy.kk`: 10k-item bounded list — assert the tree
  materializes only `~viewport/extent + 2*cache` items (count the item
  texts); scroll far → window moved, content height exact; recycling both
  policies (bump item 5's counter, scroll away + back: Transient reset,
  KeepAlive kept); infinite mode grows content ahead of the offset.
- Live tiers: one `lazy` scenario driving `t.scroll` against a lazy list
  on native AND web (both tiers already run scroll after #48).
- Ledger measurement note: materialized window size independent of count
  (10 vs 10k vs infinite).

## Cuts (MVP)

Variable extents (seam reserved via item-extent-as-estimate); per-item /
dynamic keep (designed follow-up above); horizontal lazy lists; sticky
headers / separators sugar; scroll-to-index API; eviction (LRU knob).
