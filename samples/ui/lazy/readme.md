# lazy

Builder lists: `ui/lazy`'s `lazy-column`, the `ListView.builder` equivalent.
Three 100k-row (or infinite) lists, same code on every backend.
`koka -e build.kk -- native` then `./app-native`.

To eyeball:

- The window (top-left counter of visible rows, if you add one, or just
  scroll fast) stays small even at 100,000 rows -- only the viewport +
  a small cache margin is ever built.
- Left pane (`keep = KeepAlive`): bump a few counters, scroll far away and
  back -- the counts you set are still there.
- Right pane (`keep = Transient`, the default): do the same -- the counts
  reset to 0, because scrolled-out rows are unmounted for real.
- Bottom pane has no `count`: it just keeps going, one page ahead of the
  scroll offset, however far you scroll.
