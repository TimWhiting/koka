# Web scroll takeover: koka-owned scrolling on the web backends

Status: approved direction (Tim, 2026-07-24): full unification, NO escape
hatch / per-region fallback (that would require keeping both paths alive --
if testing shows we need browser scrolling back, we revert via git).
Motivation: builder lists (task #47) need koka-driven windowing; with
browser-owned web scroll that means a second virtualization path and a
double-owned offset. Precedent: we already unified hit-testing the same way;
Flutter owns scrolling on every platform including web.

## Goal

One scroll model on every backend: the offset lives in ui/state, wheel input
drives the SAME clamp/apply path as native, metrics publish everywhere, and
`scrollbar`-as-view (auto + manual, themeable) renders on web too. The
browser's scroller (overflow:auto), its native bar, and the "web scrolling
is browser-owned" test gates all go away.

## Scope

- Wheel-driven scrolling, desktop-complete. Browsers forward macOS
  momentum-phase wheel events as ordinary wheel events, so trackpad inertia
  arrives through the same listener for free.
- Explicit FOLLOW-UPS (not in this change): touch/fling physics for mobile
  web (the known-hard part), keyboard paging (space/PageDown), rubber-band
  overscroll, scroll-anchoring niceties.
- Both web hosts: jsweb and wasi-web (dom.js + dom.c/web-ui-host.js stay in
  lockstep as usual).

## Design

1. **Lowering** (lib/ui/api/web/backend.kk, LScroll arm): `overflow:auto`
   viewport + content-sized inner box becomes `overflow:hidden` clip div +
   inner box shifted by the BAKED offset (`transform:translate3d` along the
   scroll axis -- one style write per scroll tick, the virtual-list idiom).
   The browser bar disappears with the overflow:auto.

2. **Baked offsets become shared.** `bake-scroll` (currently a private
   impeller-backend walk writing each region's clamped ui/state offset into
   its LScroll node) hoists to a shared home (ui/state, next to the scroll
   ops it reads) and BOTH backends call it at render time -- paint and
   hit-testing read one value, same as native today.

3. **Wheel input** joins the web backend's existing root-listener set
   (which already posts events for the shared Koka hit walks): a root
   "wheel" listener (passive: false, preventDefault -- the page must not
   also scroll) posts `EvWheel(x, y, dx, dy)`; the pump-loop handles it
   with the SAME logic as native's drain-scroll -- `scroll-at(x, y)` shared
   walk, horizontal regions consume dx falling back to dy, clamp,
   `set-scroll-offset`, request-render. The clamp/apply core is extracted
   into one shared function (ui/state) so native's drain-scroll and web's
   handler cannot drift.

4. **Metrics + scrollbars.** The web render calls the shared
   `sync-scroll-metrics`/each-scroll publication (today native-only), and
   publishes scroll-region rects into the anchor registry the way native
   does at paint -- so the scene composer's AUTO scrollbar views (and
   manual `scrollbar(...)`) appear on web with zero composer changes.
   The neutral/themed bar widgets are already portable.

5. **Test surface.** `test-inject-scroll-at` stops driving `scrollTop` on a
   DOM scroller (dom.js inject-wheel) and instead dispatches a real wheel
   event at the coordinates (or posts EvWheel directly through the same
   listener path -- whichever proves the production path; prefer the real
   DOM WheelEvent). The scroll scenario UN-GATES for web: `test-backend`
   gating for scroll drops, the web live tier expects 7 checks, and
   util/test-wasi.sh's web-live expectation updates.

6. **Deletions** (the point of the exercise): the overflow:auto lowering,
   dom.js/dom.c inject-wheel's scroller search + scrollTop write, the
   "browser owns web scrolling" comments/gates, and the web-only scrollbar
   asymmetry notes in view.kk/readme.

## What could regress (accepted, watched)

- Scroll FEEL on non-macOS mice (line-mode wheel deltas: normalize
  deltaMode -- pixel/line/page -- to points in the listener).
- No off-main-thread compositing: measure a long-list scroll on the site
  sample; the tick must stay one transform write (memo boundaries make the
  rebuild cheap; if a scroll tick re-lays-out the world, that is a bug in
  the change, not a cost of the design).
- Browser-native niceties (find-in-page scrolling into clipped content,
  fragment scrolling, scroll accessibility) degrade; noted for the
  semantics/a11y design to pick up.

## Verification

- Headless: existing scroll scenario (already exercises the shared path).
- Web live: the un-gated scroll scenario passes in headless Chrome on BOTH
  jsweb and (when task #41 unblocks) wasi-web; expectation counts updated.
- Native live + samples: unchanged behavior (shared-code hoists are
  refactors; the full suite gates them).
- Manual: samples/web-ui or samples/ui/scroll on jsweb -- wheel + trackpad
  flick feel, auto scrollbar appears, horizontal carousel still works.
