# Rich Text Primitive Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add `rich` — a new `ui/widget` primitive rendering one base string with a
list of `(start, end, font-override, color-override, on-click)` spans layered
over it, wrapping and flowing as one unit on both backends — and wire it into
the docs site's `prose`/`note` for inline `` `code` `` spans.

**Architecture:** A new `Rich`/`LRich` pair parallel to the existing
`Text`/`LText`, threaded through every place `widget<a>`/`ltree<a>` is
matched exhaustively (layout, reconcile, map-msg, hit-testing, size). Task 1
lands the full data model, layout math, and hit-testing logic behind a
**deterministic fixed-width test measurer** (already how `ui/test.kk` proves
`Text`'s wrap/hit behavior without touching a real text engine), with a
correctness-preserving but visually-incomplete paint fallback (spans ignored,
base style only) on both backends so the whole tree keeps compiling and
passing its existing suite throughout. Tasks 2 and 3 replace that fallback
with real multi-run rendering per backend, independently, once the shared
data model is proven. Task 4 wires it into the docs site.

**Tech Stack:** Koka, `ui/widget`'s existing constraints-based layout model,
Impeller's `ImpellerParagraphBuilder` (native), plain multi-`<span>` HTML
(web).

## Global Constraints

- Spans index by **grapheme offset** into `content` (the convention
  `.count`/`.pad-right` already use elsewhere in this codebase — see
  `samples/ui/site/blocks.kk`'s `code-block`), not byte offset.
- Overlapping spans are undefined behavior for this version — callers
  (the backtick parser, later a tokenizer) are expected to produce
  non-overlapping ranges.
- Color is a pure paint-time attribute; it never affects wrap geometry.
  Only font overrides participate in measurement.
- No inline widget spans (Flutter's `WidgetSpan`) this round — see
  `docs/superpowers/specs/2026-08-01-rich-text-primitive-design.md`'s
  non-goals. Don't add one speculatively.
- Every task must leave `koka --target=jsweb -c` AND the native impeller
  target's `-c` clean (no type errors) — this feature touches files every
  other sample/test in the repo transitively imports, so a broken match
  anywhere blocks everything downstream. Typecheck BOTH targets before
  every commit, not just the one you're actively testing against.
- Native typecheck/smoke command (adjust the KOKA path if your `koka` is
  already on PATH):
  ```bash
  KOKA=/Users/timwhiting/koka/.worktrees/koka-clang-wasm/.stack-work/install/aarch64-osx/f85b4dc81f126d06881fec188dc62cdb96d6f54b1fd1f1051955dc1d51fe411a/9.10.3/bin/koka
  impdir=/Users/timwhiting/koka/.worktrees/koka-clang-wasm/lib/ui/api/impeller
  sdk=$impdir/sdk
  $KOKA --console=raw -c <file.kk> \
    "--ccopts=-I$sdk/include -I$impdir" \
    "--cclib=impeller;impellerhost" \
    "--cclinkopts=-L$sdk/lib -L$impdir -Wl,-rpath,$sdk/lib -Wl,-rpath,$impdir"
  ```
  Swap `-c <file.kk>` for `-e <file.kk>` to build-and-run a test/smoke main.
- Web typecheck/smoke command: `koka --target=jsweb --console=raw -c
  <file.kk>` (swap `-c` for `-e` to build-and-run; the produced `.mjs` runs
  via `node`).

---

### Task 1: Core data model, layout, hit-testing (backend-agnostic)

**Files:**
- Modify: `lib/ui/widget.kk` — `text-span<a>` struct, `Rich`/`LRich`
  constructors, `rich`/`font/rich` builders, `measure-rich` effect op,
  `layout`'s `Rich` case, `reconcile`'s `LRich` case, `map-msg`'s `Rich`
  case, `size`'s `LRich` case, `hit-go`'s `LRich` case.
- Modify: `lib/ui/test.kk` — deterministic `measure-rich` handler in
  `with-test-measure`, an `LRich` case in `collect-texts` (so `t.texts(...)`
  sees rich content, matching `LText`'s inclusion).
- Modify: `lib/ui/api/impeller/backend.kk` — minimal `LRich` case in
  `paint-at`: paint the BASE text only (spans ignored), so the native
  build stays green. Task 2 replaces this.
- Modify: `lib/ui/api/web/backend.kk` — minimal `LRich` case in
  `node-html`: emit the base text only (spans ignored), so the web build
  stays green. Task 3 replaces this.
- Test: `test/ui/rich-text.kk` (new)

**Interfaces:**
- Produces:
  `pub struct text-span<a>( start : int, end : int, font : maybe<font> = Nothing, color : maybe<color> = Nothing, on-click : maybe<a> = Nothing )`
  `pub fun size/rich<a>( content : string, size : float64 = 15.0, color : color = default-fg, spans : list<text-span<a>> = [], wrap : bool = True, ?key : key ) : widget<a>`
  `pub fun font/rich<a>( content : string, font : font, color : color = default-fg, spans : list<text-span<a>> = [], wrap : bool = True, ?key : key ) : widget<a>`
  `pub effect fun measure-rich( content : string, base-font : font, spans : list<(int,int,maybe<font>)>, max-w : float64, wrap : bool ) : (float64, float64, list<list<(float64,float64,float64,float64)>>)`
  (added as a new `fun` line inside the existing `pub effect measure` block)
- Consumes: nothing from other tasks (this is the foundation task).

- [ ] **Step 1: Read the exact current shape of every site this task touches**

Read these five spots in `lib/ui/widget.kk` before writing anything — the
step code below assumes these exact shapes and will not line up if the
file has drifted:
- `pub type ltree<a>` (the full constructor list, currently ending at
  `LImage`)
- `pub fun size<msg>( ^t : ltree<msg> )` (the exhaustive `(w,h)` accessor)
- `pub fun layout<msg>( w : widget<msg>, c : constraints )`'s `Text` case
- `pub fun reconcile<msg>( old : ltree<msg>, spec : widget<msg>, c : constraints )`'s
  `LText` case (note: `reconcile`'s OUTER match on `old` has **no**
  trailing wildcard — every `ltree` constructor needs an explicit arm or
  the file fails to compile non-exhaustive)
- `pub fun map-msg<a,b>( w : widget<a>, f : a -> b )`'s `Text` case
- `fun hit-go<msg>( t : ltree<msg>, px, py, x, y )`'s `LText -> Nothing`
  case, and the `pub type hit<a>` variant list (`HitMsg` is what a
  clickable span resolves to)

- [ ] **Step 2: Add `text-span` and the `Rich`/`LRich` constructors**

In `lib/ui/widget.kk`, right after the `pub fun code<msg>(...)` block
(the existing single-line-mono constructor, so `rich` sits next to its
siblings):

```koka
// a styled sub-range of a `rich` widget's content, by GRAPHEME offset
// (the same convention `.count`/`.pad-right` use elsewhere) -- `Nothing`
// on `font`/`color` inherits the base style; `on-click` makes just this
// span a click target, resolved by `hit-go`'s `LRich` case below even
// when the span's text wraps across a line break (its resolved rects,
// plural, come from `measure-rich`).
pub struct text-span<a>
  start    : int
  end      : int
  font     : maybe<font> = Nothing
  color    : maybe<color> = Nothing
  on-click : maybe<a> = Nothing
```

In the `pub type widget<a>` block, add a `Rich` constructor right after
the existing `Text` constructor line:

```koka
  Rich( owner : int32, content : string, base-font : font, base-color : color,
        spans : list<text-span<a>>, wrap : bool )
```

In the `pub type ltree<a>` block, add `LRich` right after `LText`:

```koka
  LRich( owner : int32, content : string, base-font : font, base-color : color,
         spans : list<text-span<a>>, wrap : bool, w : float64, h : float64,
         span-rects : list<(int, list<(float64,float64,float64,float64)>)> )
    // span-rects: (index into `spans`, that span's resolved rect(s) relative
    // to this node's own origin -- more than one rect iff the span's text
    // wraps across a line break)
```

Add the builder functions right after `size/text`/`font/text`:

```koka
pub fun size/rich<a>( content : string, size : float64 = 15.0, color : color = default-fg,
                      spans : list<text-span<a>> = [], wrap : bool = True, ?key : key ) : widget<a>
  Rich(?key.key-id.int32, content, sans(size), color, spans, wrap)

pub fun font/rich<a>( content : string, font : font, color : color = default-fg,
                      spans : list<text-span<a>> = [], wrap : bool = True, ?key : key ) : widget<a>
  Rich(?key.key-id.int32, content, font, color, spans, wrap)
```

- [ ] **Step 3: Extend the `measure` effect**

In the `pub effect measure` block (right under `fun measure-text(...)`),
add:

```koka
  fun measure-rich( content : string, base-font : font, spans : list<(int,int,maybe<font>)>,
                    max-w : float64, wrap : bool ) : (float64, float64, list<list<(float64,float64,float64,float64)>>)
```

`spans` carries `(start, end, font-override)` for EVERY span, in the same
order as `text-span`'s own `spans` list (a `Nothing` override still needs
its slot so the returned rect list lines up positionally) — this keeps
the effect signature color-free per the Global Constraints while staying
a straight zip against the widget's own `spans` list, no filtering or
re-indexing required on either side of the call.

- [ ] **Step 4: `layout`'s `Rich` case**

In `pub fun layout<msg>`, right after the `Text` case:

```koka
    Rich(o, content, bf, bc, spans, wrap) ->
      val span-args = spans.map(fn(s) (s.start, s.end, s.font))
      val (tw, th, rects) = measure-rich(content, bf, span-args, if wrap then c.max-w else unbounded-w, wrap)
      val indexed-rects = spans.map-indexed(fn(i, _) i).zip(rects)
      LRich(o, content, bf, bc, spans, wrap, clamp-w(c, tw), clamp-h(c, th), indexed-rects)
```

- [ ] **Step 5: `reconcile`'s `LRich` case**

In `pub fun reconcile<msg>`'s outer `match old`, add (this MUST be
present — the outer match has no wildcard):

```koka
    LRich(_, _, _, _, _, _, _, _, _) ->
      match spec
        Rich(_, _, _, _, _, _) -> spec.layout(c)   // no fast path yet -- always relayout
        _ -> spec.layout(c)
```

(A same-content fast path that skips remeasuring is a reasonable follow-up
once `rich` is proven in real use — not required for this plan; leaving it
out only costs perf, not correctness, since `spec.layout(c)` is always
correct.)

- [ ] **Step 6: `map-msg`'s `Rich` case**

In `pub fun map-msg<a,b>`, right after the `Text` case:

```koka
    Rich(o, content, bf, bc, spans, wrap) ->
      Rich(o, content, bf, bc, spans.map(fn(s) s(on-click = s.on-click.map(f))), wrap)
```

- [ ] **Step 7: `size`'s `LRich` case**

In `pub fun size<msg>`, right after the `LText` case:

```koka
    LRich(_, _, _, _, _, _, w, h, _) -> (w, h)
```

- [ ] **Step 8: `hit-go`'s `LRich` case**

In `fun hit-go<msg>`, replace the existing bare `LText -> Nothing` line
with (leaving `LText -> Nothing` as-is right above it — `Text` still has
no click target of its own) an added case right after it:

```koka
    LText -> Nothing
    LImage -> Nothing
    LRich(_, _, _, _, spans, _, w, h, rects) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing
      else
        val hit-span = rects.find fn(entry)
          val (_, span-rects) = entry
          span-rects.any(fn(r) val (rx,ry,rw,rh) = r
                                px >= x + rx && px <= x + rx + rw && py >= y + ry && py <= y + ry + rh)
        match hit-span
          Just((idx, _)) ->
            match spans.drop(idx).head
              Just(s) -> s.on-click.map(HitMsg)
              Nothing -> Nothing
          Nothing -> Nothing
```

(`list<a>`'s `.head` returns `maybe<a>`; if this codebase's `std/core/list`
doesn't export `head` under that exact name, use
`spans.drop(idx).map(fn(s) s.fst)` — check `lib/std/core/list.kk` for the
exact accessor and adjust; the intent is "the span at position `idx`".)

- [ ] **Step 9: Typecheck and fix every remaining non-exhaustive match**

Run the native typecheck command (Global Constraints) against
`lib/ui/api/impeller/backend.kk` and the jsweb one against
`lib/ui/api/web/backend.kk`. Both will fail: `paint-at`/`node-html` are
exhaustive dispatchers over `ltree<a>` with no wildcard, so adding
`LRich` breaks them until Steps 10-11 add a case. You may also see
"non-exhaustive match" warnings/errors in other `ltree`-matching
functions this plan didn't anticipate (candidates: `owner-rect`,
`owner-find-texts`, `scroll-at`, `each-scroll`, `drag-list`, `drop-list`
— most of these already have a trailing `_ -> Nothing`/`_ -> []`
wildcard and DON'T need a change, since `LRich` behaving like a leaf
falls through correctly, but verify each one the compiler actually
flags). For any function the compiler flags that you haven't already
handled, add the smallest correct case: if the function's fallback for
`LText`/`LImage` (leaf nodes) is `Nothing`/`[]`/pass-through, give
`LRich` the same treatment.

- [ ] **Step 10: Minimal native paint fallback (keeps the build green)**

In `lib/ui/api/impeller/backend.kk`'s `paint-at`, add (right after the
`LText` case):

```koka
    LRich(_, content, base-font, base-color, _, wrap, w0, _, _) ->
      // spans ignored for now -- Task 2 replaces this with real multi-run
      // painting via the rich-* externs
      b.draw-paragraph(paragraph(content, base-font.size, base-color, if wrap then w0 else unbounded-w), x, y)
```

- [ ] **Step 11: Minimal web paint fallback (keeps the build green)**

In `lib/ui/api/web/backend.kk`'s `node-html`, add (right after the
`LText` case):

```koka
    LRich(_, content, base-font, base-color, _, wrap, w0, h0, _) ->
      // spans ignored for now -- Task 3 replaces this with real
      // multi-span painting
      val flow = if wrap then ";white-space:normal;overflow:hidden"
                 else ";line-height:" ++ px(h0) ++ ";white-space:pre;overflow:hidden"
      html/elem("div",
        [style(pos-style(x, y, w0 + 1.0, h0)
               ++ ";font:" ++ base-font.css-font
               ++ ";color:" ++ base-color.to-css
               ++ flow ++ ";pointer-events:none")] ++ extra,
        [html/text(content)])
```

- [ ] **Step 12: Deterministic `measure-rich` for headless tests**

In `lib/ui/test.kk`'s `with-test-measure`, add a `measure-rich` handler
using the SAME fixed-width character model `measure-text` already uses
(`cw = font.size * 0.6`, `lh = font.size * 1.25`), computing per-span
rects from that model:

```koka
  with fun measure-rich( content : string, base-font : font, spans : list<(int,int,maybe<font>)>,
                         max-w : float64, wrap : bool )
    // every span here uses base-font's cw for simplicity (a real
    // per-span-width model isn't needed to prove wrap/hit-test LOGIC,
    // only that rects come out non-overlapping and geometrically sane) --
    // the font override is accepted for signature parity with the real
    // handlers but unused by this fixed-width model
    val cw = base-font.size * 0.6
    val lh = base-font.size * 1.25
    val n  = content.count
    val per = if wrap then (max-w / cw).int.max(1) else n.max(1)   // chars per line
    fun rect-for( start : int, end : int ) : list<(float64,float64,float64,float64)>
      // walk [start,end) in per-line chunks, one rect per line it touches
      fun go( pos : int, acc : list<(float64,float64,float64,float64)> ) : list<(float64,float64,float64,float64)>
        if pos >= end then acc.reverse
        else
          val line = pos / per
          val line-end = ((line + 1) * per).min(end)
          val x = (pos % per).float64 * cw
          val w = (line-end - pos).float64 * cw
          val y = line.float64 * lh
          go(line-end, Cons((x, y, w, lh), acc))
      go(start, [])
    val lines = if n == 0 then 1 else (n + per - 1) / per
    val total-w = if wrap then max-w else n.float64 * cw
    val total-h = lines.float64 * lh
    val rects = spans.map(fn(sp) val (s, e, _) = sp; rect-for(s, e))
    (total-w, total-h, rects)
```

This now matches Steps 3-4's `measure-rich` signature exactly (one
`(start, end, font-override)` entry per span, in `spans` order) — the
real backend handlers Tasks 2-3 add must match it too.

- [ ] **Step 13: Write `test/ui/rich-text.kk`**

```koka
// `rich`'s wrap geometry and click-hit-testing, proven against
// `ui/test`'s deterministic fixed-width measurer (the same one `Text`'s
// own wrap/hit behavior is proven against) -- no real backend text
// engine involved, matching every other layout-math test in this suite.
//
// The clicked span's name is rendered back into a plain `text` widget
// (scoped "last") so the scenario can assert on it via `t.texts("last")`
// the same way other headless tests in this suite read back app state --
// through what's actually painted, not by reaching into `model` directly.
module rich-text

import std/async
import std/num/float64
import ui/widget
import ui/test

pub struct model( last : string = "none" )
pub type msg
  Clicked( which : string )

pub fun view( m : model, key : key ) : <keytree,uistate,scene<msg>,ioc> widget<msg>
  column([
    fixed(
      rich("plain aaaa bbbb", 10.0, spans = [
        Text-span(6, 10, on-click = Just(Clicked("aaaa"))),
      ], wrap = True, ?key = scope("r")),
      width = Just(24.0) ),   // narrow enough to force a wrap mid-content
    text(m.last, 10.0, ?key = scope("last")),
  ])

pub fun update( m : model, msg : msg ) : dispatch<msg> model
  match msg
    Clicked(which) -> m(last = which)

pub fun rich-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  t.settle()
  check-eq("starts unclicked", t.texts("last"), ["none"])
  // "plain aaaa bbbb" at cw=6.0 (10.0 * 0.6), 24px width -> 4 chars/line:
  // "plai" / "n aa" / "aa b" / "bbb" / "b" -- span [6,10) ("aaaa") straddles
  // that wrap, so it must resolve to clicks at BOTH its line positions.
  t.click(10.0, 4.0)    // inside line 1's slice of the span ("aa", chars 6-7)
  t.settle()
  check-eq("click on the span's first-line slice resolves", t.texts("last"), ["aaaa"])
  (t.emit)(Clicked("none"))   // reset between assertions
  t.settle()
  t.click(6.0, 16.0)    // inside line 2's slice of the span ("aa", chars 8-9)
  t.settle()
  check-eq("click on the span's wrapped-continuation slice also resolves", t.texts("last"), ["aaaa"])

pub fun main()
  test-scenarios("rich bubbles clicks through a wrapped span", Model(), view, update,
                 [("rich", rich-scenario)])
```

The exact click coordinates above (`(10.0, 4.0)` and `(6.0, 16.0)`) are
worked out from the deterministic measurer's geometry (`cw = 6.0`,
`lh = 10.0 * 1.25 = 12.5`) but VERIFY them against Step 12's actual
`rect-for` output before trusting them — run the scenario, and if a
check fails on coordinates rather than on click-resolution logic, print
the resolved `span-rects` (e.g. via a temporary `println` in `layout`'s
`Rich` case) to find the real rects and adjust the click points, the
same debugging approach used earlier this session to root-cause the
sidebar's `intrinsic-width` bug.

This step's test sketch is intentionally incomplete on the assertion
(the comment says so) — before moving on, extend `model`/`update` to
actually record the last-clicked span name and assert it, for BOTH the
first-line and wrapped-continuation click points, matching the design's
"clickable while wrapped" requirement. Do not leave the placeholder
assertion (`is-empty.not`) in the committed test.

- [ ] **Step 14: Run it, both targets**

```bash
koka --target=jsweb --console=raw -e test/ui/rich-text.kk
node .koka/v3.2.7/js-debug-*/test_ui_rich_dash_text__main.mjs
```
and the native command from Global Constraints with `-e` instead of `-c`.
Expected: all checks pass.

- [ ] **Step 15: Full-suite regression check**

Run every existing test under `test/ui/` (the same list Task 5 of the
"docs site feedback" work re-ran this session — `anchor-scroll`,
`async-boundary`, `async-store`, `basic`, `clip-hit`,
`intrinsic-scroll-row`, `lazy-oversize`, `lazy`, `mat4`, `nested-scroll`,
`retain`, `selector`, `state-channels`, `transform-hit`, `wheel-bubble`,
`windows`) plus `samples/ui/site`'s smoke suite, on jsweb. All must still
pass — this task touches files every one of them transitively depends on.

- [ ] **Step 16: Commit**

```bash
git add lib/ui/widget.kk lib/ui/test.kk lib/ui/api/impeller/backend.kk \
        lib/ui/api/web/backend.kk test/ui/rich-text.kk
git commit -m "ui: add the rich widget's core data model, layout, and hit-testing"
```

---

### Task 2: Native (Impeller) full multi-run rendering

**Files:**
- Modify: `lib/ui/api/impeller/shim.c` — `rich-*` incremental builder
  externs.
- Modify: `lib/ui/api/impeller/impeller.kk` — Koka wrappers for the new
  externs, plus a `rich-hit`/`rich-rects` glyph-info-based function.
- Modify: `lib/ui/api/impeller/backend.kk` — replace Task 1's minimal
  `LRich` paint case with real multi-run painting; add a real
  (non-test) `measure-rich` handler.

**Interfaces:**
- Consumes: `LRich`'s fields (Task 1); `text-span<a>` (Task 1).
- Produces: nothing new for later tasks — this is a leaf backend task.

- [ ] **Step 1: Read the existing single-run paragraph code end to end**

Read `lib/ui/api/impeller/impeller.kk`'s `paragraph`/`draw-paragraph`
(around lines 385-412) and `shim.c`'s `kk_imp_paragraph_uncached`
(around line 745, just above `kk_imp_paragraph` at line 777 seen during
planning) in full — the new `rich-*` externs mirror this shape (style,
add text, build) but split across multiple calls instead of one.

- [ ] **Step 2: Add the incremental builder externs to `shim.c`**

Add, right after `kk_imp_paragraph`'s existing helpers:

```c
static kk_box_t kk_imp_rich_begin(kk_context_t* ctx) {
  ImpellerParagraphBuilder pb = ImpellerParagraphBuilderNew(kk_imp_typo());
  return kk_cptr_raw_box(&kk_imp_para_builder_free, (void*)pb, ctx);
}

static kk_unit_t kk_imp_rich_push_style(kk_box_t builder, double size,
                                        double r, double g, double b, double a,
                                        kk_context_t* ctx) {
  ImpellerParagraphBuilder pb =
      (ImpellerParagraphBuilder)kk_cptr_raw_unbox_borrowed(builder, ctx);
  ImpellerParagraphStyle style = ImpellerParagraphStyleNew();
  ImpellerColor c = { (float)r, (float)g, (float)b, (float)a };
  ImpellerPaint fg = ImpellerPaintNew();
  ImpellerPaintSetColor(fg, &c);
  ImpellerParagraphStyleSetForeground(style, fg);
  ImpellerParagraphStyleSetFontSize(style, (float)size);
  ImpellerParagraphBuilderPushStyle(pb, style);
  ImpellerPaintRelease(fg);
  ImpellerParagraphStyleRelease(style);
  kk_box_drop(builder, ctx);
  return kk_Unit;
}

static kk_unit_t kk_imp_rich_add_text(kk_box_t builder, kk_string_t text, kk_context_t* ctx) {
  ImpellerParagraphBuilder pb =
      (ImpellerParagraphBuilder)kk_cptr_raw_unbox_borrowed(builder, ctx);
  kk_ssize_t len;
  const char* cbuf = kk_string_cbuf_borrow(text, &len, ctx);
  ImpellerParagraphBuilderAddText(pb, (const uint8_t*)cbuf, (uint32_t)len);
  kk_string_drop(text, ctx);
  kk_box_drop(builder, ctx);
  return kk_Unit;
}

static kk_unit_t kk_imp_rich_pop_style(kk_box_t builder, kk_context_t* ctx) {
  ImpellerParagraphBuilder pb =
      (ImpellerParagraphBuilder)kk_cptr_raw_unbox_borrowed(builder, ctx);
  ImpellerParagraphBuilderPopStyle(pb);
  kk_box_drop(builder, ctx);
  return kk_Unit;
}

static kk_box_t kk_imp_rich_build(kk_box_t builder, double width, kk_context_t* ctx) {
  ImpellerParagraphBuilder pb =
      (ImpellerParagraphBuilder)kk_cptr_raw_unbox_borrowed(builder, ctx);
  ImpellerParagraph para = ImpellerParagraphBuilderBuildParagraphNew(pb, (float)width);
  kk_box_drop(builder, ctx);
  g_live_para++;
  return kk_cptr_raw_box(&kk_imp_para_free, (void*)para, ctx);
}
```

You'll need a `kk_imp_para_builder_free` release function
(`ImpellerParagraphBuilderRelease`) matching the pattern
`kk_imp_para_free` already uses right above `kk_imp_paragraph_uncached`
— add it alongside. Note: unlike `kk_imp_paragraph`, these are NOT
cached (`kk_imp_paragraph`'s cache key is the whole text+style+width
combination, cheap to hash for one run; hashing an arbitrary-length span
list isn't worth it for a first version) — every `rich` layout/paint
rebuilds its paragraph. Revisit if profiling shows this matters.

- [ ] **Step 3: Wrap the externs in `impeller.kk`**

```koka
pub value struct rich-builder(obj : any)

extern rich-begin-raw() : ioc any
  c "kk_imp_rich_begin"
pub fun rich-begin() : ioc rich-builder
  Rich-builder(rich-begin-raw())

extern rich-push-style-raw(b : any, size : float64, r : float64, g : float64, b2 : float64, a : float64) : ioc ()
  c "kk_imp_rich_push_style"
pub fun push-style(b : rich-builder, size : float64, color : color) : ioc ()
  rich-push-style-raw(b.obj, size, color.r, color.g, color.b, color.a)

extern rich-add-text-raw(b : any, text : string) : ioc ()
  c "kk_imp_rich_add_text"
pub fun add-text(b : rich-builder, text : string) : ioc ()
  rich-add-text-raw(b.obj, text)

extern rich-pop-style-raw(b : any) : ioc ()
  c "kk_imp_rich_pop_style"
pub fun pop-style(b : rich-builder) : ioc ()
  rich-pop-style-raw(b.obj)

extern rich-build-raw(b : any, width : float64) : ioc any
  c "kk_imp_rich_build"
pub fun build(b : rich-builder, width : float64 = 10000.0) : ioc paragraph
  Paragraph(rich-build-raw(b.obj, width))
```

- [ ] **Step 4: Drive it from `backend.kk`'s real paint case**

Replace Task 1's minimal `LRich` paint case with:

```koka
    LRich(_, content, base-font, base-color, spans, wrap, w0, _, _) ->
      val pb = rich-begin()
      pb.push-style(base-font.size, base-color)
      // walk `content` left to right, opening/closing a pushed style at
      // each span boundary and falling back to the base style in the gaps
      fun emit( pos : int, remaining : list<text-span<msg>> ) : ioc ()
        match remaining
          Nil -> pb.add-text(content.slice.advance(pos).truncate.string)
          Cons(s, rest) ->
            if s.start > pos then pb.add-text(content.slice.advance(pos).truncate.extend(s.start - pos).string)
            pb.push-style(s.font.default(base-font).size, s.color.default(base-color))
            pb.add-text(content.slice.advance(s.start).truncate.extend(s.end - s.start).string)
            pb.pop-style()
            emit(s.end, rest)
      emit(0, spans)
      pb.pop-style()
      b.draw-paragraph(pb.build(if wrap then w0 else unbounded-w), x, y)
```

- [ ] **Step 5: Real `measure-rich` via glyph info**

Add to `backend.kk`'s effect handler block (alongside the existing
`measure-text` handler): build the SAME multi-run paragraph as Step 4
(measurement and paint build equivalent structures — a real dedup/cache
between them is a reasonable follow-up, not required here), read its
`width`/`height` the way `measure-web`/`measure-native` already do for
`measure-text`, then resolve each span's rect(s) via
`ImpellerParagraphCreateGlyphInfoAtCodeUnitIndexNew` at the span's
`start` and `end` boundaries plus `ImpellerGlyphInfoGetGraphemeClusterBounds`
— when a span's start and end glyphs report different line origins (Y
differs), the span crosses a wrap; walk the code-unit indices between
them to find the line-break boundary and split into two rects the same
way Task 1's deterministic test measurer's `rect-for` does (one rect per
line the span touches). Expose this as new `impeller.kk`
functions (`glyph-bounds-at`, mirroring `height`/`width`'s wrapper
pattern) before wiring it into `backend.kk`'s handler.

- [ ] **Step 6: Typecheck, run `test/ui/rich-text.kk` and the docs site smoke suite on native**

Both from Global Constraints, `-c` then `-e`. Also re-run the FULL
`test/ui/` suite (Task 1 Step 15's list) on native this time (Task 1
only required it on jsweb) — this task touches the native backend
specifically.

- [ ] **Step 7: Commit**

```bash
git add lib/ui/api/impeller/shim.c lib/ui/api/impeller/impeller.kk \
        lib/ui/api/impeller/backend.kk
git commit -m "ui: native multi-run rich-text rendering via Impeller's incremental paragraph builder"
```

---

### Task 3: Web full multi-run rendering

**Files:**
- Modify: `lib/web-ui/api/jsweb/dom.kk` and `lib/web-ui/api/jsweb/dom.js`
  (and the `wasiweb` mirrors, `lib/web-ui/api/wasiweb/dom.kk`/`.js`, if
  this project keeps them in lockstep — check whether `wasiweb`'s
  `measure-text-width`/`measure-text-box-height` externs are literally
  duplicated from `jsweb`'s or share a file; match whatever the existing
  pattern is) — `measure-rich-*` extern.
- Modify: `lib/ui/api/web/backend.kk` — replace Task 1's minimal `LRich`
  paint case with real multi-span painting; real `measure-rich` handler.

**Interfaces:**
- Consumes: `LRich`'s fields (Task 1); `text-span<a>` (Task 1).
- Produces: nothing new for later tasks.

- [ ] **Step 1: Read the existing multi-node emission pattern**

Read `lib/ui/api/web/backend.kk`'s `node-html`'s `LFlex`/`LLayer` cases
(they already emit a LIST of child nodes into one parent — the same
shape `LRich`'s spans need, just with `<span>` instead of positioned
`<div>`s) and `to-css`/`css-font` (used to build each span's inline
style string).

- [ ] **Step 2: Real paint case in `backend.kk`**

Replace Task 1's minimal `LRich` case with:

```koka
    LRich(_, content, base-font, base-color, spans, wrap, w0, h0, _) ->
      fun span-html( pos : int, remaining : list<text-span<msg>> ) : list<html<msg>>
        match remaining
          Nil ->
            if pos < content.count
              then [html/elem("span", [style(";font:" ++ base-font.css-font ++ ";color:" ++ base-color.to-css)],
                     [html/text(content.slice.advance(pos).truncate.string)])]
              else []
          Cons(s, rest) ->
            val gap = if s.start > pos
              then [html/elem("span", [style(";font:" ++ base-font.css-font ++ ";color:" ++ base-color.to-css)],
                     [html/text(content.slice.advance(pos).truncate.extend(s.start - pos).string)])]
              else []
            val f = s.font.default(base-font)
            val c = s.color.default(base-color)
            val extra-attrs = match s.on-click
              Just(msg) -> [on-click(fn(_) msg, evch)]   // check node-html's existing click-attr helper name/shape and match it exactly
              Nothing -> []
            val span-node = [html/elem("span", [style(";font:" ++ f.css-font ++ ";color:" ++ c.to-css)] ++ extra-attrs,
                     [html/text(content.slice.advance(s.start).truncate.extend(s.end - s.start).string)])]
            gap ++ span-node ++ span-html(s.end, rest)
      val flow = if wrap then ";white-space:normal;overflow:hidden" else ";white-space:pre;overflow:hidden"
      html/elem("div", [style(pos-style(x, y, w0 + 1.0, h0) ++ flow)] ++ extra, span-html(0, spans))
```

Check how existing clickable nodes (e.g. `LBox`'s `on.click`) wire their
DOM click listener in this same function — the `extra-attrs`/`on-click`
line above is a placeholder shape; replace it with whatever the real
helper/attr constructor already used for click-to-message wiring in this
file is named, so span clicks go through the SAME event path (not a new
one).

- [ ] **Step 3: `measure-rich` JS extern**

In `lib/web-ui/api/jsweb/dom.kk`, mirroring `measure-text-box-height`:

```koka
pub extern measure-rich-box(content : string, base-css-font : string,
                            span-starts : vector<int>, span-ends : vector<int>, span-css-fonts : vector<string>,
                            max-w : float64, wrap : bool) : ioc (float64, float64, vector<vector<float64>>)
  js "kk_dom_measure_rich_box"
```

(Check whether this codebase's Koka-to-JS extern binding supports
returning a NESTED vector/tuple this shape directly, or whether the
existing externs only return scalars/flat tuples — `measure-text-box-height`
returns one `float64`. If nested vectors aren't supported cleanly, flatten
the return to parallel vectors instead: total width, total height, then
one flat vector of `(x,y,w,h)` quads per span in order, with a companion
vector of how many rects each span produced, and reassemble the grouping
on the Koka side.)

In `lib/web-ui/api/jsweb/dom.js`, alongside `kk_dom_measure_text_box_height`:
build a hidden container div with one `<span>` per entry (mirroring Step
2's paint structure exactly, so measured geometry matches painted
geometry), force layout, and read back the container's
`getBoundingClientRect()` plus each span's `getClientRects()` (which
already returns one rect PER LINE a span occupies when it wraps — no
glyph-index math needed on this backend, unlike native).

- [ ] **Step 4: Wire it into `backend.kk`'s real `measure-rich` handler**

Same shape as `measure-web`'s existing `measure-text` handler — call the
Step 3 extern, reshape its return into the `(float64, float64,
list<list<(float64,float64,float64,float64)>>)` shape `measure-rich`'s
effect signature expects.

- [ ] **Step 5: Typecheck, run `test/ui/rich-text.kk` and the docs site smoke suite on jsweb**

- [ ] **Step 6: Commit**

```bash
git add lib/web-ui/api/jsweb/dom.kk lib/web-ui/api/jsweb/dom.js \
        lib/ui/api/web/backend.kk
git commit -m "ui: web multi-span rich-text rendering via native DOM reflow"
```

---

### Task 4: Docs-site integration — inline code spans in prose

**Files:**
- Modify: `samples/ui/site/blocks.kk` — backtick-span parser, `prose`/`note`
  call `rich` instead of `paragraph`; remove `drop-backticks`.
- Test: extend `samples/ui/site/smoke.kk`.

**Interfaces:**
- Consumes: `rich`, `text-span` (Task 1); real rendering (Tasks 2-3).

- [ ] **Step 1: Write the backtick-span parser**

In `blocks.kk`, replace `drop-backticks` with:

```koka
// finds `` `...` `` ranges in `s` and returns the STRIPPED string (ticks
// removed) alongside a `text-span` per match, offset-adjusted for the
// characters already removed by earlier matches -- so span offsets are
// correct against the RETURNED string, not the original.
fun parse-code-spans<a>( s : string, mono-font : font ) : (string, list<text-span<a>>)
  val chars = s.list
  fun go( cs : list<char>, out : list<char>, pos : int, in-code : bool,
          code-start : int, spans : list<text-span<a>> ) : (list<char>, list<text-span<a>>)
    match cs
      Nil -> (out.reverse, spans.reverse)
      Cons(c, rest) ->
        if c == '`' then
          if in-code
            then go(rest, out, pos, False, 0, Cons(Text-span(code-start, pos, font = Just(mono-font)), spans))
            else go(rest, out, pos, True, pos, spans)
          else go(rest, Cons(c, out), pos + 1, in-code, code-start, spans)
  val (result-chars, spans) = go(chars, [], 0, False, 0, [])
  (result-chars.string, spans)
```

An unterminated trailing backtick (`in-code` still `True` at `Nil`) is
dropped silently — no span for it, and the opening tick itself was
already excluded from `out`. That's an acceptable degenerate case for
now; note it in the function's own comment rather than special-casing it.

- [ ] **Step 2: Wire `prose`/`note` to it**

```koka
pub fun prose<a>( s : string, ?key : key ) : theme widget<a>
  val (text, spans) = s.parse-code-spans(mono(16.0))
  rich(text, 16.0, theme.fg, spans, wrap = True)

pub fun note<a>( s : string, ?key : key ) : theme widget<a>
  val (text, spans) = s.parse-code-spans(mono(15.0))
  box( rich(text, 15.0, theme.fg, spans, wrap = True), padding = 12.0,
       bg = Just(Fill(theme.surface, 8.0)) )
```

Delete `drop-backticks` entirely (grep the file to confirm nothing else
calls it before removing).

- [ ] **Step 3: Typecheck and run the smoke suite (both targets)**

- [ ] **Step 4: Add a smoke assertion**

In `samples/ui/site/smoke.kk`'s `pure-checks` (or a new headless check
alongside it), assert `parse-code-spans("the `padding` param", mono(16.0))`
returns `("the padding param", [Text-span(4, 11, font = Just(mono(16.0)))])`
— pin the exact offsets so a future refactor can't silently shift them.

- [ ] **Step 5: Visual verification**

Build for jsweb, serve, screenshot a reference page with backtick-heavy
prose (e.g. `reference-widgets`, whose `box`/`row, column, spacer`
descriptions have several `` `code` `` spans) via headless Chrome at
900px. Confirm inline code words render in the mono font distinctly
from surrounding prose, with no literal backtick characters.

- [ ] **Step 6: Commit**

```bash
git add samples/ui/site/blocks.kk samples/ui/site/smoke.kk
git commit -m "site: prose renders backtick spans as real inline code via rich, not stripped"
```

---

### Task 5: Full regression pass

**Files:** none (verification only).

- [ ] **Step 1: Typecheck every `.kk` file this plan touched, both targets**

`lib/ui/widget.kk`, `lib/ui/test.kk`, `lib/ui/api/impeller/backend.kk`,
`lib/ui/api/impeller/impeller.kk`, `lib/ui/api/web/backend.kk`,
`lib/web-ui/api/jsweb/dom.kk`, `samples/ui/site/blocks.kk`, plus
`samples/ui/site/main.kk` (pulls the whole site's transitive graph).

- [ ] **Step 2: Run the full `test/ui/` suite, both targets**

The list from Task 1 Step 15, on BOTH jsweb and native this time.

- [ ] **Step 3: Run the docs-site smoke suite, both targets**

- [ ] **Step 4: Screenshot every reference/how-to/tutorial page at 900px in headless Chrome**

Confirm nothing overflows 900px width (this rollout's recurring failure
mode per `docs/ui/design-notes.md`) and that inline code spans render
correctly on every page, not just the one Task 4 spot-checked.

- [ ] **Step 5: Report any regressions found back through the fix loop before considering this plan done**
