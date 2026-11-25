// Native-only regression for `rich`'s REAL (non-test) measure path --
// `measure-native`/`measure-rich-native` in `lib/ui/api/impeller/backend.kk`
// (both made `pub` specifically so this file can call them directly, no
// window/mount needed: paragraph shaping is CPU-only).
//
// WHY THIS FILE EXISTS: every other file in test/ui/ (including
// rich-text.kk) routes through `ui/test`'s deterministic fixed-width
// measurer, which installs its OWN `measure-rich` handler and never calls
// `measure-rich-native` at all -- so a green `test/ui/` suite proves
// nothing about the real Impeller backend's rich-text path. That gap let a
// text-loss bug ship in `measure-rich-native`'s (and `paint-at`'s LRich
// case's) `Nil` branch: `content.slice.advance(pos).truncate.string` is
// UNCONDITIONALLY "" (`.truncate` zeroes a slice's length; the branch
// never `.extend`s it back), so any `rich` whose last span didn't reach
// the end of the string lost everything after it, and `rich(spans = [])`
// (no spans at all) measured as an EMPTY paragraph. Fixed by dropping the
// stray `.truncate` (see task-2-report.md's "Fix-loop round 1"); this file
// is the regression so it can't silently come back.
//
// UNLIKE every other file in test/ui/, this one needs the Impeller SDK's
// ccopts/cclib/cclinkopts (it links against the real backend) -- see
// lib/ui/api/impeller/backend.kk's brief for the exact flags, e.g.:
//
//   impdir=lib/ui/api/impeller; sdk=$impdir/sdk
//   koka --console=raw -e test/ui/native/rich-measure.kk \
//     "--ccopts=-I$sdk/include -I$impdir" \
//     "--cclib=impeller;impellerhost" \
//     "--cclinkopts=-L$sdk/lib -L$impdir -Wl,-rpath,$sdk/lib -Wl,-rpath,$impdir"
module rich-measure

import std/core/console
import std/core/unsafe
import std/num/float64
import std/num/int32
import ui/widget
import ui/api/impeller/backend

extern native-exit( code : int32 ) : ioc ()
  c inline "(exit((int)(#1)), kk_Unit)"

val passed : ref<global,int> = unsafe-total{ ref(0) }
val failed : ref<global,int> = unsafe-total{ ref(0) }

fun check( label : string, ok : bool ) : ioc ()
  if ok then passed := !passed + 1
  else
    failed := !failed + 1
    println("FAIL: " ++ label)

fun close( a : float64, b : float64, eps : float64 = 0.01 ) : bool
  (a - b).abs < eps

pub fun main()
  val f = sans(14.0)
  val content = "hello world foo"     // 15 codepoints
  val (full-w, full-h) = measure-native(content, f, unbounded-w)

  // 1. a span-less `rich` (no spans at all) must measure IDENTICALLY to
  //    plain `text` -- this is the exact `emit(0, [])` -> `Nil` branch the
  //    critical bug hit immediately, dropping the WHOLE string.
  val (spanless-w, spanless-h, spanless-rects) = measure-rich-native(content, f, [], unbounded-w)
  check("span-less rich matches plain text width", close(spanless-w, full-w))
  check("span-less rich matches plain text height", close(spanless-h, full-h))
  check("span-less rich has no spans to report rects for", spanless-rects.is-nil)
  check("span-less rich is not the empty-string regression (width > 0)", spanless-w > 1.0)

  // 2. a span that does NOT reach the end of the content ("hello" is
  //    codepoints [0,5) of "hello world foo") must still measure the FULL
  //    string -- the `Nil` branch (which emits whatever comes AFTER the
  //    last span) is exactly what carries " world foo" to the builder.
  val (head-w, _) = measure-native("hello", f, unbounded-w)
  val (spanned-w, spanned-h, spanned-rects) = measure-rich-native(content, f, [(0, 5, Nothing)], unbounded-w)
  check("mid-string span: full width matches plain text (tail included)", close(spanned-w, full-w))
  check("mid-string span: full height matches plain text", close(spanned-h, full-h))
  check("mid-string span: wider than the pre-span text alone", spanned-w > head-w)
  check("mid-string span: reports exactly one span's rects", spanned-rects.length == 1)

  // 3. GEOMETRY regression: a span whose text wraps across two lines must
  //    resolve to rects whose Y (vertical/line) coordinate increases from
  //    line to line, and whose X (horizontal-within-line) coordinate stays
  //    close together when both lines start their own word at the line's
  //    left edge. This is the exact shape that would invert if
  //    `lib/ui/api/impeller/shim.c`'s `kk_imp_glyph_bounds_at` ever stopped
  //    swapping `ImpellerGlyphInfoGetGraphemeClusterBounds`'s (x,y) fields
  //    (see that function's "EMPIRICALLY (not per the header comment)"
  //    comment): a regressed swap would make X the field that jumps
  //    between lines (the real vertical/line position leaking into x) and
  //    Y the field that stays flat (the real horizontal position leaking
  //    into y) -- exactly backwards from what's asserted below. Every
  //    OTHER assertion in this file (counts, widths) stays equally green
  //    whether or not x/y are swapped, which is precisely the coverage
  //    gap this section closes.
  val narrow-content = "abc def ghi"
  val word-w = measure-native("abc", f, unbounded-w).fst
  val narrow-w = word-w + 4.0    // fits "abc" alone, not "abc def" -- forces a wrap after word 1
  val (_, wrap-h, wrap-rects) = measure-rich-native(narrow-content, f, [(0, 7, Nothing)], narrow-w)
  check("wrapped span reports exactly one span's rect list", wrap-rects.length == 1)
  val rects = wrap-rects.head([])
  check("wrapped span crosses exactly two lines (two rects)", rects.length == 2)
  match rects
    Cons((x0, y0, _, _), Cons((x1, y1, _, _), Nil)) ->
      check("line 1's rect sits above line 2's rect (y strictly increases)", y1 > y0 + 2.0)
      // small negative slack on y0: a glyph's grapheme-cluster bounds can
      // overshoot slightly above the line box (ascent rounding) -- real
      // font-metrics noise, not a transposition; a swapped-axis regression
      // produces errors orders of magnitude larger than this, not a
      // fraction of a pixel
      check("both rects' y stay within a sane bound (not a huge transposed value)", y0 >= -2.0 && y1 < wrap-h + 4.0)
      check("both rects' x stay near the line start (no line-index leaking into x)", (x1 - x0).abs < 8.0)
      check("x values stay within the narrow width, not a line-height-scale jump", x0 < narrow-w + 4.0 && x1 < narrow-w + 4.0)
    _ ->
      check("wrapped span geometry: unexpected rect shape (expected exactly 2 rects)", False)

  println("rich-measure: " ++ (!passed).show ++ "/" ++ (!passed + !failed).show ++ " passed")
  if !failed > 0 then
    println("rich-measure: FAILED")
    native-exit(1.int32)
