// Regression test for the REAL web (jsweb) `rich`-text measurement path:
// `lib/web-ui/api/jsweb/dom.js`'s `kk_dom_measure_rich_box`, the extern
// behind `ui/api/web/backend.kk`'s `measure-rich-web` handler (task 3 of
// the rich-text-primitive plan).
//
// `test/ui/rich-text.kk` proves `rich`'s wrap/hit-test geometry against
// `ui/test`'s DETERMINISTIC MOCK measurer -- it never touches this file, or
// the real DOM-per-span structure `ui/api/web/backend.kk`'s `LRich` paint
// case builds. This test exercises the ACTUAL extern instead, run under
// plain node (no browser needed): `document`/`getBoundingClientRect`/
// `getClientRects` are replaced by a small fixed-width stub good enough to
// prove the extern's MARSHALLING logic is correct -- not real typographic
// accuracy (impossible to get from node without a real layout engine), but
// exactly the class of bug this task's review flagged: a `.truncate` used
// without `.extend` silently drops a span's trailing/gap text. The stub's
// deterministic char-width model turns that class of bug into an exact,
// assertable width/rect mismatch (see test 2 below).
//
// Run: `node test/ui/rich-text-web.mjs` (no koka compile needed -- this
// file imports the production dom.js directly). Exits 1 on any failure.

import { kk_dom_measure_rich_box } from "../../lib/web-ui/api/jsweb/dom.js";

// ---- minimal DOM stub: fixed-width monospace layout, good enough to
// exercise real getBoundingClientRect()/getClientRects() call shapes ----
const CW = 7;   // px per character (arbitrary but fixed)
const LH = 16;  // px per line

class FakeElement {
  constructor(tag) {
    this.tagName = tag;
    this.style = {};
    this.children = [];
    this._text = "";
    this.parentNode = null;
    this._charCursor = 0;   // container-only: running char offset of appended children
  }
  get textContent() { return this._text; }
  set textContent(t) { this._text = t; }
  appendChild(child) {
    child._charStart = this._charCursor;
    this._charCursor += child._text.length;
    child._charEnd = this._charCursor;
    child.parentNode = this;
    this.children.push(child);
  }
  removeChild(child) {
    const i = this.children.indexOf(child);
    if (i >= 0) this.children.splice(i, 1);
  }
  _wrapPerLine() {
    if (this.style.whiteSpace === "normal" && this.style.width) {
      return Math.max(1, Math.floor(parseFloat(this.style.width) / CW));
    }
    return null;   // no-wrap: everything on one line
  }
  getBoundingClientRect() {
    const total = this._charCursor;
    const perLine = this._wrapPerLine();
    if (perLine === null) return { left: 0, top: 0, width: total * CW, height: LH };
    const lines = Math.max(1, Math.ceil(total / perLine));
    return { left: 0, top: 0, width: Math.min(total, perLine) * CW, height: lines * LH };
  }
  getClientRects() {
    const parent = this.parentNode;
    if (!parent) return [];
    const s = this._charStart, e = this._charEnd;
    if (s === e) return [];
    const perLine = parent._wrapPerLine();
    if (perLine === null) return [{ left: s * CW, top: 0, width: (e - s) * CW, height: LH }];
    const rects = [];
    let i = s;
    while (i < e) {
      const line = Math.floor(i / perLine);
      const lineEnd = Math.min(e, (line + 1) * perLine);
      rects.push({ left: (i - line * perLine) * CW, top: line * LH, width: (lineEnd - i) * CW, height: LH });
      i = lineEnd;
    }
    return rects;
  }
}

class FakeDocument {
  constructor() { this.body = new FakeElement("body"); }
  createElement(tag) { return new FakeElement(tag); }
}

globalThis.document = new FakeDocument();

// ---- test harness ----
let passed = 0, failed = 0;
function check(name, cond) {
  if (cond) { passed++; }
  else { failed++; console.log("FAIL: " + name); }
}
function checkEq(name, actual, expected) {
  check(name + " (got " + JSON.stringify(actual) + ", expected " + JSON.stringify(expected) + ")",
        JSON.stringify(actual) === JSON.stringify(expected));
}

// 1. span-less `rich`: the whole content is one implicit base-styled run
// (the `Nil` branch of both the paint case and this extern's mirror
// structure) -- must still measure sane, non-empty geometry.
{
  const r = kk_dom_measure_rich_box("hello world", "14px sans", [], [], [], 1.0e7);
  check("span-less: total width is positive", r.fst > 0);
  check("span-less: total height is positive", r.snd > 0);
  checkEq("span-less: no rects, no spans", [r.thd.length, r.field4.length], [0, 0]);
}

// 2. the exact regression this task's review flagged: a span that does NOT
// reach the end of its content string -- trailing text after it must still
// be measured, not silently dropped by a bare `.truncate` (no `.extend`).
// "abcdefghij" (10 chars), span [2,5) ("cde"): 5 chars of tail ("fghij")
// remain after the span. Single line (max-w = unbounded sentinel), so the
// stub's total width is EXACTLY total-chars * CW -- if the tail were
// dropped, this would come up short (7 chars * CW instead of 10).
{
  const r = kk_dom_measure_rich_box("abcdefghij", "14px sans", [2], [5], ["14px sans"], 1.0e7);
  checkEq("trailing text after the last span is NOT dropped: total width reflects all 10 chars",
          r.fst, 10 * CW);
  checkEq("exactly one span, one rect (single line)", [r.thd.length, r.field4.length], [4, 1]);
  // the span's own rect: chars [2,5) -> x = 2*CW, w = 3*CW
  checkEq("span rect lands at the gap-adjusted x/width", [r.thd[0], r.thd[2]], [2 * CW, 3 * CW]);
}

// 3. wrapping: a span whose text straddles a line break reports ONE RECT
// PER LINE it touches (getClientRects()' own contract) -- mirrors
// `test/ui/rich-text.kk`'s mock-measurer scenario (same content/span),
// picking `maxW` so the stub's 4-chars-per-line breakdown lines up exactly:
// "plai"/"n aa"/"aa b"/"bbb" -- span [6,10) ("aaaa") crosses the line0/line1
// boundary at char 8, so it must produce 2 rects.
{
  const maxW = 4 * CW;   // exactly 4 chars/line
  const r = kk_dom_measure_rich_box("plain aaaa bbbb", "14px sans", [6], [10], ["14px sans"], maxW);
  checkEq("wrapped span straddling a line break reports 2 rects", r.field4, [2]);
  checkEq("total quads match the reported count (2 rects * 4 numbers)", r.thd.length, 8);
  check("wrapped total width is capped at max-w", r.fst <= maxW);
  checkEq("wrapped total height spans all 4 lines", r.snd, 4 * LH);
}

console.log("rich-text-web: " + passed + "/" + (passed + failed) + " passed");
if (failed > 0) {
  console.log("rich-text-web: FAILED");
  process.exit(1);
}
