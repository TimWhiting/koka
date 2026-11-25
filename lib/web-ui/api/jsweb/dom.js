/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// DOM fringe for `--target=jsweb`: the compiled Koka runs in the page, so
// these are direct DOM calls -- no externref table, no import object. The
// semantics mirror the wasi-web host runtime (support/wasi-web/web-ui-host.js):
// live value/checked/disabled/selected property sync, declarative drag
// wiring, and the transient current-event exposed while a listener runs.

let $currentEvent = null;

export function kk_dom_get_element_by_id(id) {
  return document.getElementById(id);
}

export function kk_dom_create_element(tag) {
  return document.createElement(tag);
}

export function kk_dom_create_text(s) {
  return document.createTextNode(s);
}

export function kk_dom_append_child(parent, child) {
  parent.appendChild(child);
}

export function kk_dom_remove_child(parent, child) {
  parent.removeChild(child);
}

export function kk_dom_replace_child(parent, fresh, old) {
  parent.replaceChild(fresh, old);
}

export function kk_dom_insert_before(parent, child, anchor) {
  parent.insertBefore(child, anchor);
}

export function kk_dom_set_attribute(el, name, value) {
  // "value" must be the live property, not the attribute, or controlled
  // inputs never update/clear. Guarded so an unchanged value never
  // disturbs the cursor.
  if (name === "value" && "value" in el) {
    if (el.value !== value) el.value = value;
  }
  else if ((name === "checked" || name === "disabled" || name === "selected") && name in el) {
    el[name] = true;
    el.setAttribute(name, value);
  }
  else el.setAttribute(name, value);
  // declarative drag source (html.kk's `draggable(data)`)
  if (name === "data-drag" && !el.kokaDragWired) {
    el.kokaDragWired = true;
    el.addEventListener("dragstart",
      (e) => e.dataTransfer?.setData("text/plain", el.dataset?.drag ?? ""));
  }
}

export function kk_dom_remove_attribute(el, name) {
  if ((name === "checked" || name === "disabled" || name === "selected") && name in el) el[name] = false;
  el.removeAttribute(name);
}

export function kk_dom_set_text(el, s) {
  el.textContent = s;
}

export function kk_dom_get_prop(el, name) {
  if (name === "value") return el && "value" in el ? el.value : "";
  if (name === "hash")  return (el === window || el == null) ? window.location.hash : "";
  if (name === "drag-data") return $currentEvent?.dataTransfer?.getData("text/plain") ?? "";
  return el && typeof el[name] === "string" ? el[name] : "";
}

export function kk_dom_get_num_prop(el, name) {
  const v = el?.[name];
  return typeof v === "number" && Number.isFinite(v) ? v : 0.0;
}

export function kk_dom_current_event() {
  return $currentEvent;
}

// wheel deltas of the CURRENT event, normalized by deltaMode (0 = pixels: x1;
// 1 = lines: x16; 2 = pages: one page = window.innerHeight) and NEGATED: the
// browser reports deltaY > 0 for "wheel down" (scroll toward later content),
// while ui/state's `apply-wheel` (shared with the native/impeller backend,
// whose GLFW scroll callback reports positive = wheel-up) takes delta > 0 =
// wheel-up = reveal earlier content. Negating here keeps that one convention.
function kk_dom_wheel_scale(e, prop) {
  const d = e?.[prop];
  if (typeof d !== "number" || !Number.isFinite(d)) return 0.0;
  const mode = e?.deltaMode ?? 0;
  const scaled = mode === 1 ? d * 16 : mode === 2 ? d * (window.innerHeight || 1) : d;
  return -scaled;
}

export function kk_dom_event_wheel_dx() {
  return kk_dom_wheel_scale($currentEvent, "deltaX");
}

export function kk_dom_event_wheel_dy() {
  return kk_dom_wheel_scale($currentEvent, "deltaY");
}

export function kk_dom_window() {
  return window;
}

export function kk_dom_set_hash(s) {
  window.location.hash = s;
}

// `action` is the compiled Koka listener action (a plain function): the
// runtime's emit, never a user callback (see web-ui/dom).
export function kk_dom_subscribe(el, event, action) {
  const fn = (e) => {
    if (event === "drop") e.preventDefault();
    // right-click drives our own context menu; suppress the browser's
    if (event === "contextmenu") e.preventDefault();
    // one-target-per-click (match native hit-testing): don't let a click also
    // fire an ancestor handler -- notably one acquired during the synchronous
    // re-render this very click triggers (the role-shift double-fire).
    if (event === "click") e.stopPropagation();
    // koka-owned scrolling: suppress the browser's native page/element
    // scroll so ONLY our listener moves the scroll region (needs the
    // {passive:false} registration below to be effective)
    if (event === "wheel") e.preventDefault();
    $currentEvent = e;
    try { action(); }
    finally { $currentEvent = null; }
  };
  // a passive listener cannot preventDefault; "wheel" must be non-passive
  el.addEventListener(event, fn, event === "wheel" ? { passive: false } : undefined);
  let over = null;
  if (event === "drop") {   // a drop target must cancel dragover
    over = (e) => e.preventDefault();
    el.addEventListener("dragover", over);
  }
  return { el, event, fn, over, removed: false };
}

export function kk_dom_unsubscribe(s) {
  if (s == null || s.removed) return;   // idempotent
  s.el.removeEventListener(s.event, s.fn);
  if (s.over) s.el.removeEventListener("dragover", s.over);
  s.removed = true;
}

export function kk_dom_prefers_dark() {
  return !!(window.matchMedia && window.matchMedia("(prefers-color-scheme: dark)").matches);
}

let $measureCtx = null;
export function kk_dom_measure_text_width(content, cssFont) {
  if ($measureCtx === null) $measureCtx = document.createElement("canvas").getContext("2d");
  $measureCtx.font = cssFont;
  return $measureCtx.measureText(content).width;
}

let $measureDiv = null;
export function kk_dom_measure_text_box_height(content, cssFont, maxW) {
  if ($measureDiv === null) {
    $measureDiv = document.createElement("div");
    $measureDiv.style.cssText =
      "position:absolute;visibility:hidden;left:-9999px;top:0;white-space:normal;word-wrap:break-word;box-sizing:border-box";
    document.body.appendChild($measureDiv);
  }
  $measureDiv.style.font = cssFont;
  $measureDiv.style.width = maxW + "px";
  $measureDiv.textContent = content;
  const h = $measureDiv.offsetHeight;
  $measureDiv.textContent = "";   // clear: a lingering string pollutes DOM text scans
  return h;
}

// measure a `rich` widget's runs -- mirrors `ui/api/web/backend.kk`'s
// `LRich` paint case's RUN STRUCTURE (one `<span>` per run: base-styled
// gaps and span-styled runs, interleaved left to right) so measured
// geometry always matches painted geometry. NOT an exact style mirror,
// though: the wrapped-pass container below additionally sets
// `word-wrap:break-word` (`wordWrap = "break-word"`), which the paint case
// does not set (it only sets `white-space:normal;overflow:hidden`) -- a
// pre-existing measure/paint styling asymmetry inherited from how plain
// `Text` already measured/painted before `rich` existed, not introduced
// here and not resolved by this change (see the design spec's known
// follow-ups). `content` is sliced by CODEPOINT offset
// (`Array.from` splits on codepoints, not UTF-16 code units, so surrogate
// pairs/astral characters don't misalign a span's start/end -- the same
// convention `ui/widget`'s `text-span` documents).
//
// Two passes, only the second when actually needed: a "natural" (unwrapped,
// `white-space:pre`) pass always runs first to get the content's true
// single-line width; if `maxW` is the "unbounded" sentinel (>= 1e6, mirrors
// `ui/api/web/backend.kk`'s `single-line-w`) or the natural width already
// fits within `maxW`, that pass's own measurements are the answer (no
// wrapping occurs either way). Only when the natural width EXCEEDS a finite
// `maxW` does a second, `white-space:normal` pass at `width:maxW` run to
// get the wrapped height and per-line rects -- at exactly the width the
// paint case will use (`min(naturalWidth, maxW)` collapses to `maxW` in
// that branch), so rects measured here land where the browser will
// actually paint the spans.
//
// The Koka-side wrapper (`measure-rich-web` in `ui/api/web/backend.kk`)
// only passes font overrides (`span-css-fonts`) through this extern --
// color is intentionally absent (Global Constraint: only font
// participates in measurement, color is paint-time only).
//
// Returns `{fst: totalW, snd: totalH, thd: flatQuads, field4: rectCounts}`
// (a Koka 4-tuple's JS shape): `flatQuads` packs every span's rect(s)
// back-to-back, 4 numbers (x, y, w, h -- relative to the container's own
// origin) each, in span order; `rectCounts` has one entry per span saying
// how many of those quads are its (`getClientRects()` already returns one
// rect per LINE a span occupies when it wraps, so a span whose text breaks
// across a line boundary naturally reports 2+ rects here -- no glyph-index
// math needed on this backend, unlike native's Impeller paragraph builder).
export function kk_dom_measure_rich_box(content, baseCssFont, spanStarts, spanEnds, spanCssFonts, maxW) {
  const cps = Array.from(content);
  const n = spanStarts.length;

  function buildContainer(wrapWidth) {
    const div = document.createElement("div");
    div.style.cssText =
      "position:absolute;visibility:hidden;left:-9999px;top:0;box-sizing:border-box";
    if (wrapWidth === null) {
      div.style.whiteSpace = "pre";
    } else {
      div.style.whiteSpace = "normal";
      div.style.wordWrap = "break-word";
      div.style.width = wrapWidth + "px";
    }
    const spanEls = new Array(n);
    let pos = 0;
    for (let i = 0; i < n; i++) {
      const s = spanStarts[i], e = spanEnds[i];
      if (s > pos) {
        const gap = document.createElement("span");
        gap.style.font = baseCssFont;
        gap.textContent = cps.slice(pos, s).join("");
        div.appendChild(gap);
      }
      const el = document.createElement("span");
      el.style.font = spanCssFonts[i];
      el.textContent = cps.slice(s, e).join("");
      div.appendChild(el);
      spanEls[i] = el;
      pos = e;
    }
    if (pos < cps.length) {
      const tail = document.createElement("span");
      tail.style.font = baseCssFont;
      tail.textContent = cps.slice(pos).join("");
      div.appendChild(tail);
    }
    document.body.appendChild(div);
    return { div, spanEls };
  }

  function measure(built) {
    const rect = built.div.getBoundingClientRect();
    const quads = [];
    const counts = new Array(n);
    for (let i = 0; i < n; i++) {
      const rs = built.spanEls[i].getClientRects();
      counts[i] = rs.length;
      for (let j = 0; j < rs.length; j++) {
        const r = rs[j];
        quads.push(r.left - rect.left, r.top - rect.top, r.width, r.height);
      }
    }
    return { tw: rect.width, th: rect.height, quads, counts };
  }

  const wrapMode = maxW < 1e6;
  const natural = buildContainer(null);
  const naturalM = measure(natural);
  let result = naturalM;
  if (wrapMode && naturalM.tw > maxW) {
    const wrapped = buildContainer(maxW);
    result = measure(wrapped);
    document.body.removeChild(wrapped.div);
  }
  document.body.removeChild(natural.div);
  return { fst: result.tw, snd: result.th, thd: result.quads, field4: result.counts };
}

export function kk_dom_is_null(x) {
  return (x === null || x === undefined);
}

// ---- ui/test-live synthetic input: REAL DOM events through the real
// listeners. Dispatch is DEFERRED to a clean stack (setTimeout 0): real user
// events never arrive re-entrantly inside a koka extern frame, and neither
// may synthetic ones (the input listener re-enters the runtime otherwise).
// (untrusted events do not natively focus, so focus explicitly)
export function kk_dom_inject_click(x, y) {
  setTimeout(() => {
    const el = document.elementFromPoint(x, y) || document.getElementById("app");
    if (!el) return;
    const opts = { clientX: x, clientY: y, bubbles: true };
    el.dispatchEvent(new window.MouseEvent("mousedown", opts));
    if (el.focus && (el.tagName === "INPUT" || el.tagName === "TEXTAREA")) el.focus();
    el.dispatchEvent(new window.MouseEvent("mouseup", opts));
    el.dispatchEvent(new window.MouseEvent("click", opts));
  }, 0);
}

export function kk_dom_inject_text(s) {
  const el = document.activeElement;
  if (!el || (el.tagName !== "INPUT" && el.tagName !== "TEXTAREA")) return false;
  setTimeout(() => {
    // re-resolve: a vdom patch may have replaced the element since capture.
    // NOTE window.Event: this file is inlined into the compiled module, whose
    // generated scope shadows the bare `Event` global.
    const now = document.activeElement;
    const tgt = (now && (now.tagName === "INPUT" || now.tagName === "TEXTAREA")) ? now : el;
    tgt.value = tgt.value + s;
    tgt.dispatchEvent(new window.Event("input", { bubbles: true }));
  }, 0);
  return true;
}

export function kk_dom_set_title(s) {
  document.title = s;
}

export function kk_dom_inject_key(key) {
  const el = document.activeElement || document.getElementById("app");
  if (!el) return;
  setTimeout(() => {
    const isInput = (el.tagName === "INPUT" || el.tagName === "TEXTAREA");
    if (key === "Backspace" && isInput) {
      // untrusted keydowns perform no default action: simulate the edit the
      // way a trusted Backspace would, then fire `input` like real typing
      el.value = el.value.slice(0, -1);
      el.dispatchEvent(new window.Event("input", { bubbles: true }));
    } else {
      el.dispatchEvent(new window.KeyboardEvent("keydown", { key: key, bubbles: true }));
    }
  }, 0);
}

export function kk_dom_inject_move(x, y) {
  setTimeout(() => {
    const el = document.elementFromPoint(x, y) || document.getElementById("app");
    if (el) el.dispatchEvent(new window.MouseEvent("mousemove", { clientX: x, clientY: y, bubbles: true }));
  }, 0);
}

// a real wheel event at the point, through the real listener (koka-owned
// scrolling: OUR root "wheel" listener does the scrolling, not the browser --
// an untrusted WheelEvent's default action is a no-op regardless).
// NOTE window.WheelEvent: this file is inlined into the compiled module,
// whose generated scope shadows the bare global.
// `dy` is in the caller's convention (dy > 0 = wheel-up, see test.kk's
// `send-scroll`); deltaMode 0 (pixels) and the NEGATION here is the inverse
// of kk_dom_wheel_scale's read-side negation, so the round trip is identity.
export function kk_dom_inject_wheel(x, y, dy) {
  setTimeout(() => {
    const el = document.elementFromPoint(x, y) || document.getElementById("app");
    if (!el) return;
    el.dispatchEvent(new window.WheelEvent("wheel", {
      clientX: x, clientY: y, deltaY: -dy, deltaMode: 0,
      bubbles: true, cancelable: true,
    }));
  }, 0);
}

// ui/image's `FromPixels` (task 4, web parity): paint raw RGBA8888 onto an
// OFFSCREEN canvas via putImageData, then read it back out as a PNG data-url
// -- so FromPixels reuses the SAME `<img src>` / onload-probe path as every
// other source variant (one lowering, one wait mechanism), rather than a
// separate live `<canvas>` element in the tree. `rgba` is a plain Koka
// `vector<int8>` (a JS array of possibly-negative two's-complement bytes);
// `& 0xFF` recovers the unsigned byte JS's Uint8ClampedArray expects.
export function kk_dom_pixels_to_dataurl(rgba, w, h) {
  const n = w * h * 4;
  const clamped = new Uint8ClampedArray(n);
  for (let i = 0; i < n; i++) clamped[i] = (rgba[i] ?? 0) & 0xff;
  const canvas = document.createElement("canvas");
  canvas.width = w; canvas.height = h;
  const ctx = canvas.getContext("2d");
  ctx.putImageData(new ImageData(clamped, w, h), 0, 0);
  return canvas.toDataURL();
}
