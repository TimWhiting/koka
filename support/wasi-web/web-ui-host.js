// Host runtime for Koka `web-ui` apps (wasm32-wasip1 core modules built with
// `--target=wasi-web` that import the "koka:dom" module, see lib/web-ui).
// A project page needs only:
//
//   <div id="app"></div>
//   <script type="module">
//     import { runKoka } from "./web-ui-host.js";
//     await runKoka("./app.wasm");
//   </script>
//
// Design notes (see lib/web-ui/readme.md):
// - real DOM objects cross the boundary as externrefs; the wasm side owns
//   the only reference table (jsobj.c, Perceus-managed) — no handle Map here
// - program stdout/stderr (println/trace) goes to the browser console
//
// Debug vs release: by default the hot paths are unadorned (no per-node
// bookkeeping). Pass `{ debug: true }` — or open any page with
// `?kokaDebug` — to enable the release-debugging instrumentation:
// `kokaDebug` on `window` (live externref-slot enumeration, detached-DOM
// leak check), FinalizationRegistry observation of browser GC, and the
// DOM-relocation counter. See readme "Debugging resource release".

import { WASI, File, OpenFile, ConsoleStdout } from "./vendor/browser_wasi_shim/index.js";
import * as timers from "./timers.js";

export async function runKoka(wasmUrl, opts = {}) {
  const debug = opts.debug ?? new URLSearchParams(window.location.search).has("kokaDebug");
  const wasi = new WASI(["koka-web-ui"], [], [
    new OpenFile(new File([])),
    ConsoleStdout.lineBuffered((msg) => console.log("[stdout]", msg)),
    ConsoleStdout.lineBuffered((msg) => console.log("[stderr]", msg)),
  ]);

  let instance = null;
  let currentEvent = null;
  if (debug) window.__kokaMoves = 0;  // counts DOM relocations (moves of already-attached nodes)
  const decoder = new TextDecoder();
  const encoder = new TextEncoder();

  // fresh Uint8Array over memory.buffer on EVERY call: a cached buffer
  // detaches when wasm memory grows (the classic bug -- do not "optimize").
  const decode = (ptr, len) =>
    decoder.decode(new Uint8Array(instance.exports.memory.buffer, ptr, len));

  // JS->Koka string: snapshot on the length call; the copy call writes that
  // exact snapshot, so the pair can never disagree about length.
  let propSnapshot = new Uint8Array(0);
  let dataurlSnapshot = new Uint8Array(0);   // FromPixels' pixels-to-dataurl (task 4)
  const stringProp = (el, name) => {
    if (name === "value") return el && "value" in el ? el.value : "";
    if (name === "hash")  return (el === window || el == null) ? window.location.hash : "";
    if (name === "drag-data") return currentEvent?.dataTransfer?.getData("text/plain") ?? "";
    return el && typeof el[name] === "string" ? el[name] : "";
  };

  // wheel delta of `e`'s `prop` (deltaX/deltaY), normalized by deltaMode (0 =
  // pixels x1; 1 = lines x16; 2 = pages = window.innerHeight) and NEGATED:
  // the browser reports deltaY > 0 for "wheel down" (scroll toward later
  // content), while ui/state's `apply-wheel` (shared with the native/impeller
  // backend, whose GLFW scroll callback reports positive = wheel-up) takes
  // delta > 0 = wheel-up = reveal earlier content.
  const wheelScale = (e, prop) => {
    const d = e?.[prop];
    if (typeof d !== "number" || !Number.isFinite(d)) return 0;
    const mode = e?.deltaMode ?? 0;
    const scaled = mode === 1 ? d * 16 : mode === 2 ? d * (window.innerHeight || 1) : d;
    return -scaled;
  };

  // browser-GC observation (debug only: per-node FinalizationRegistry
  // registration is not free): when the browser actually reclaims a node
  // (slot freed AND detached), gcCount rises.
  const gcSeen = { count: 0 };
  const gcRegistry = debug && typeof FinalizationRegistry !== "undefined"
    ? new FinalizationRegistry((desc) => { gcSeen.count++; console.debug("koka gc:", desc); })
    : null;
  const gcRegister = (x) => { gcRegistry.register(x, describe(x)); return x; };

  const dom = {
    "get-element-by-id": (ptr, len) => document.getElementById(decode(ptr, len)),
    // ui/test-live synthetic input: real DOM events through the real
    // listeners (untrusted events do not natively focus, so focus explicitly)
    "inject-click": (x, y) => {
      const el = document.elementFromPoint(x, y) || document.getElementById("app");
      if (!el) return;
      const opts = { clientX: x, clientY: y, bubbles: true };
      el.dispatchEvent(new MouseEvent("mousedown", opts));
      if (el.focus && (el.tagName === "INPUT" || el.tagName === "TEXTAREA")) el.focus();
      el.dispatchEvent(new MouseEvent("mouseup", opts));
      el.dispatchEvent(new MouseEvent("click", opts));
    },
    "set-title": (ptr, len) => { document.title = decode(ptr, len); },
    "inject-key": (ptr, len) => {
      const key = decode(ptr, len);
      const el = document.activeElement || document.getElementById("app");
      if (!el) return;
      setTimeout(() => {
        const isInput = (el.tagName === "INPUT" || el.tagName === "TEXTAREA");
        if (key === "Backspace" && isInput) {
          // untrusted keydowns perform no default action: simulate the edit
          el.value = el.value.slice(0, -1);
          el.dispatchEvent(new Event("input", { bubbles: true }));
        } else {
          el.dispatchEvent(new KeyboardEvent("keydown", { key, bubbles: true }));
        }
      }, 0);
    },
    "inject-move": (x, y) => {
      setTimeout(() => {
        const el = document.elementFromPoint(x, y) || document.getElementById("app");
        if (el) el.dispatchEvent(new MouseEvent("mousemove", { clientX: x, clientY: y, bubbles: true }));
      }, 0);
    },
    // a real wheel event at the point, through the real listener (koka-owned
    // scrolling: OUR root "wheel" listener does the scrolling, not the
    // browser -- an untrusted WheelEvent's default action is a no-op
    // regardless). `dy` is in the caller's convention (dy > 0 = wheel-up,
    // see lib/ui/test.kk's `send-scroll`); the negation here is the inverse
    // of `wheelScale`'s read-side negation, so the round trip is identity.
    "inject-wheel": (x, y, dy) => {
      setTimeout(() => {
        const el = document.elementFromPoint(x, y) || document.getElementById("app");
        if (!el) return;
        el.dispatchEvent(new WheelEvent("wheel", {
          clientX: x, clientY: y, deltaY: -dy, deltaMode: 0,
          bubbles: true, cancelable: true,
        }));
      }, 0);
    },
    "inject-text": (ptr, len) => {
      const el = document.activeElement;
      if (!el || (el.tagName !== "INPUT" && el.tagName !== "TEXTAREA")) return 0;
      el.value = el.value + decode(ptr, len);
      el.dispatchEvent(new Event("input", { bubbles: true }));
      return 1;
    },
    "create-element":    (ptr, len) => document.createElement(decode(ptr, len)),
    "create-text":       (ptr, len) => document.createTextNode(decode(ptr, len)),
    "append-child":      (parent, child) => { parent.appendChild(child); },
    "remove-child":      (parent, child) => { parent.removeChild(child); },
    "replace-child":     (parent, fresh, old) => { parent.replaceChild(fresh, old); },
    "set-attribute": (el, nptr, nlen, vptr, vlen) => {
      const name = decode(nptr, nlen), value = decode(vptr, vlen);
      // "value" must be the live property, not the attribute, or controlled
      // inputs never update/clear (the attribute is only the initial value).
      // Guarded so re-applying an unchanged value never disturbs the cursor.
      if (name === "value" && "value" in el) {
        if (el.value !== value) el.value = value;
      }
      // boolean form-control state likewise lives in properties; presence of
      // the attribute means true (html.kk's checked(b)/disabled(b)/selected(b)).
      else if ((name === "checked" || name === "disabled" || name === "selected") && name in el) {
        el[name] = true;
        el.setAttribute(name, value);
      }
      else el.setAttribute(name, value);
      // declarative drag source (html.kk's `draggable(data)`): the first
      // time data-drag is set, wire a dragstart that fills dataTransfer
      // from the attribute -- no imperative setData in guest code, and it
      // tracks later attribute updates automatically.
      if (name === "data-drag" && !el.kokaDragWired) {
        el.kokaDragWired = true;
        el.addEventListener("dragstart",
          (e) => e.dataTransfer?.setData("text/plain", el.dataset?.drag ?? ""));
      }
    },
    "remove-attribute": (el, nptr, nlen) => {
      const name = decode(nptr, nlen);
      if ((name === "checked" || name === "disabled" || name === "selected") && name in el) el[name] = false;
      el.removeAttribute(name);
    },
    "set-text":         (el, ptr, len) => { el.textContent = decode(ptr, len); },
    "get-prop-length": (el, nptr, nlen) => {
      propSnapshot = encoder.encode(stringProp(el, decode(nptr, nlen)));
      return propSnapshot.length;
    },
    "get-prop-copy": (el, ptr) => {
      new Uint8Array(instance.exports.memory.buffer, ptr, propSnapshot.length).set(propSnapshot);
    },
    "measure-text-width": (ptr, len, fptr, flen) => {
      if (!window.$kokaMeasureCtx) window.$kokaMeasureCtx = document.createElement("canvas").getContext("2d");
      window.$kokaMeasureCtx.font = decode(fptr, flen);
      return window.$kokaMeasureCtx.measureText(decode(ptr, len)).width;
    },
    "measure-text-box-height": (ptr, len, fptr, flen, maxw) => {
      if (!window.$kokaMeasureDiv) {
        window.$kokaMeasureDiv = document.createElement("div");
        window.$kokaMeasureDiv.style.cssText =
          "position:absolute;visibility:hidden;left:-9999px;top:0;white-space:normal;word-wrap:break-word;box-sizing:border-box";
        document.body.appendChild(window.$kokaMeasureDiv);
      }
      window.$kokaMeasureDiv.style.font = decode(fptr, flen);
      window.$kokaMeasureDiv.style.width = maxw + "px";
      window.$kokaMeasureDiv.textContent = decode(ptr, len);
      const h = window.$kokaMeasureDiv.offsetHeight;
      window.$kokaMeasureDiv.textContent = "";   // clear: a lingering string pollutes DOM text scans
      return h;
    },
    "get-num-prop": (el, nptr, nlen) => {
      const v = el?.[decode(nptr, nlen)];
      return typeof v === "number" && Number.isFinite(v) ? v : 0;
    },
    "insert-before": (parent, child, anchor) => { parent.insertBefore(child, anchor); },
    "window":   () => window,
    "set-hash": (ptr, len) => { window.location.hash = decode(ptr, len); },
    // subscription record out as an externref: removal needs no JS-side
    // bookkeeping beyond the record itself (held in the wasm-side table,
    // Perceus-owned via dom.c's kk_dom_sub_free_fun).
    "current-event": () => currentEvent,
    "event-wheel-dx": () => wheelScale(currentEvent, "deltaX"),
    "event-wheel-dy": () => wheelScale(currentEvent, "deltaY"),
    "add-listener": (el, ptr, len, listenerId) => {
      const event = decode(ptr, len);
      const fn = (e) => {
        // drop must preventDefault or the browser navigates (see also the
        // auto-dragover wiring below and the dragstart filler in
        // set-attribute -- drag mechanics stay declarative).
        if (event === "drop") e.preventDefault();
        // right-click drives our own context menu; suppress the browser's
        if (event === "contextmenu") e.preventDefault();
        // one-target-per-click (match native hit-testing + avoid the role-shift
        // double-fire where a click bubbles to an ancestor that gained a
        // listener during the synchronous re-render this click triggered)
        if (event === "click") e.stopPropagation();
        // koka-owned scrolling: suppress the browser's native scroll so ONLY
        // our listener moves the scroll region (needs the {passive:false}
        // registration below to be effective)
        if (event === "wheel") e.preventDefault();
        // expose the live event to `current-event` for the duration of the
        // dispatch (the guest reads payload props like "key" at fire time)
        currentEvent = e;
        try { instance.exports["koka:dom/dispatch-event"](listenerId); }
        finally { currentEvent = null; }
      };
      // a passive listener cannot preventDefault; "wheel" must be non-passive
      el.addEventListener(event, fn, event === "wheel" ? { passive: false } : undefined);
      // a drop target must cancel dragover or the browser never fires drop;
      // wire that automatically (part of the same subscription record so
      // removal cleans it up too).
      let over = null;
      if (event === "drop") {
        over = (e) => e.preventDefault();
        el.addEventListener("dragover", over);
      }
      return { el, event, fn, over, removed: false };
    },
    "remove-listener": (s) => {
      if (s == null || s.removed) return;  // idempotent
      s.el.removeEventListener(s.event, s.fn);
      if (s.over) s.el.removeEventListener("dragover", s.over);
      s.removed = true;
    },
    // ui/image's `FromPixels` (task 4, web parity): paint raw RGBA8888 onto
    // an offscreen canvas, read it back as a PNG data-url. `rgba_ptr` points
    // straight into wasm linear memory (dom.c already unboxed the
    // vector<int8> into a flat byte buffer there). Length-then-copy, same
    // snapshot discipline as get-prop above (the length call snapshots the
    // data-url; the copy call writes that exact snapshot).
    "pixels-to-dataurl-length": (rgba_ptr, rgba_len, w, h) => {
      const bytes = new Uint8Array(instance.exports.memory.buffer, rgba_ptr, rgba_len);
      const clamped = new Uint8ClampedArray(w * h * 4);
      for (let i = 0; i < clamped.length; i++) clamped[i] = bytes[i] ?? 0;
      const canvas = document.createElement("canvas");
      canvas.width = w; canvas.height = h;
      const ctx = canvas.getContext("2d");
      ctx.putImageData(new ImageData(clamped, w, h), 0, 0);
      dataurlSnapshot = encoder.encode(canvas.toDataURL());
      return dataurlSnapshot.length;
    },
    "pixels-to-dataurl-copy": (ptr) => {
      new Uint8Array(instance.exports.memory.buffer, ptr, dataurlSnapshot.length).set(dataurlSnapshot);
    },
  };

  // ---- release-debugging API (console: kokaDebug.dump()) ------------------
  // Enumerates the wasm-side externref table (jsobj.c's slot-ref exports)
  // and describes what each live slot still references. The invariant that
  // makes leaks visible: outside a patch, every live slot should reference
  // something still CONNECTED to the document (or the window/subscription
  // records of live listeners) — a live slot holding a detached node means
  // a Koka value still owns DOM the page can no longer show.
  const describe = (x) => {
    if (x == null) return "null";
    if (x === window) return "window";
    if (x instanceof Element) {
      const id = x.id ? "#" + x.id : "";
      const cls = x.classList?.length ? "." + [...x.classList].join(".") : "";
      return `<${x.tagName.toLowerCase()}${id}${cls}>`;
    }
    if (x.nodeType === 3) return `text:${JSON.stringify(x.textContent?.slice(0, 24) ?? "")}`;
    if (x.el && x.event) return `listener:${x.event} on ${describe(x.el)}`;
    if (x instanceof Event) return `event:${x.type}`;
    return String(x);
  };
  const isDetached = (x) => {
    if (x == null || x === window) return false;
    if (x instanceof Node) return !x.isConnected;
    if (x.el && x.event) return x.removed || x.el === window ? false : !(x.el.isConnected);
    return false;
  };
  // debug instrumentation: wrap the hot paths only when asked for
  if (gcRegistry) {
    dom["create-element"] = (ptr, len) => gcRegister(document.createElement(decode(ptr, len)));
    dom["create-text"]    = (ptr, len) => gcRegister(document.createTextNode(decode(ptr, len)));
  }
  if (debug) {
    const plainAppend = dom["append-child"], plainInsert = dom["insert-before"];
    dom["append-child"] = (parent, child) => {
      if (child.parentNode) window.__kokaMoves++;   // relocation, not first attach
      plainAppend(parent, child);
    };
    dom["insert-before"] = (parent, child, anchor) => {
      if (child.parentNode) window.__kokaMoves++;
      plainInsert(parent, child, anchor);
    };
  }

  const kokaDebug = {
    live:      () => instance.exports["koka:dom/live-slots"](),
    allocated: () => instance.exports["koka:dom/slots-allocated"](),
    freed:     () => instance.exports["koka:dom/slots-freed"](),
    gcCount:   () => gcSeen.count,
    slots:     () => {
      const hi = instance.exports["koka:dom/slot-high-water"]();
      const out = [];
      for (let i = 1; i < hi; i++) {
        const ref = instance.exports["koka:dom/slot-ref"](i);
        if (ref != null) out.push({ slot: i, what: describe(ref), detached: isDetached(ref) });
      }
      return out;
    },
    detached:  () => kokaDebug.slots().filter((s) => s.detached),
    dump:      () => { console.table(kokaDebug.slots()); return kokaDebug.live(); },
  };
  if (debug) window.kokaDebug = kokaDebug;

  const wasm = await WebAssembly.compileStreaming(fetch(wasmUrl));
  // --wasithreads builds import shared memory; only then load the threads
  // shim (so staged dirs of plain builds need no extra files)
  const threaded = WebAssembly.Module.imports(wasm).some((i) => i.kind === "memory");
  const threads = threaded
    ? (await import("./wasi-threads.js")).threadSupport(wasm, new URL("./wasi-worker.js", import.meta.url))
    : null;
  instance = await WebAssembly.instantiate(wasm, {
    wasi_snapshot_preview1: wasi.wasiImport,
    "koka:async/timers": timers,
    "koka:dom": dom,
    ...(threads ? threads.imports : {}),
  });
  timers.setInstance(instance);
  wasi.start(instance);

  const loopDone = instance.exports["koka:async/loop-done"];
  if (typeof loopDone === "function" && !loopDone()) {
    const iv = setInterval(() => { if (loopDone()) clearInterval(iv); }, 50);
  }
  return { instance, kokaDebug };
}
