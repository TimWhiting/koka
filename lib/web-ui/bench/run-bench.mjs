// Fake-DOM node host for bench.kk: every koka:dom import is a minimal stub
// so the measurement isolates the Koka-side diff/patch machinery.
// usage: node run-bench.mjs <path-to-bench.wasm>
import { readFile } from "node:fs/promises";
import { WASI } from "node:wasi";

const wasi = new WASI({
  version: "preview1",
  args: ["bench"],
  env: { ...process.env },   // pass MIMALLOC_SHOW_STATS through for allocstats builds
  preopens: {},
});

const decoder = new TextDecoder();
let instance = null;
const decode = (ptr, len) =>
  decoder.decode(new Uint8Array(instance.exports.memory.buffer, ptr, len));

const fakeEl = () => ({ children: [] });
const root = fakeEl();
let propSnapshot = new Uint8Array(0);

const dom = {
  "get-element-by-id": (ptr, len) => (decode(ptr, len) === "root" ? root : null),
  "create-element": () => fakeEl(),
  "create-text": () => fakeEl(),
  "append-child": () => {},
  "remove-child": () => {},
  "replace-child": () => {},
  "insert-before": () => {},
  "set-attribute": () => {},
  "remove-attribute": () => {},
  "set-text": () => {},
  "get-prop-length": () => { propSnapshot = new Uint8Array(0); return 0; },
  "get-prop-copy": () => {},
  "get-num-prop": () => 0,
  "window": () => globalThis,
  "set-hash": () => {},
  "current-event": () => null,
  "add-listener": () => ({}),
  "remove-listener": () => {},
};

const timers = {
  "set-timeout": () => 0,
  "clear-timeout": () => {},
};

const wasmBytes = await readFile(process.argv[2]);
instance = (await WebAssembly.instantiate(wasmBytes, {
  wasi_snapshot_preview1: wasi.wasiImport,
  "koka:async/timers": timers,
  "koka:dom": dom,
})).instance;
wasi.start(instance);
