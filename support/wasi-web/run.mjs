// node entry for a koka wasi-web build (requires node >= 24)
// generated next to <module>.wasm by `koka --target=wasi-web`; {{MODULE}} is
// substituted with the wasm file's basename (without extension).
//
// Rev 3: `--target=wasi-web` emits a plain wasm32-wasip1 core module (command
// model, `_start` export) -- no wit-bindgen, no jco, no component model.
// node's builtin `node:wasi` implements the `wasi_snapshot_preview1` import
// namespace; the only other import namespace a program can have is
// `koka:async/timers` (only when the program transitively imports
// `std/async` -- see lib/std/async/api/wasiweb/evloop.c), implemented here by
// timers.js over the real `setTimeout`/`clearTimeout`.
import { readFile } from "node:fs/promises";
import { WASI } from "node:wasi";
import * as timers from "./timers.js";

const wasi = new WASI({
  version: "preview1",
  args: process.argv.slice(1),
  env: process.env,
  preopens: {},
});

const wasmBytes = await readFile(new URL("./{{MODULE}}.wasm", import.meta.url));
const wasmModule = await WebAssembly.compile(wasmBytes);

// This generic runner only supplies WASI + koka:async/timers. A program that
// imports more (e.g. `koka:dom` from a DOM/browser sample) needs its own host
// (usually a browser page) providing those imports -- diagnose that up front
// instead of failing with an opaque instantiation TypeError.
{
  const provided = new Set(["wasi_snapshot_preview1", "koka:async/timers", "env", "wasi"]);
  const missing = [...new Set(WebAssembly.Module.imports(wasmModule)
                      .map((i) => i.module).filter((m) => !provided.has(m)))];
  if (missing.length > 0) {
    console.error(`error: this program imports [${missing.join(", ")}] which this generic node runner does not provide.`);
    console.error(`hint : browser/DOM programs need their sample's own host page -- run its build.sh and serve the staged out/ directory it prints.`);
    process.exit(1);
  }
}

// --wasithreads builds import shared memory + wasi.thread-spawn. node's
// builtin `node:wasi` cannot host wasi-threads, so under node a threaded
// build runs single-threaded: we supply the memory it asks for and a spawn
// hook that always fails (pthread_create sees EAGAIN). Use the browser
// (index.html + serve.py) for actual threads.
const MEMORY = {{MEMORY}};
const importsMemory = WebAssembly.Module.imports(wasmModule).some((i) => i.kind === "memory");
const threadImports = importsMemory
  ? { env: { memory: new WebAssembly.Memory(MEMORY) },
      wasi: { "thread-spawn": (_arg) => { console.error("[run.mjs] thread-spawn refused: node:wasi cannot host wasi-threads; use the browser host"); return -1; } } }
  : {};

const instance = await WebAssembly.instantiate(wasmModule, {
  wasi_snapshot_preview1: wasi.wasiImport,
  "koka:async/timers": timers,
  ...threadImports,
});

// std/async's wasiweb evloop needs to call back into this instance's
// `koka:async/dispatch` export once a real setTimeout fires; hand timers.js
// the instance now, before starting the guest.
timers.setInstance(instance);

// `wasi.start` calls the guest's `_start` and returns its exit code. A plain
// sync-only program (no `std/async`) runs to completion here and we exit
// immediately below. A program that registered pending async work (timers)
// returns from `_start` early (the inverted event loop never blocks); such a
// program additionally exports `koka:async/loop-done`, which we poll -- node
// exits on its own once there is no more pending work and no other reason to
// stay alive.
const exitCode = wasi.start(instance);

const loopDone = instance.exports["koka:async/loop-done"];
if (typeof loopDone === "function") {
  const iv = setInterval(() => {
    if (loopDone()) {
      clearInterval(iv);
      process.exit(exitCode);
    }
  }, 50);
} else {
  process.exit(exitCode);
}
