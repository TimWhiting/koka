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
const { instance } = await WebAssembly.instantiate(wasmBytes, {
  wasi_snapshot_preview1: wasi.wasiImport,
  "koka:async/timers": timers,
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
