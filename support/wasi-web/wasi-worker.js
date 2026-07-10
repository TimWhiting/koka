// A wasi-threads worker: instantiate the SAME module against the SHARED
// memory and run one thread's entry. `wasi.thread-spawn` (wasi-threads.js)
// posts {module, memory, tid, start_arg} here; wasi-libc's pthread machinery
// takes over inside `wasi_thread_start` (TLS setup, then the thread body).
// The worker gets its own preview1 shim instance (stdout/stderr prefixed
// with the thread id) over the same shared memory, and its own spawn support
// so threads can create threads.
import { WASI, File, OpenFile, ConsoleStdout } from "./vendor/browser_wasi_shim/index.js";
import * as timers from "./timers.js";
import { makeSupport } from "./wasi-threads.js";

self.onmessage = async (e) => {
  const { module, memory, tidSab, tid, startArg, workerUrl } = e.data;
  try {
    const fds = [
      new OpenFile(new File([])),
      ConsoleStdout.lineBuffered((m) => console.log(`[thread ${tid}]`, m)),
      ConsoleStdout.lineBuffered((m) => console.error(`[thread ${tid}]`, m)),
    ];
    const wasi = new WASI(["{{MODULE}}"], [], fds);
    const support = makeSupport(module, memory, new URL(workerUrl), tidSab);
    const instance = await WebAssembly.instantiate(module, {
      wasi_snapshot_preview1: wasi.wasiImport,
      "koka:async/timers": timers,
      ...support.imports,
    });
    timers.setInstance(instance);
    wasi.initialize(instance);   // secondary instance: set up the shim, do NOT run _start
    instance.exports.wasi_thread_start(tid, startArg);
  } catch (err) {
    console.error(`[thread ${tid}] died:`, err);
  } finally {
    self.close();
  }
};
