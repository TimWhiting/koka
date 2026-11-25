// wasi-threads host support (browser leg of `koka --wasithreads` builds).
//
// The wasi-threads ABI is small: the module imports its (SHARED) linear
// memory as `env.memory` and a `wasi.thread-spawn(start_arg) -> tid` hook;
// each spawned thread is the SAME module instantiated again on a Worker
// against the same memory, entered through the module's exported
// `wasi_thread_start(tid, start_arg)`. wasi-libc's pthreads sit entirely on
// top of that hook, so `pthread_create` in kklib just works once this file
// provides it. Thread ids come from an atomic counter in a side
// SharedArrayBuffer so nested spawns (a thread creating a thread) allocate
// unique ids without round-tripping to the main page.
//
// `{{MEMORY}}` is substituted at koka post-link: `null` for a non-threaded
// build, a `{initial, maximum, shared:true}` descriptor (matching the
// linker's --initial-memory/--max-memory) for a threaded one.
const MEMORY = {{MEMORY}};

// Main-page entry: returns null for non-threaded modules (host proceeds
// exactly as before); for threaded ones, creates the shared memory and the
// extra imports ({env, wasi}) to spread into WebAssembly.instantiate.
export function threadSupport(module, workerUrl) {
  const importsMemory = WebAssembly.Module.imports(module).some((i) => i.kind === "memory");
  if (!importsMemory) return null;
  if (MEMORY === null) {
    throw new Error("this module imports shared memory (--wasithreads build) but the host files were staged without it -- rebuild so {{MODULE}} and its host files match");
  }
  if (typeof SharedArrayBuffer === "undefined") {
    throw new Error("SharedArrayBuffer is unavailable: threaded wasi builds need the COOP/COEP headers -- serve this directory with `python3 serve.py` instead of a plain static server");
  }
  return makeSupport(module, new WebAssembly.Memory(MEMORY), workerUrl, new SharedArrayBuffer(4));
}

// Shared between the main page and workers (nested pthread_create).
export function makeSupport(module, memory, workerUrl, tidSab) {
  const tids = new Int32Array(tidSab);
  const spawn = (startArg) => {
    try {
      const tid = Atomics.add(tids, 0, 1) + 2;   // ids start at 2 (main thread is 1)
      const w = new Worker(workerUrl, { type: "module" });
      w.postMessage({ module, memory, tidSab, tid, startArg, workerUrl: workerUrl.toString() });
      return tid;
    } catch (e) {
      console.error("wasi thread-spawn failed:", e);
      return -1;   // pthread_create sees EAGAIN
    }
  };
  return { memory, imports: { env: { memory }, wasi: { "thread-spawn": spawn } } };
}
