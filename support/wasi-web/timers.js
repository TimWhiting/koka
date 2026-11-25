// Host (JS) implementation of the `koka:async/timers` core-module import
// namespace used by std/async's wasiweb evloop
// (lib/std/async/api/wasiweb/evloop.c). Rev 3: plain wasm32-wasip1 core
// module -- the import object key is the literal namespace string
// `"koka:async/timers"` and each property is looked up by the wasm
// `import_name` string, e.g. `importObject["koka:async/timers"]["set-timeout"]`
// (clang's `import_name("set-timeout")` attribute becomes that property key;
// it need not be a valid JS identifier since it is always accessed via
// bracket/property lookup on the namespace object, never imported by name).
//
// Registry/setter pattern: this module is a static import of both run.mjs
// (node) and index.html (browser), so it cannot import the wasm instance's
// own exports back (a cycle, and the instance does not exist yet at this
// module's evaluation time anyway). Instead the runner hands us the
// instantiated `instance` object once, after instantiation and before
// `_start` is called.
let instance = null;
let nextHandle = 1;
const handles = new Map();

export function setInstance(inst) {
  instance = inst;
}

// JS identifiers cannot contain `-`, so the two host functions are declared
// with plain names and re-exported under their wasm `import_name` strings
// (ESM string export names, `export { x as "..." }`) -- `import * as timers`
// in run.mjs/index.html then yields a namespace object with exactly the
// property keys the wasm import section expects:
// `importObject["koka:async/timers"]["set-timeout"]`.
function setTimeoutImpl(timerId, millisecs) {
  const handle = nextHandle++;
  // timerId/millisecs cross the wasm boundary as i64 -> BigInt.
  const id = globalThis.setTimeout(() => {
    handles.delete(handle);
    if (!instance) {
      throw new Error("timers.js: dispatch called before instance registered");
    }
    instance.exports["koka:async/dispatch"](timerId);
  }, Number(millisecs));
  handles.set(handle, id);
  return handle;
}

function clearTimeoutImpl(handle) {
  const id = handles.get(handle);
  if (id !== undefined) {
    globalThis.clearTimeout(id);
    handles.delete(handle);
  }
}

export { setTimeoutImpl as "set-timeout", clearTimeoutImpl as "clear-timeout" };
