import { WASI, Fd, File } from "https://unpkg.com/@bjorn3/browser_wasi_shim@0.2.14/dist/index.js";
import * as wasi from "https://unpkg.com/@bjorn3/browser_wasi_shim@0.2.14/dist/wasi_defs.js";

class ConsoleFile extends Fd {
  constructor(file) {
    super();
    this.file = file;
  }

  fd_fdstat_get() {
    return { ret: 0, fdstat: new wasi.Fdstat(wasi.FILETYPE_REGULAR_FILE, 0) };
  }

  fd_read(view8, iovs) {
    let nread = 0;
    return { ret: -1, nread };
  }

  fd_seek(offset, whence) {
    return { ret: -1, offset: 0 };
  }

  fd_write(
    view8,
    iovs
  ) {
    let nwritten = 0;
    for (let iovec of iovs) {
      let buffer = view8.slice(iovec.buf, iovec.buf + iovec.buf_len);      
      console.log(String.fromCharCode(...buffer));
      nwritten += iovec.buf_len;
    }
    return { ret: 0, nwritten };
  }

  fd_filestat_get() {
    return { ret: 0, filestat: this.file.stat() };
  }
}

class LinearMemory {
  constructor({ initial = 1000, maximum = 1000 }) {
    this.memory = new WebAssembly.Memory({ initial, maximum });
  }
  read_string(offset) {
    let view = new Uint8Array(this.memory.buffer);
    let bytes = []
    for (let byte = view[offset]; byte; byte = view[++offset])
      bytes.push(byte);
    return String.fromCharCode(...bytes);
  }
  log(str) { console.log(`wasm log: ${str}`) }
  log_i(str, i) { console.log(`wasm log: ${str}: ${i}`) }
  env() {
    return {
      memory: this.memory,
      wasm_log: (off) => this.log(this.read_string(off)),
      wasm_log_i: (off, i) => this.log_i(this.read_string(off), i),
      wasm_logobj: (obj) => console.log(obj),
      to_jsstring: (off) => this.read_string(off),
      js_property_get: (obj, prop) => obj[prop],
      js_property_set: (obj, prop, val) => obj[prop] = val,
      js_function_call1: (fun, arg) => fun(arg),
      js_new: (obj, args) => new obj(...args),
      js_array_get: (arr, i) => arr[i],
      js_array_set: (arr, i, val) => arr[i] = val,
      js_array_length: (arr) => arr.length,
      js_global_this: () => globalThis,
      js_true: () => true,
      js_false: () => false,
      js_null: () => null,
      js_undefined: () => undefined,
    }
  }
}

let finalizers = new FinalizationRegistry(f => { f(); });

function invoke(callback, arg) {
  return callback(arg)
}
function out_of_memory() {
  console.log('error: out of linear memory');
}

class WasmObject {
  constructor(wasm, memory) {
    this.memory = memory.memory;
    this.wasm = wasm
    let obj = wasm.exports.make_obj();
    this.obj = obj;
    this.byteBuff = new Uint8Array(this.memory.buffer)
    console.log(`Allocated bytes ${this.byteBuff.slice(obj, obj + 8)}`)
    let free_obj = this.wasm.exports.free_obj;
    finalizers.register(this, () => { free_obj(obj); }, this);
  }
  attachCallback(f) {
    this.wasm.exports.attach_callback(this.obj, f);
  }
  invokeCallback(a) {
    this.wasm.exports.invoke_callback(this.obj, a);
  }
}

async function main(name) {
  let args = ["bin", "arg1", "arg2"];
  let env = ["FOO=bar"];
  let fds = [
    new ConsoleFile(new File([])), // stdin
    new ConsoleFile(new File([])), // stdout
    new ConsoleFile(new File([])), // stderr
  ];
  let wasi = new WASI(args, env, fds);
  let resp = await fetch(name);

  let memory = new LinearMemory({ initial: 2, maximum: 100 });
  let rt = { invoke, out_of_memory };
  let imports = {
    env: memory.env(), rt, wasi_snapshot_preview1: wasi.wasiImport,
  }
  let wasm = await WebAssembly.compileStreaming(resp);
  let instance = await WebAssembly.instantiate(wasm, imports);
  wasi.start(instance);
}

export default main;