#!/usr/bin/env node
/**
 * Run the compiled Koka compiler in Node.js (CommonJS).
 * Provides Emscripten stubs and VFS, then loads the compiler.
 */

// Set up minimal Emscripten environment before loading the compiler
const buffer = new ArrayBuffer(1024 * 1024); // 1MB heap
globalThis.Module = {
  // Skip WASM instantiation entirely - provide dummy instance
  instantiateWasm(imports, callback) {
    // Provide a mock instance with empty exports and a memory
    const memory = new WebAssembly.Memory({ initial: 256 });
    const instance = { exports: { memory: memory } };
    callback(instance, null);
    return instance.exports;
  },
  onRuntimeInitialized() {
    console.log('[runtime] Haskell runtime initialized');
  },
  noInitialRun: true,
  noExitRuntime: true,
};

// Set up VFS
globalThis.kokaVFS = {
  readFile(p) { console.log('[vfs] readFile:', p); return null; },
  fileExists(p) { return false; },
  fileTime(p) { return 0; },
  writeFile(p, c) { console.log('[vfs] writeFile:', p, '(' + c.length + ' chars)'); },
  listDir(p) { return []; },
  createDir(p) {},
  dirExists(p) { return false; },
  fileSize(p) { return 0; },
  removeFile(p) {},
};

console.log('[test] Loading compiled Koka compiler...');

const jsPath = process.argv[2] ||
  __dirname + '/../dist-newstyle/build/javascript-ghcjs/ghc-9.15.20260321/koka-3.2.4/x/koka-playground/build/koka-playground/koka-playground.jsexe/all.js';

try {
  require(jsPath);
} catch (e) {
  console.error('[test] Error loading compiler:', e.message);
  console.error(e.stack?.split('\n').slice(0, 5).join('\n'));
}

// Check if compiler registered
setTimeout(() => {
  console.log('[test] kokaCompile type:', typeof globalThis.kokaCompile);
  if (typeof globalThis.kokaCompile === 'function') {
    console.log('[test] SUCCESS: Compiler is alive!');
  } else {
    console.log('[test] Compiler not registered.');
  }
  process.exit(0);
}, 5000);
