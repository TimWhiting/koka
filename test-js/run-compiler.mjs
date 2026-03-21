#!/usr/bin/env node
/**
 * Run the compiled Koka compiler in Node.js.
 * Provides Emscripten stubs and VFS, then invokes the compiler.
 */

import { readFileSync } from 'fs';
import { createRequire } from 'module';

// Set up minimal Emscripten environment before loading the compiler
const buffer = new ArrayBuffer(1024 * 1024); // 1MB heap
globalThis.Module = {
  HEAP8: new Int8Array(buffer),
  HEAPU8: new Uint8Array(buffer),
  // Skip WASM instantiation
  instantiateWasm(imports, callback) {
    // Return empty exports - no C code to run
    callback({}, null);
    return {};
  },
  onRuntimeInitialized() {
    console.log('[runtime] Haskell runtime initialized');
  },
  // Suppress Emscripten's default behavior
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

// The all.js uses var declarations so we need to load it in global scope
const require_ = createRequire(import.meta.url);

try {
  // Directly evaluate the JS file
  const jsPath = process.argv[2] ||
    '../dist-newstyle/build/javascript-ghcjs/ghc-9.15.20260321/koka-3.2.4/x/koka-playground/build/koka-playground/koka-playground.jsexe/all.js';
  const code = readFileSync(jsPath, 'utf-8');

  // The code uses `Module` and `globalThis` references.
  // We need to evaluate it, but with our pre-configured Module.
  const fn = new Function(code);
  fn();
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
    console.log('[test] Compiler not registered. Runtime may still be initializing...');
    console.log('[test] Check if h$main was called.');
  }
  process.exit(0);
}, 5000);
