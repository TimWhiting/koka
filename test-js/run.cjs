#!/usr/bin/env node
/**
 * Run the Koka compiler in Node.js with filesystem-backed VFS.
 * Usage: node run.cjs [source.kk]
 */

const fs = require('fs');
const path = require('path');

const JSEXE = path.join(__dirname, '..', 'dist-newstyle', 'build', 'javascript-ghcjs',
  'ghc-9.15.20260321', 'koka-3.2.4', 'x', 'koka-playground', 'build',
  'koka-playground', 'koka-playground.jsexe');

const LIB = path.join(__dirname, '..', 'lib');
const PRECOMPILED = path.join(__dirname, '..', 'precompiled');

// ── VFS backed by real filesystem ────────────────────────────────────────────

const vfsFiles = {};

function vfsAdd(vfsPath, content, time) {
  vfsFiles[vfsPath] = { content, time: time || Date.now() };
}

globalThis.kokaVFS = {
  readFile(p) {
    if (vfsFiles[p]) return vfsFiles[p].content;
    return null;
  },
  fileExists(p) {
    var found = !!vfsFiles[p];
    if (p.includes('/lib/') && p.endsWith('.kki')) {
      console.log('[vfs ' + (found ? 'HIT' : 'MISS') + '] fileExists: ' + p);
    }
    return found;
  },
  fileTime(p) { return vfsFiles[p] ? vfsFiles[p].time : 0; },
  writeFile(p, c) { vfsFiles[p] = { content: c, time: Date.now() }; },
  listDir(p) { return []; },
  createDir(p) {},
  dirExists(p) { return true; },
  fileSize(p) { return vfsFiles[p] ? vfsFiles[p].content.length : 0; },
  removeFile(p) { delete vfsFiles[p]; },
};

// ── Preload stdlib ───────────────────────────────────────────────────────────

function preloadStdlib() {
  // Load source files
  let sourceCount = 0;
  function loadDir(fsDir, vfsPrefix) {
    if (!fs.existsSync(fsDir)) return;
    for (const entry of fs.readdirSync(fsDir, { withFileTypes: true })) {
      const fsPath = path.join(fsDir, entry.name);
      const vfsPath = vfsPrefix + '/' + entry.name;
      if (entry.isDirectory()) {
        loadDir(fsPath, vfsPath);
      } else {
        vfsAdd(vfsPath, fs.readFileSync(fsPath, 'utf-8'));
        sourceCount++;
      }
    }
  }
  loadDir(path.join(LIB, 'std'), '/share/lib/std');
  console.log(`Loaded ${sourceCount} source files`);

  // Load precompiled .kki and .mjs
  let precompiledCount = 0;
  if (fs.existsSync(PRECOMPILED)) {
    for (const f of fs.readdirSync(PRECOMPILED)) {
      const content = fs.readFileSync(path.join(PRECOMPILED, f), 'utf-8');
      if (f.endsWith('.kki')) {
        vfsAdd('/lib/js-debug/' + f, content, Date.now() + 100000);
        precompiledCount++;
      }
      if (f.endsWith('.mjs')) {
        vfsAdd('/lib/js-debug/' + f, content, Date.now() + 100000);
      }
    }
  }
  console.log(`Loaded ${precompiledCount} precompiled .kki files`);
}

// ── Compiler log callback ────────────────────────────────────────────────────

globalThis.kokaOnCompilerLog = function(msg) {
  console.log('[compiler] ' + msg);
};

globalThis.kokaVerbose = 3;

// ── Load and run ─────────────────────────────────────────────────────────────

const sourceFile = process.argv[2];
const source = sourceFile
  ? fs.readFileSync(sourceFile, 'utf-8')
  : 'module main\n\nfun main()\n  println("Hello from Koka in Node.js!")\n';
const moduleName = sourceFile ? path.basename(sourceFile, '.kk') : 'main';

console.log('=== Koka Playground (Node.js) ===');
console.log(`Module: ${moduleName}`);
console.log('');

preloadStdlib();

console.log('');
console.log('Loading compiler...');

// Load the patched all.js
// The Emscripten async createWasm needs to run, so we use a different approach:
// Load individual files instead of all.js to avoid the Emscripten WASM issue

// Actually, for Node.js we need the WASM file available.
// Copy it to the expected location and provide the right Module config.
const wasmPath = path.join(JSEXE, 'koka-playground.wasm');
if (!fs.existsSync(wasmPath)) {
  const rtsWasm = path.join(__dirname, '..', 'ghc-rts.wasm');
  if (fs.existsSync(rtsWasm)) {
    fs.copyFileSync(rtsWasm, wasmPath);
  }
}

// Override fetch to handle relative paths (WASM loading)
const origFetch = globalThis.fetch;
globalThis.fetch = async function(url, ...args) {
  if (typeof url === 'string' && !url.startsWith('http')) {
    const filePath = path.join(JSEXE, url);
    if (fs.existsSync(filePath)) {
      const data = fs.readFileSync(filePath);
      return {
        ok: true,
        arrayBuffer: async () => data.buffer.slice(data.byteOffset, data.byteOffset + data.byteLength),
        text: async () => data.toString('utf-8'),
      };
    }
    return { ok: false };
  }
  if (origFetch) return origFetch(url, ...args);
  return { ok: false };
};

// Make require available globally (Emscripten code in all.js uses it)
globalThis.require = require;
globalThis.__dirname = JSEXE;

// Load the patched all.js in global scope
const allJs = fs.readFileSync(path.join(JSEXE, 'all.js'), 'utf-8');
console.log(`Loading all.js (${(allJs.length / 1e6).toFixed(1)}MB)...`);
try {
  require('vm').runInThisContext(allJs, { filename: 'all.js' });
  console.log('all.js loaded');
} catch(e) {
  console.error('Error loading all.js:', e.message);
  console.error(e.stack.split('\n').slice(0,5).join('\n'));
  process.exit(1);
}

// Wait for compiler to register
setTimeout(() => {
  if (typeof globalThis.kokaCompile !== 'function') {
    console.error('kokaCompile not registered after 3s');
    process.exit(1);
  }

  console.log('Compiler ready!');
  console.log('');
  console.log('=== Compiling ===');
  globalThis.kokaResult = undefined;
  globalThis.kokaCompile(moduleName, source);

  // Poll for result
  const poll = setInterval(() => {
    if (globalThis.kokaResult !== undefined) {
      clearInterval(poll);
      console.log('');
      console.log('=== Result ===');
      console.log(globalThis.kokaResult);

      // Show generated files
      const mjsFiles = Object.keys(vfsFiles).filter(p => p.endsWith('.mjs'));
      console.log('');
      console.log('Generated .mjs files:', mjsFiles.length);
      mjsFiles.forEach(p => console.log('  ' + p + ' (' + vfsFiles[p].content.length + ' chars)'));

      // Exit after a bit
      setTimeout(() => process.exit(0), 1000);
    }
  }, 100);

  // Timeout
  setTimeout(() => {
    if (globalThis.kokaResult === undefined) {
      console.error('Compilation timed out');
      process.exit(1);
    }
  }, 30000);
}, 3000);
