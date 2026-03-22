#!/usr/bin/env node
/**
 * Run the Koka compiler in Node.js with filesystem-backed VFS.
 * Usage: node run.cjs [source.kk]
 */

const fs = require('fs');
const path = require('path');

// Auto-detect jsexe directory
function findJsexe() {
  const base = path.join(__dirname, '..', 'dist-newstyle', 'build', 'javascript-ghcjs');
  if (!fs.existsSync(base)) return null;
  for (const ghcVer of fs.readdirSync(base)) {
    const jsexe = path.join(base, ghcVer, 'koka-3.2.4', 'x', 'koka-playground',
      'build', 'koka-playground', 'koka-playground.jsexe');
    if (fs.existsSync(path.join(jsexe, 'all.js'))) return jsexe;
  }
  return null;
}
const JSEXE = findJsexe();
if (!JSEXE) {
  console.error('Could not find koka-playground.jsexe. Build first with:');
  console.error('  cabal build lib:koka exe:koka-playground --with-compiler=javascript-unknown-ghcjs-ghc --with-hc-pkg=javascript-unknown-ghcjs-ghc-pkg');
  process.exit(1);
}
console.log('Using:', JSEXE);

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

globalThis.kokaVerbose = 1;

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

// GHC 9.12.2+ embeds WASM as base64 data URI — no external file needed.
// But Node.js fetch doesn't handle data URIs, so polyfill it.

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
