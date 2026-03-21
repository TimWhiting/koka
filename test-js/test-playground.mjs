#!/usr/bin/env node
/**
 * test-playground.mjs
 *
 * Test harness for running the Koka compiler (compiled to JS via GHC JS backend)
 * in Node.js. Uses the real filesystem as the VFS backend.
 *
 * Usage:
 *   node test-playground.mjs [source-file.kk]
 *
 * If no source file is given, compiles a built-in "Hello, Koka!" program.
 */

import fs from 'fs';
import path from 'path';

// ── VFS backed by the real filesystem ────────────────────────────────────────

/**
 * Create a VFS that delegates to Node.js filesystem operations.
 * This is used for testing — the browser version uses an in-memory VFS.
 */
function createNodeVFS(roots) {
  return {
    readFile(p) {
      for (const root of roots) {
        const fullPath = path.join(root, p);
        try {
          return fs.readFileSync(fullPath, 'utf-8');
        } catch { /* try next root */ }
      }
      // Try absolute path
      try {
        return fs.readFileSync(p, 'utf-8');
      } catch {
        return null;
      }
    },

    fileExists(p) {
      for (const root of roots) {
        if (fs.existsSync(path.join(root, p))) return true;
      }
      return fs.existsSync(p);
    },

    fileTime(p) {
      for (const root of roots) {
        try {
          return fs.statSync(path.join(root, p)).mtimeMs;
        } catch { /* try next */ }
      }
      try {
        return fs.statSync(p).mtimeMs;
      } catch {
        return 0;
      }
    },

    writeFile(p, content) {
      const dir = path.dirname(p);
      fs.mkdirSync(dir, { recursive: true });
      fs.writeFileSync(p, content, 'utf-8');
      console.log(`[VFS] Wrote: ${p} (${content.length} bytes)`);
    },

    listDir(p) {
      for (const root of roots) {
        try {
          return fs.readdirSync(path.join(root, p));
        } catch { /* try next */ }
      }
      try {
        return fs.readdirSync(p);
      } catch {
        return [];
      }
    },

    createDir(p) {
      fs.mkdirSync(p, { recursive: true });
    },

    dirExists(p) {
      for (const root of roots) {
        try {
          return fs.statSync(path.join(root, p)).isDirectory();
        } catch { /* try next */ }
      }
      try {
        return fs.statSync(p).isDirectory();
      } catch {
        return false;
      }
    },

    fileSize(p) {
      for (const root of roots) {
        try {
          return fs.statSync(path.join(root, p)).size;
        } catch { /* try next */ }
      }
      try {
        return fs.statSync(p).size;
      } catch {
        return 0;
      }
    },

    removeFile(p) {
      try {
        fs.unlinkSync(p);
      } catch { /* ignore */ }
    },
  };
}

// ── Default test program ─────────────────────────────────────────────────────

const DEFAULT_SOURCE = `module main

fun main()
  println("Hello from Koka compiled in JavaScript!")
`;

// ── Main ─────────────────────────────────────────────────────────────────────

async function main() {
  const sourceFile = process.argv[2];
  const source = sourceFile
    ? fs.readFileSync(sourceFile, 'utf-8')
    : DEFAULT_SOURCE;
  const moduleName = sourceFile
    ? path.basename(sourceFile, '.kk')
    : 'main';

  console.log('=== Koka Playground Test (Node.js) ===');
  console.log(`Module: ${moduleName}`);
  console.log(`Source: ${source.length} chars`);
  console.log('');

  // Set up VFS with filesystem roots
  // In a real deployment, these would point to the installed koka stdlib
  const roots = [
    '.',
    process.cwd(),
    // Add koka share/lib path if available
  ];

  globalThis.kokaVFS = createNodeVFS(roots);

  // Load the compiled Koka compiler
  // The path will depend on the cabal build output location
  const compilerPath = process.env.KOKA_JS_PATH || './koka-playground.js';

  console.log(`Loading compiler from: ${compilerPath}`);

  try {
    // The compiled GHC JS output is a self-contained JS file
    // that sets up globalThis.kokaCompile when loaded
    await import(compilerPath);
  } catch (err) {
    console.error(`Failed to load compiler: ${err.message}`);
    console.error('');
    console.error('Set KOKA_JS_PATH to the compiled koka-playground.js file.');
    console.error('Build it with: cabal build exe:koka-playground');
    process.exit(1);
  }

  // Check if the compiler registered itself
  if (typeof globalThis.kokaCompile !== 'function') {
    console.error('Compiler loaded but globalThis.kokaCompile not registered.');
    console.error('The compiler main() may not have run correctly.');
    process.exit(1);
  }

  console.log('Compiler loaded successfully!');
  console.log('');
  console.log('--- Compiling ---');

  try {
    const result = await Promise.resolve(
      globalThis.kokaCompile(moduleName, source)
    );
    console.log('');
    console.log('--- Compilation Result ---');
    console.log(result);
  } catch (err) {
    console.error(`Compilation failed: ${err.message}`);
    process.exit(1);
  }
}

main().catch(err => {
  console.error(err);
  process.exit(1);
});
