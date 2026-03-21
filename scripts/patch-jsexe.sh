#!/bin/bash
# Patches the GHC JS backend output to fix Emscripten WASM loading issues.
# Run this after each `cabal build exe:koka-playground`.
#
# Usage: ./scripts/patch-jsexe.sh [path-to-jsexe-dir]

set -e

JSEXE="${1:-dist-newstyle/build/javascript-ghcjs/ghc-9.15.20260321/koka-3.2.4/x/koka-playground/build/koka-playground/koka-playground.jsexe}"

if [ ! -f "$JSEXE/all.js" ]; then
  echo "Error: $JSEXE/all.js not found"
  exit 1
fi

echo "Patching $JSEXE/all.js..."

# Copy the real RTS WASM (the embedded one in all.js has corrupt memory limits)
RTS_WASM="$(dirname "$0")/../ghc-rts.wasm"
if [ ! -f "$RTS_WASM" ]; then
  # Try to find it from the GHC build
  GHC_BUILD="${GHC_JS_BUILD:-$HOME/ghc-js-build}"
  if [ -f "$GHC_BUILD/_build/stage1/rts/build/a.wasm" ]; then
    cp "$GHC_BUILD/_build/stage1/rts/build/a.wasm" "$RTS_WASM"
    echo "  Copied RTS WASM from GHC build"
  else
    echo "  Warning: Could not find RTS WASM. Set GHC_JS_BUILD env var."
  fi
fi

if [ -f "$RTS_WASM" ]; then
  cp "$RTS_WASM" "$JSEXE/koka-playground.wasm"
  echo "  Installed koka-playground.wasm"
fi

# Patch all.js with node (handles the binary-encoded content safely)
node -e "
const fs = require('fs');
let code = fs.readFileSync('$JSEXE/all.js', 'latin1');
let patched = 0;

// 1. Replace findWasmBinary to load external .wasm file instead of corrupt embedded binary
const oldFind = code.match(/function findWasmBinary\(\) \{[^}]*return binaryDecode\('[^']*'\);[^}]*\}/);
if (oldFind) {
  code = code.replace(oldFind[0], 'function findWasmBinary() { return \"koka-playground.wasm\"; }');
  patched++;
  console.log('  [1] Patched findWasmBinary -> external .wasm');
}

// 2. Replace getBinarySync to return null for string paths (triggers fetch)
if (code.includes('function getBinarySync(file) {\n  return file;\n}')) {
  code = code.replace(
    'function getBinarySync(file) {\n  return file;\n}',
    'function getBinarySync(file) {\n  if (typeof file === \"string\") return null;\n  return file;\n}'
  );
  patched++;
  console.log('  [2] Patched getBinarySync -> null for string paths');
}

// 3. Replace getWasmBinary to fetch from URL when getBinarySync returns null
const oldGetWasm = 'async function getWasmBinary(binaryFile) {\n\n  // Otherwise, getBinarySync should be able to get it synchronously\n  return getBinarySync(binaryFile);\n}';
if (code.includes(oldGetWasm)) {
  code = code.replace(oldGetWasm,
    'async function getWasmBinary(binaryFile) { var s = getBinarySync(binaryFile); if (s) return s; var r = await fetch(binaryFile); return new Uint8Array(await r.arrayBuffer()); }'
  );
  patched++;
  console.log('  [3] Patched getWasmBinary -> fetch for URLs');
}

// 4. Add WASI stubs to empty wasmImports
if (code.includes('var wasmImports = {\n  \n};')) {
  code = code.replace(
    'var wasmImports = {\n  \n};',
    'var wasmImports = {\n  fd_close: function(fd) { return 0; },\n  fd_write: function(fd, iov, iovcnt, pnum) { return 0; },\n  fd_seek: function(fd, offset_lo, offset_hi, whence, newoffset) { return 0; }\n};'
  );
  patched++;
  console.log('  [4] Added WASI stubs to wasmImports');
}

fs.writeFileSync('$JSEXE/all.js', code, 'latin1');
console.log('  Applied ' + patched + '/4 patches');
"

echo "Done. Test with: open $JSEXE/test.html"
