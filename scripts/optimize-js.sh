#!/bin/bash
# Optimize the GHC JS backend output with Google Closure Compiler.
# Requires: npm install -g google-closure-compiler
#
# Usage: ./scripts/optimize-js.sh [path-to-jsexe-dir]

set -e

JSEXE="${1:-dist-newstyle/build/javascript-ghcjs/ghc-9.15.20260321/koka-3.2.4/x/koka-playground/build/koka-playground/koka-playground.jsexe}"

if [ ! -f "$JSEXE/all.js" ]; then
  echo "Error: $JSEXE/all.js not found"
  exit 1
fi

echo "Original size: $(wc -c < "$JSEXE/all.js") bytes"

# Check for closure compiler
if ! command -v google-closure-compiler &> /dev/null; then
  echo "google-closure-compiler not found. Install with:"
  echo "  npm install -g google-closure-compiler"
  echo ""
  echo "Falling back to simple minification with terser..."
  if command -v terser &> /dev/null; then
    terser "$JSEXE/all.js" -o "$JSEXE/all.min.js" --compress --mangle
    echo "Minified: $(wc -c < "$JSEXE/all.min.js") bytes"
  else
    echo "terser not found either. Install with: npm install -g terser"
    exit 1
  fi
  exit 0
fi

echo "Running Google Closure Compiler (SIMPLE_OPTIMIZATIONS)..."
# Start with SIMPLE - ADVANCED may break GHC RTS code
google-closure-compiler \
  --compilation_level SIMPLE_OPTIMIZATIONS \
  --js "$JSEXE/all.js" \
  --js_output_file "$JSEXE/all.min.js" \
  --language_in ECMASCRIPT_2020 \
  --language_out ECMASCRIPT_2020

echo "Minified: $(wc -c < "$JSEXE/all.min.js") bytes"

# Compress
if command -v gzip &> /dev/null; then
  gzip -k -9 -f "$JSEXE/all.min.js"
  echo "Gzipped:  $(wc -c < "$JSEXE/all.min.js.gz") bytes"
fi

if command -v brotli &> /dev/null; then
  brotli -k -9 -f "$JSEXE/all.min.js"
  echo "Brotli:   $(wc -c < "$JSEXE/all.min.js.br") bytes"
fi

echo ""
echo "Size comparison:"
echo "  Original:  $(du -h "$JSEXE/all.js" | cut -f1)"
echo "  Minified:  $(du -h "$JSEXE/all.min.js" | cut -f1)"
[ -f "$JSEXE/all.min.js.gz" ] && echo "  Gzipped:   $(du -h "$JSEXE/all.min.js.gz" | cut -f1)"
[ -f "$JSEXE/all.min.js.br" ] && echo "  Brotli:    $(du -h "$JSEXE/all.min.js.br" | cut -f1)"
