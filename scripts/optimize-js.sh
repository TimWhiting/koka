#!/bin/bash
# Compress the GHC JS backend output for deployment.
#
# Minification is NOT recommended — brotli compression alone achieves 95%
# reduction (42MB → 2.3MB), and minified code actually compresses worse
# because the variable renaming hurts compression patterns.
#
# Usage: ./scripts/optimize-js.sh [path-to-jsexe-dir]

set -e

JSEXE="${1:-dist-newstyle/build/javascript-ghcjs/ghc-9.15.20260321/koka-3.2.4/x/koka-playground/build/koka-playground/koka-playground.jsexe}"

if [ ! -f "$JSEXE/all.js" ]; then
  echo "Error: $JSEXE/all.js not found"
  exit 1
fi

echo "Original:  $(du -h "$JSEXE/all.js" | cut -f1)"

# Gzip
gzip -k -9 -f "$JSEXE/all.js"
echo "Gzipped:   $(du -h "$JSEXE/all.js.gz" | cut -f1)"

# Brotli (if available)
if command -v brotli &> /dev/null; then
  brotli -k -9 -f "$JSEXE/all.js"
  echo "Brotli:    $(du -h "$JSEXE/all.js.br" | cut -f1)"
else
  echo "Brotli not available (install with: brew install brotli)"
fi

echo ""
echo "GitHub Pages serves brotli automatically — no additional setup needed."
