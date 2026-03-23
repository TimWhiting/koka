#!/bin/bash
# Setup the Koka playground for local development.
# Run from the project root directory.
#
# Usage:
#   ./utils/playground-setup.sh          # Full setup (JS + WASM + precompile + web)
#   ./utils/playground-setup.sh js       # JS backend only
#   ./utils/playground-setup.sh wasm     # WASM backend only
#   ./utils/playground-setup.sh web      # Web frontend only (copies assets + starts dev server)
#   ./utils/playground-setup.sh precompile  # Precompile stdlib only
#   ./utils/playground-setup.sh deploy   # Copy all assets to web/public (no build)

set -e

BACKEND="${1:-all}"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

GREEN='\033[0;32m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m'
info() { echo -e "${GREEN}[setup]${NC} $1"; }
warn() { echo -e "${YELLOW}[setup]${NC} $1"; }
err()  { echo -e "${RED}[setup]${NC} $1"; }

# ── Generate cabal file ──────────────────────────────────────────────────────

hpack 2>/dev/null || { err "hpack not found. Install via: cabal install hpack"; exit 1; }

# ── Build JS backend ────────────────────────────────────────────────────────

if [ "$BACKEND" = "all" ] || [ "$BACKEND" = "js" ]; then
  info "Building Koka for JS backend..."
  cabal build lib:koka koka:exe:koka-playground \
    --with-compiler=javascript-unknown-ghcjs-ghc \
    --with-hc-pkg=javascript-unknown-ghcjs-ghc-pkg
  info "JS build done."
fi

# ── Build WASM backend ──────────────────────────────────────────────────────

if [ "$BACKEND" = "all" ] || [ "$BACKEND" = "wasm" ]; then
  if [ -f ~/.ghc-wasm/env ]; then source ~/.ghc-wasm/env; fi
  if command -v wasm32-wasi-ghc &>/dev/null; then
    info "Building Koka for WASM backend..."
    cabal build lib:koka koka:exe:koka-playground \
      --with-compiler=wasm32-wasi-ghc \
      --with-hc-pkg=wasm32-wasi-ghc-pkg

    WASM=$(find dist-newstyle -name "koka-playground.wasm" -path "*/wasm32-wasi/*" | head -1)
    WASM_OPT="${WASM%.wasm}.opt.wasm"

    # Optimize with wasm-opt
    WASM_OPT_BIN=$(command -v wasm-opt 2>/dev/null || echo ~/.ghc-wasm/binaryen/bin/wasm-opt)
    if [ -x "$WASM_OPT_BIN" ]; then
      info "Optimizing WASM with wasm-opt -Oz..."
      "$WASM_OPT_BIN" -Oz "$WASM" -o "$WASM_OPT"
      info "Optimized: $(du -h "$WASM_OPT" | cut -f1) (from $(du -h "$WASM" | cut -f1))"
    else
      warn "wasm-opt not found, using unoptimized WASM"
      cp "$WASM" "$WASM_OPT"
    fi
    info "WASM build done."
  else
    warn "wasm32-wasi-ghc not found, skipping WASM backend."
    warn "Install via: curl https://gitlab.haskell.org/ghc/ghc-wasm-meta/-/raw/master/bootstrap.sh | sh"
  fi
fi

# ── Precompile standard library ─────────────────────────────────────────────

if [ "$BACKEND" = "all" ] || [ "$BACKEND" = "precompile" ]; then
  info "Building native Koka for precompilation..."
  stack build koka:exe:koka-plain --fast --no-terminal 2>&1 | tail -3

  info "Precompiling all std libraries..."
  KOKA=$(stack exec -- which koka-plain)
  mkdir -p precompiled
  $KOKA --target=js --outputdir=precompiled --library lib/toc.kk 2>&1 | tail -3
  info "Precompiled $(ls precompiled/*.kki 2>/dev/null | wc -l | tr -d ' ') .kki + $(ls precompiled/*.mjs 2>/dev/null | wc -l | tr -d ' ') .mjs files"
fi

# ── Deploy assets to web/public ──────────────────────────────────────────────

if [ "$BACKEND" = "all" ] || [ "$BACKEND" = "web" ] || [ "$BACKEND" = "deploy" ]; then
  info "Deploying assets to web/public/..."
  mkdir -p web/public/lib web/public/precompiled

  # JS compiler bundle
  JSEXE=$(find dist-newstyle -name "koka-playground.jsexe" -type d 2>/dev/null | head -1)
  if [ -n "$JSEXE" ] && [ -f "$JSEXE/all.js" ]; then
    cp "$JSEXE/all.js" web/public/all.js
    info "Copied JS bundle: $(du -h web/public/all.js | cut -f1)"
  else
    warn "JS bundle not found. Build with: ./utils/playground-setup.sh js"
  fi

  # WASM compiler binary (optimized)
  WASM_OPT=$(find dist-newstyle -name "koka-playground.opt.wasm" -path "*/wasm32-wasi/*" 2>/dev/null | head -1)
  if [ -n "$WASM_OPT" ] && [ -f "$WASM_OPT" ]; then
    cp "$WASM_OPT" web/public/koka-playground.wasm
    info "Copied WASM: $(du -h web/public/koka-playground.wasm | cut -f1)"
  else
    warn "WASM binary not found. Build with: ./utils/playground-setup.sh wasm"
  fi

  # Stdlib sources (needed by compiler for inline externs)
  cp -r lib/std web/public/lib/
  info "Copied stdlib sources"

  # Precompiled .kki + .mjs
  if [ -d precompiled ] && ls precompiled/*.kki &>/dev/null; then
    cp precompiled/*.kki precompiled/*.mjs web/public/precompiled/
    info "Copied precompiled files"
  else
    warn "No precompiled files. Run: ./utils/playground-setup.sh precompile"
  fi

  # Generate manifests
  python3 -c "
import json, os
files = []
for root, dirs, fnames in os.walk('web/public/lib/std'):
    if '/v1/' in root: continue
    for f in fnames:
        p = os.path.join(root, f).replace('web/public/lib/', '')
        files.append(p)
print(json.dumps(sorted(files)))
" > web/public/stdlib-manifest.json

  ls web/public/precompiled/ 2>/dev/null | python3 -c "
import sys, json
print(json.dumps(sorted([l.strip() for l in sys.stdin if l.strip()])))
" > web/public/precompiled-manifest.json

  info "Generated manifests: $(python3 -c "import json; print(len(json.load(open('web/public/stdlib-manifest.json'))))" 2>/dev/null || echo '?') stdlib, $(python3 -c "import json; print(len(json.load(open('web/public/precompiled-manifest.json'))))" 2>/dev/null || echo '?') precompiled"
fi

# ── Start web dev server ─────────────────────────────────────────────────────

if [ "$BACKEND" = "web" ]; then
  info "Installing npm dependencies..."
  cd web && npm install

  info ""
  info "=== Ready! ==="
  info "Starting dev server..."
  npx vite --host
fi

if [ "$BACKEND" = "all" ]; then
  info ""
  info "=== Setup complete! ==="
  info ""
  info "Start the dev server:"
  info "  cd web && npm install && npx vite --host"
  info ""
  info "Or just deploy + start:"
  info "  ./utils/playground-setup.sh web"
fi
