# Koka Playground — Local Development Setup

This guide explains how to set up the Koka Playground for local development.

## Prerequisites

| Tool | Version | Purpose |
|------|---------|---------|
| GHC (native) | 9.10+ | Bootstrap compiler, native Koka builds |
| cabal | 3.16+ | Building Koka for JS/WASM targets |
| stack | latest | Building native Koka (for precompiling stdlib) |
| hpack | latest | Generate .cabal from package.yaml |
| Node.js | 18+ | Web frontend dev server, testing |
| Emscripten | 3.1.74 | Required by GHC JS 9.12.2 |

### Install GHC + cabal + stack

```bash
# Via ghcup (recommended)
curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
ghcup install ghc 9.12.2
ghcup set ghc 9.12.2
ghcup install cabal 3.16.1.0
ghcup install stack latest
cabal install hpack
```

### Install Emscripten (for JS backend)

```bash
git clone https://github.com/emscripten-core/emsdk.git ~/emsdk
cd ~/emsdk
./emsdk install 3.1.74
./emsdk activate 3.1.74
source ./emsdk_env.sh
```

## Backend Setup

The playground supports two compiler backends. You only need to set up the one(s) you want to work with.

### Option A: GHC JavaScript Backend

```bash
# Add cross-compiler channel and install
ghcup config add-release-channel cross
source ~/emsdk/emsdk_env.sh
emconfigure ghcup install ghc --set javascript-unknown-ghcjs-9.12.2

# Verify
javascript-unknown-ghcjs-ghc --version
# → The Glorious Glasgow Haskell Compilation System, version 9.12.2
```

**Build:**
```bash
cd /path/to/koka   # this repo
hpack
cabal build lib:koka koka:exe:koka-playground \
  --with-compiler=javascript-unknown-ghcjs-ghc \
  --with-hc-pkg=javascript-unknown-ghcjs-ghc-pkg
```

**Test with Node.js:**
```bash
node test-js/run.cjs
# → {"success": true}
```

### Option B: GHC WASM Backend

The WASM backend produces smaller output and supports Template Haskell.

```bash
# Install WASI SDK + GHC WASM via ghc-wasm-meta
# See: https://gitlab.haskell.org/ghc/ghc-wasm-meta
curl https://gitlab.haskell.org/ghc/ghc-wasm-meta/-/raw/master/bootstrap.sh | sh

# Source the environment
source ~/.ghc-wasm/env

# Verify
wasm32-wasi-ghc --version
```

**Build:**
```bash
hpack
source ~/.ghc-wasm/env
cabal build lib:koka koka:exe:koka-playground \
  --with-compiler=wasm32-wasi-ghc \
  --with-hc-pkg=wasm32-wasi-ghc-pkg
```

**Optimize (recommended, reduces 25MB → 8.4MB):**
```bash
WASM=$(find dist-newstyle -name "koka-playground.wasm" -path "*/wasm32-wasi/*")
~/.ghc-wasm/binaryen/bin/wasm-opt -Oz "$WASM" -o "${WASM%.wasm}.opt.wasm"
```

**Test with wasmtime:**
```bash
source ~/.ghc-wasm/env
echo 'module main
fun main()
  println("Hello!")
' | wasmtime --dir=. --dir=$(pwd)/lib::/share/lib \
    $(find dist-newstyle -name "koka-playground.wasm" -path "*/wasm32-wasi/*") main
# → {"success": true}
```

**Test with Node.js:**
```bash
node --experimental-wasi-unstable-preview1 test-js/run-wasm.cjs
```

## Precompile Standard Library

Both backends need the stdlib precompiled for fast compilation in the playground:

```bash
# Build native koka
stack build koka:exe:koka-plain --fast

# Precompile std/core
KOKA=$(stack exec -- which koka-plain)
mkdir -p precompiled
$KOKA --target=js --outputdir=precompiled --library lib/std/core.kk
```

## Run the Web Frontend

```bash
# Set up dev symlinks (run from project root)
mkdir -p web/public

# JS backend output
JSEXE=$(find dist-newstyle -name "koka-playground.jsexe" -type d | head -1)
[ -n "$JSEXE" ] && ln -sf "$JSEXE/all.js" web/public/all.js

# WASM backend output (optimized)
WASM_OPT=$(find dist-newstyle -name "koka-playground.opt.wasm" -path "*/wasm32-wasi/*" | head -1)
[ -n "$WASM_OPT" ] && ln -sf "$WASM_OPT" web/public/koka-playground.wasm

# Stdlib and precompiled files
ln -sf "$(pwd)/lib" web/public/lib
ln -sf "$(pwd)/precompiled" web/public/precompiled

# Generate manifests
python3 -c "
import json, os
files = []
for root, dirs, fnames in os.walk('lib/std'):
    if '/v1/' in root: continue
    for f in fnames:
        files.append(os.path.join(root, f).replace('lib/', ''))
print(json.dumps(sorted(files)))
" > web/public/stdlib-manifest.json

ls precompiled/ | python3 -c "
import sys, json
print(json.dumps(sorted([l.strip() for l in sys.stdin])))
" > web/public/precompiled-manifest.json

# Install web dependencies and start dev server
cd web
npm install
npx vite --host
```

Open the URL shown by Vite (usually http://localhost:5173/).

## Running Tests

```bash
# Native backend tests (C codegen)
stack test --fast --test-arguments="--match cgen"

# JS backend Node.js test
node test-js/run.cjs

# WASM backend Node.js test
node --experimental-wasi-unstable-preview1 test-js/run-wasm.cjs

# Compile a specific file with JS backend
node test-js/run.cjs samples/basic/fibonacci.kk
```

## Project Structure

```
src/Platform/
  cpp/     # Native platform (System.Directory, System.Process, Isocline)
  js/      # JS platform (VFS via globalThis.kokaVFS FFI)
  wasm/    # WASM platform (WASI filesystem, no process execution)

web/src/
  main.ts           # Editor, compiler integration, file browser
  vfs.ts            # Virtual filesystem for JS backend
  wasm-runner.ts    # WASM compiler runner with browser_wasi_shim
  module-runner.ts  # ES module execution via blob URLs
  koka-lang.ts      # TextMate grammar for syntax highlighting
  file-browser.ts   # File tree with GitHub samples
  github-integration.ts  # Fetch samples, Gist save/load

test-js/
  run.cjs           # Node.js E2E test (JS backend)
  run-wasm.cjs      # Node.js E2E test (WASM backend)
```

## Troubleshooting

### `ghc-pkg version mismatch`
Cabal is finding the wrong `ghc-pkg`. Pass `--with-hc-pkg` explicitly:
```bash
cabal build lib:koka --with-compiler=javascript-unknown-ghcjs-ghc \
  --with-hc-pkg=javascript-unknown-ghcjs-ghc-pkg
```

### `isocline not found` on JS/WASM
The `isocline` dependency should be conditional on `!arch(javascript) && !arch(wasm32)`.
Run `hpack` to regenerate `koka.cabal` from `package.yaml`.

### WASM: `emconfigure` errors
Make sure you have the correct emscripten version:
```bash
emcc --version  # Should show 3.1.74 for GHC JS 9.12.2
```

### Tests fail with `mimalloc.h not found`
Initialize git submodules:
```bash
git submodule update --init --recursive
```
