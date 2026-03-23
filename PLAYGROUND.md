# Koka Playground — Browser-Based Compiler & LSP

Compile, edit, and run Koka programs directly in the browser with full IDE
features (hover, completion, diagnostics, go-to-definition). The Koka compiler
and LSP server run as WASM in Web Workers.

## Architecture

```
┌─────────────────────────────────────────┐
│  Web Frontend (web/)                    │
│  Monaco editor + @codingame/vscode-api  │
│  Code lenses, file browser, VFS        │
└────┬─────────────────────┬──────────────┘
     │ LSP (JSON-RPC)      │ Compile & Run
┌────▼──────────┐   ┌──────▼──────────────┐
│ LSP Worker    │   │ Compiler Worker     │
│ koka-lsp.wasm │   │ koka-playground.wasm│
│ SharedArrayBuf│   │ (fallback)          │
│ stdin/stdout  │   │                     │
└───────────────┘   └─────────────────────┘
```

**Default flow:** LSP (WASM) handles type-checking, hover, completion, diagnostics,
AND compilation via `koka/compile`. Falls back to standalone WASM compiler if needed.
JS backend (`all.js`) loads on demand only when explicitly selected.

## Quick Start (Local Development)

### Prerequisites

- **GHC WASM 9.12** — via ghc-wasm-meta bootstrap
- **GHC 9.12** (native) — for precompiling stdlib
- **Node.js 18+** — for web frontend
- **cabal 3.16+**, **stack**, **hpack**

### Install GHC WASM Backend

```bash
# Install GHC WASM via ghc-wasm-meta
FLAVOUR=9.12 sh <(curl -sL https://gitlab.haskell.org/ghc/ghc-wasm-meta/-/raw/master/bootstrap.sh)
source ~/.ghc-wasm/env
wasm32-wasi-ghc --version
```

### One-Command Setup

```bash
./utils/playground-setup.sh        # Build everything + deploy assets
cd web && npm install && npx vite --host
```

### Step-by-Step Build

```bash
# Generate cabal file
hpack

# Build WASM compiler + LSP server
source ~/.ghc-wasm/env
wasm32-wasi-cabal build lib:koka koka:exe:koka-playground koka:exe:koka-lsp-wasm

# Optimize with wasm-opt
~/.ghc-wasm/binaryen/bin/wasm-opt -Oz \
  $(find dist-newstyle -name "koka-playground.wasm" -path "*/wasm32-wasi/*" | head -1) \
  -o web/public/koka-playground.wasm

~/.ghc-wasm/binaryen/bin/wasm-opt -Oz \
  $(find dist-newstyle -name "koka-lsp-wasm.wasm" -path "*/wasm32-wasi/*" | head -1) \
  -o web/public/koka-lsp.wasm

# Precompile stdlib (uses native compiler)
stack build koka:exe:koka-plain --fast
$(stack exec -- which koka-plain) --target=js --outputdir=precompiled --library lib/toc.kk

# Deploy assets + generate manifests
./utils/playground-setup.sh deploy

# Start dev server
cd web && npm install && npx vite --host
```

### Optional: JS Backend (Fallback)

The JS backend is optional. Build only if you need it as a fallback:

```bash
# Requires emscripten 3.1.74 + GHC JS 9.12.2
source ~/emsdk/emsdk_env.sh
ghcup config add-release-channel cross
emconfigure ghcup install ghc --set javascript-unknown-ghcjs-9.12.2

cabal build lib:koka koka:exe:koka-playground \
  --with-compiler=javascript-unknown-ghcjs-ghc \
  --with-hc-pkg=javascript-unknown-ghcjs-ghc-pkg
```

## LSP Server

The Koka LSP server runs in the browser via WASM, providing:

- **Hover** — type signatures + documentation
- **Completion** — function/type/module completion
- **Diagnostics** — real-time error checking
- **Go-to-definition** — navigate to definitions
- **Document symbols** — outline view
- **Inlay hints** — inferred types
- **Folding ranges** — code folding
- **Code lenses** — "▶ Run" buttons above `fun main()`, `fun test/...()`, `fun example/...()`
- **Compile & run** — `koka/compile` command generates JS, module-runner executes

### LSP Architecture

The LSP uses a forked `lsp` Haskell package with a `-websockets` flag to exclude
the `network` dependency (which can't build on WASI).

Communication uses `SharedArrayBuffer` + `Atomics.wait` for stdin (requires
Cross-Origin Isolation via `coi-serviceworker`). The Haskell `wasiStdinRead`
retries with `threadDelay` when `fd_read` returns empty, allowing GHC green
threads to run (e.g., the `sendServer` thread that writes responses).

Key files:
- `web/src/lsp-worker.ts` — Web Worker with WASI, blocking stdin, LSP stdout capture
- `web/src/lsp-client.ts` — MonacoLanguageClient with custom MessageReader/Writer
- `src/Main/langserver/LanguageServer/Run.hs` — WASM branch with retrying stdin
- `src/Main/langserver/LanguageServer/Conversions.hs` — `inmemory://` URI handling
- `/tmp/lsp-fork/lsp/` — Forked `lsp` package with `-websockets` flag

## CI / Deployment

The GitHub Actions workflow (`.github/workflows/playground.yml`):

1. Installs GHC WASM 9.12 via ghc-wasm-meta bootstrap
2. Builds Koka library, playground compiler, and LSP server for WASM
3. Optimizes both WASM binaries with `wasm-opt -Oz`
4. Precompiles std library with native Koka
5. Builds the Vite web frontend
6. Assembles a static site with `coi-serviceworker` and deploys to GitHub Pages

Enable deployment: repo Settings → Pages → Source: **GitHub Actions**

## Project Structure

```
├── src/
│   ├── Platform/js/          # JS-specific Platform modules (8 modules)
│   ├── Platform/wasm/        # WASM-specific Platform modules (8 modules)
│   ├── Platform/cpp/         # Native Platform modules (default)
│   ├── Common/File.hs        # Delegates IO to Platform.FileIO (no CPP guards)
│   ├── Compile/Options.hs    # playgroundFlags for browser config
│   └── Main/
│       ├── playground/       # Playground entry point (JS/WASM)
│       └── langserver/       # LSP server (shared with native + WASM)
│           └── LanguageServer/
│               ├── Run.hs    # WASM branch: runServerWith + retrying stdin
│               ├── Conversions.hs  # inmemory:// URI support
│               └── Monad.hs  # VFS suffix matching for inmemory:// URIs
├── jsbits/
│   └── vfs.js                # JS VFS bridge functions for FFI
├── web/                      # TypeScript + Vite + Monaco playground
│   ├── src/
│   │   ├── main.ts           # Editor, compile/run, file browser, LSP startup
│   │   ├── vfs.ts            # KokaVFS class (globalThis.kokaVFS)
│   │   ├── lsp-worker.ts     # Web Worker: WASI LSP with SharedArrayBuffer stdin
│   │   ├── lsp-client.ts     # MonacoLanguageClient bridge + compile API
│   │   ├── wasm-runner.ts    # Standalone WASM compiler (fallback)
│   │   ├── wasm-worker.ts    # Web Worker: standalone WASM compiler
│   │   ├── koka-lang.ts      # TextMate grammar + Monarch fallback
│   │   ├── module-runner.ts  # ES module execution via blob URLs
│   │   ├── file-browser.ts   # Tree view with GitHub integration
│   │   └── github-integration.ts  # Fetch samples, load/save Gists
│   ├── index.html
│   └── public/               # Static assets (WASM binaries, stdlib, etc.)
├── .github/workflows/
│   └── playground.yml        # CI: build WASM + LSP + deploy to GitHub Pages
└── PLAYGROUND.md             # This file
```

## Known Limitations

- **Initial type-check is slow** (~30s on WASM) — the LSP recompiles `std/core` from source on first file open because `.kki` files don't contain range maps. Subsequent edits are fast.
- **Int overflow**: WASM/JS backends use 32-bit Int; some literals overflow (warnings only)
- **FBIP samples**: `rbtree.kk` and `rbtree-fbip.kk` crash with BigInt errors
- **Lazy constructors**: `lazycons.kk` not supported on web
- **SharedArrayBuffer**: Requires Cross-Origin Isolation headers (handled by `coi-serviceworker`)
- **No C compiler warnings**: `gcc not found` — harmless, C backend not used in browser
