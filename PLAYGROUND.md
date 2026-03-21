# Koka Playground — Browser-Based Compiler

This directory contains the infrastructure for compiling the Koka compiler to JavaScript using GHC's JavaScript backend, enabling an in-browser playground where users can edit, compile, and run Koka programs.

## Architecture

```
┌─────────────────────────────────────┐
│  Web Frontend (web/)                │
│  Monaco editor + VFS + compile/run  │
└──────────────┬──────────────────────┘
               │ globalThis.kokaVFS / kokaCompile
┌──────────────▼──────────────────────┐
│  Koka Compiler (GHC JS backend)    │
│  All 108 modules compiled to JS    │
│  Platform/js/ stubs for IO         │
│  VFS-backed file operations        │
└─────────────────────────────────────┘
```

The JS/TS frontend is the orchestrator:
1. Populates `globalThis.kokaVFS` with source files and cached `.kki` interfaces
2. Calls `globalThis.kokaCompile(moduleName, sourceText)`
3. Reads generated `.mjs` output from VFS
4. Executes the compiled JavaScript

The Haskell compiler runs in the browser, reading/writing through the VFS instead of the real filesystem.

## Prerequisites

### GHC JavaScript Cross-Compiler

The GHC JS backend must be built from source (no pre-built binaries for macOS ARM):

```bash
# Install prerequisites
brew install autoconf automake python
# Ensure emscripten is installed (https://emscripten.org/docs/getting_started/)
source ~/emsdk/emsdk_env.sh

# Clone GHC (shallow)
git clone --recurse-submodules --depth=1 https://gitlab.haskell.org/ghc/ghc.git ~/ghc-js-build
cd ~/ghc-js-build

# Configure for JS target (requires GHC 9.10+ as bootstrap compiler)
./boot
emconfigure ./configure --target=javascript-unknown-ghcjs GHC=$(which ghc)

# Build (~20 minutes on M1)
hadrian/build -j12 --flavour=quick --bignum=native --docs=none

# The cross-compiler is at:
# ~/ghc-js-build/_build/stage1/bin/javascript-unknown-ghcjs-ghc
```

**Note:** If the GHC `settings` file is missing a `"base unit-id"` entry, add it manually:
```bash
# Get the base unit-id
~/ghc-js-build/_build/stage1/bin/javascript-unknown-ghcjs-ghc-pkg field base id
# Add to settings file (before the closing `]`):
# ,("base unit-id", "base-4.XX.0.0-inplace")
```

### Other Requirements

- **cabal-install** 3.16+ (for GHC 9.15 compatibility)
- **hpack** (for regenerating `.cabal` from `package.yaml`)
- **Node.js** 18+ (for testing the compiled output)
- **Emscripten SDK** (for the GHC JS build)

## Building the Koka Library for JavaScript

```bash
cd /path/to/koka  # this worktree

# Ensure GHC JS is on PATH
export PATH=~/ghc-js-build/_build/stage1/bin:$PATH

# Update cabal index (needs head.hackage for GHC 9.15 compat)
cabal update

# Build the library
cabal build lib:koka
```

The `cabal.project.local` is pre-configured with:
- `head.hackage` repository overlay (for GHC HEAD-compatible packages)
- `allow-newer` for base library version constraints
- Cross-compiler paths

## Building the Playground Executable

```bash
cabal build exe:koka-playground
```

This produces a JavaScript file that can be loaded in Node.js or a browser.

## Testing with Node.js

```bash
cd test-js/
node test-playground.js
```

See `test-js/README.md` for details.

## Web Frontend

```bash
cd web/
npm install
npm run dev
```

Opens a local dev server with the Monaco-based playground editor.

## Project Structure

```
├── src/
│   ├── Platform/js/          # JS-specific Platform stubs (7 modules)
│   ├── Common/File.hs        # CPP-guarded for VFS on JS
│   ├── Syntax/Highlight.hs   # CPP-guarded (no Isocline on JS)
│   ├── Lib/Printer.hs        # CPP-guarded (no Isocline on JS)
│   ├── Compile/Options.hs    # playgroundFlags for browser config
│   └── Main/playground/      # JS entry point (callback registration)
├── jsbits/
│   └── vfs.js                # JS VFS bridge functions for FFI
├── web/                      # TypeScript + Monaco playground frontend
│   ├── src/
│   │   ├── main.ts           # Editor + compile/run wiring
│   │   ├── vfs.ts            # KokaVFS class (globalThis.kokaVFS)
│   │   ├── koka-lang.ts      # Monarch tokenizer (from TextMate grammar)
│   │   └── lsp-adapter.ts    # LSP provider scaffold
│   └── index.html
├── cabal.project.local       # head.hackage + GHC JS compiler paths
├── package.yaml              # arch(javascript) conditionals
└── PLAYGROUND.md             # This file
```

## How It Works

### Virtual Filesystem (VFS)

The compiler's IO operations are redirected through a global `kokaVFS` object:

```javascript
globalThis.kokaVFS = {
  readFile:   (path) => string | null | Promise,
  fileExists: (path) => boolean,
  fileTime:   (path) => number,  // ms since epoch
  writeFile:  (path, content) => void,
  listDir:    (path) => string[],
  createDir:  (path) => void,
  dirExists:  (path) => boolean,
  fileSize:   (path) => number,
  removeFile: (path) => void,
};
```

On the JS target, `Common/File.hs` functions like `readTextFile`, `doesFileExist`, etc. call through to these VFS functions via FFI (defined in `jsbits/vfs.js`).

### Platform Abstraction

The `src/Platform/js/` directory provides browser-compatible implementations:
- **Console.hs** — no-op color stubs (no terminal in browser)
- **ReadLine.hs** — no-op REPL stubs
- **Filetime.hs** — stubbed file times (VFS handles freshness)
- **Runtime.hs** — standard GHC exception handling (no C FFI)
- **Var.hs** — IORef-based (single-threaded JS)

### Build Configuration

The `package.yaml` uses `arch(javascript)` conditionals to:
- Swap `src/Platform/cpp` for `src/Platform/js`
- Define `-DKOKA_WEB` CPP flag
- Include `jsbits/vfs.js` as JS sources
- Mark native-only executables (koka, koka-plain, koka-test) as not buildable
- Remove `isocline` dependency (native terminal library)

## Known Issues

- **Int overflow warnings** in `Type/Infer.hs` — JS backend uses 32-bit Int; some literal constants exceed this range. Functionally harmless for most programs but may affect edge cases with very large integer literals.
- **No Template Haskell** — `lsp-types` package can't be used on JS backend. LSP features will use direct function calls instead of the LSP protocol.
- **GHC 9.15 (HEAD)** — Using bleeding-edge GHC; some packages need `head.hackage` overlay. Will stabilize when GHC 9.12 bindists support JS on aarch64-darwin.
