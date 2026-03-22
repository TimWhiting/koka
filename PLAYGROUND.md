# Koka Playground — Browser-Based Compiler

Compile, edit, and run Koka programs directly in the browser. The Koka compiler
itself runs as JavaScript (compiled via GHC's JS backend), with a Monaco-based
editor frontend.

## Architecture

```
┌─────────────────────────────────────┐
│  Web Frontend (web/)                │
│  Monaco editor + VFS + compile/run  │
└──────────────┬──────────────────────┘
               │ globalThis.kokaVFS / kokaCompile
┌──────────────▼──────────────────────┐
│  Koka Compiler (GHC JS backend)    │
│  All 109 modules compiled to JS    │
│  Platform/js/ stubs for IO         │
│  VFS-backed file operations        │
└─────────────────────────────────────┘
```

## Quick Start (Local Development)

### Prerequisites

- **Emscripten 3.1.74** — required by GHC JS 9.12.2
- **GHC 9.12.2** (native) — for bootstrap and native builds
- **GHC JS cross-compiler** — installed via ghcup
- **Node.js 18+** — for testing and web frontend
- **cabal 3.16+**, **stack**, **hpack**

### Install GHC JS Cross-Compiler

```bash
# Install emscripten 3.1.74
cd ~/emsdk
./emsdk install 3.1.74
./emsdk activate 3.1.74
source ./emsdk_env.sh

# Install GHC JS via ghcup
ghcup config add-release-channel cross
emconfigure ghcup install ghc --set javascript-unknown-ghcjs-9.12.2

# Verify
javascript-unknown-ghcjs-ghc --version
```

### Build the Compiler for JavaScript

```bash
# Generate cabal file from package.yaml
hpack

# Build the library and playground executable
cabal build lib:koka koka:exe:koka-playground \
  --with-compiler=javascript-unknown-ghcjs-ghc \
  --with-hc-pkg=javascript-unknown-ghcjs-ghc-pkg
```

GHC 9.12.2 produces valid output with no post-processing needed.

### Precompile Standard Library

```bash
# Build native koka for precompiling
stack build koka:exe:koka-plain --fast

# Precompile std/core to .kki + .mjs
KOKA=$(stack exec -- which koka-plain)
mkdir -p precompiled
$KOKA --target=js --outputdir=precompiled --library lib/std/core.kk
```

### Run the Web Frontend

```bash
# Set up dev symlinks
JSEXE=$(find dist-newstyle -name "koka-playground.jsexe" -type d | head -1)
mkdir -p web/public
ln -sf $JSEXE/all.js web/public/all.js
ln -sf $(pwd)/lib web/public/lib
ln -sf $(pwd)/precompiled web/public/precompiled

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

# Start dev server
cd web && npm install && npx vite --host
```

### Test with Node.js

```bash
node test-js/run.cjs                    # Hello World
node test-js/run.cjs samples/basic/fibonacci.kk  # Specific file
```

## CI / Deployment

The GitHub Actions workflow (`.github/workflows/playground.yml`):

1. Installs GHC JS 9.12.2 via ghcup (~2 min, pre-built bindist)
2. Builds Koka library + playground for JS target
3. Precompiles std library with native Koka
4. Builds the Vite web frontend
5. Assembles a static site and deploys to GitHub Pages

Enable deployment: repo Settings → Pages → Source: **GitHub Actions**

The playground will be at `https://<username>.github.io/koka/`

## Project Structure

```
├── src/
│   ├── Platform/js/          # JS-specific Platform modules (8 modules)
│   │   ├── FileIO.hs         # VFS-backed doesFileExist, readTextFile, etc.
│   │   ├── Filetime.hs       # VFS-backed file times via FFI
│   │   ├── Console.hs        # No-op console stubs
│   │   ├── ReadLine.hs       # No-op REPL stubs
│   │   ├── Runtime.hs        # Standard GHC exception handling
│   │   ├── Var.hs            # IORef-based (single-threaded JS)
│   │   ├── Config.hs         # Hardcoded web config
│   │   └── GetOptions.hs     # Re-export GetOpt
│   ├── Common/File.hs        # Delegates IO to Platform.FileIO (no CPP guards)
│   ├── Compile/Options.hs    # playgroundFlags for browser config
│   └── Main/playground/      # JS entry point (callback registration)
├── jsbits/
│   └── vfs.js                # JS VFS bridge functions for FFI
├── web/                      # TypeScript + Vite + Monaco playground
│   ├── src/
│   │   ├── main.ts           # Editor, compile/run, file browser
│   │   ├── vfs.ts            # KokaVFS class (globalThis.kokaVFS)
│   │   ├── koka-lang.ts      # TextMate grammar + Monarch fallback
│   │   ├── module-runner.ts  # ES module execution via blob URLs
│   │   ├── file-browser.ts   # Tree view with GitHub integration
│   │   ├── github-integration.ts  # Fetch samples, load/save Gists
│   │   └── lsp-adapter.ts    # LSP provider scaffold
│   └── index.html
├── test-js/
│   └── run.cjs               # Node.js end-to-end test
├── .github/workflows/
│   └── playground.yml         # CI: build + deploy to GitHub Pages
└── PLAYGROUND.md              # This file
```

## How It Works

### Virtual Filesystem (VFS)

The compiler's IO operations go through `Platform.FileIO` which on the JS
target delegates to `globalThis.kokaVFS` via FFI:

```javascript
globalThis.kokaVFS = {
  readFile:   (path) => string | null,
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

### Precompiled Standard Library

The `.kki` interface files are placed at `/lib/js-debug/` in the VFS with
far-future timestamps. The compiler recognizes these as cached and skips
recompilation — only the user's module is parsed, type-checked, and code-generated.

### Platform Abstraction

All platform-specific IO is in `Platform/` modules (no CPP in caller code):
- `Platform.FileIO` — filesystem operations (VFS on JS, System.Directory on native)
- `Platform.Filetime` — file modification times (VFS on JS, Data.Time on native)
- `Platform.Console` — terminal colors (no-op on JS)
- `Platform.ReadLine` — REPL input (no-op on JS)

### GHC JS Backend Notes

- **GHC 9.12.2** with **emscripten 3.1.74** produces valid output with no patching
- The embedded WASM is a base64 data URI with zero imports
- Output is ~44MB uncompressed, ~2.3MB with brotli (served automatically by CDNs)
- Minification is counterproductive — repetitive GHC output compresses better unminified

### Known Limitations

- **Int overflow**: JS backend uses 32-bit Int; some literals in `Type/Infer.hs` overflow (warnings only)
- **FBIP samples**: `rbtree.kk` and `rbtree-fbip.kk` crash with BigInt errors (JS backend bug)
- **Lazy constructors**: `lazycons.kk` not supported on web
- **No Template Haskell**: `lsp-types` package can't be used on JS backend
- **No LSP server**: Full LSP requires packages that depend on TH; future work will expose query functions directly
