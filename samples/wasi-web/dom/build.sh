#!/usr/bin/env bash
# samples/wasi-web/dom/build.sh
#
# Builds this DOM interop demo for `--target=wasi-web` and produces a
# servable output directory (default: ./out next to this script).
#
# Rev 3 / Core Task 2: `--target=wasi-web` emits a plain wasm32-wasip1 core
# module (no component model, no wit-bindgen, no jco anywhere in this path
# any more -- see ../../../lib/std/async/api/wasiweb/evloop.c and dom.c/
# jsobj.c in this directory). The compiler's own post-link step
# (`wasiWebPostLink` in src/Compile/CodeGen.hs) already emits everything a
# generic wasi-web program needs (`demo.wasm`, `run.mjs`, a generic
# `index.html`, `timers.js`, `vendor/browser_wasi_shim/`) -- this script only
# needs to run the plain `koka --target=wasi-web` build and then swap in this
# sample's own hand-written `index.html` (which additionally implements the
# `koka:dom` import namespace and runs the auto-verify hook), since a plain
# `koka` build has no idea a page wants a `koka:dom`-aware host. No second
# transpile pass, no extra `--cclinkopts` -- `dom.c` and `jsobj.c` are
# ordinary sample-local Koka modules (`dom.kk`/`jsobj.kk`) that the
# compiler's own module-dependency-driven linker (`codeGenLinkC`) already
# links in because `demo.kk` transitively imports them.
#
# Usage:
#   ./build.sh            # build only, leaves ./out ready to serve
#   ./build.sh --serve     # build, then `npx serve ./out` (Ctrl-C to stop)
#
# Requires: WASI_SDK_PATH (wasi-sdk clang), and a `koka` built from this
# repo (via `stack build`) on PATH or reachable through `stack exec koka --`.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(cd "$here/../../.." && pwd)"
outdir="$here/out"

: "${WASI_SDK_PATH:=$HOME/wasi-sdk-34.0-rc.1-arm64-macos}"
export WASI_SDK_PATH
if [ ! -d "$WASI_SDK_PATH" ]; then
  echo "error: wasi-sdk not found at WASI_SDK_PATH=$WASI_SDK_PATH" >&2
  exit 1
fi

koka_cmd=(koka)
if ! command -v koka >/dev/null 2>&1; then
  koka_cmd=(stack exec --cwd "$repo" koka --)
fi

rm -rf "$outdir"

echo "== 1/2: koka --target=wasi-web (links dom.c + jsobj.c via the ordinary module graph) =="
"${koka_cmd[@]}" --target=wasi-web -v1 --buildname=demo --outputdir="$outdir" \
  "$here/demo.kk" -c </dev/null

echo "== 2/2: installing sample-local host page (implements koka:dom + auto-verify) =="
cp "$here/index.html" "$outdir/index.html"

echo
echo "built: $outdir"
echo "serve it, e.g.:"
echo "  npx serve $outdir"
echo "  # or: python3 -m http.server -d $outdir 8080"
echo "then open http://localhost:<port>/index.html"

if [ "${1:-}" = "--serve" ]; then
  echo
  echo "== starting: npx serve $outdir =="
  npx --yes serve "$outdir"
fi
