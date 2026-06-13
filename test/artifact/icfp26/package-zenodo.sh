#!/usr/bin/env bash
#
# package-zenodo.sh — build the *source* archive uploaded to Zenodo for the
# ICFP'26 HMCFA artifact ("A Precise and Practical Big-Step Control Flow
# Analysis for Effect Handlers").
#
# The archive is a clean snapshot of the committed source tree PLUS the
# contents of every git submodule:
#
#   * Using `git archive` means only TRACKED files are exported, so every local
#     build/cache directory is omitted automatically and we do not have to
#     maintain a fragile denylist — .git, .stack-work, .koka, .worktrees,
#     .venv, lean/.lake, benchmarks/results, __pycache__, etc. are all gitignored
#     or untracked and therefore never appear in the archive.
#
#   * Submodules are exported explicitly (see below). This is the important
#     part: plain `git archive` silently drops submodules, which is why
#     kklib/mimalloc — required to build the Koka runtime — was missing from the
#     previous Zenodo upload.
#
#   * The reference benchmark results (benchmarks/results-cached/) are overlaid
#     from an external cache directory. In the repository this path is a git
#     "gitlink" with no checked-out contents, so — like a submodule — git archive
#     would otherwise leave it empty. These are the cached results the figure
#     scripts fall back to (and validate.py checks against).
#
# Usage:
#   test/artifact/icfp26/package-zenodo.sh [VERSION] [RESULTS_CACHE]
#       VERSION        archive version tag           (default: 1.0)
#       RESULTS_CACHE  dir of cached benchmark JSON   (default: $HOME/results-cached-submitted;
#                                                      also settable via the RESULTS_CACHE env var)
#
# Output:
#   icfp26-hmcfa-<VERSION>-source.zip   (written to the repository root)
#
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"

VERSION="${1:-1.0}"
RESULTS_CACHE="${2:-${RESULTS_CACHE:-$HOME/results-cached-submitted}}"
PREFIX="koka"                                   # top-level dir inside the archive
OUT="$ROOT/icfp26-hmcfa-${VERSION}-source.zip"
STAGE="$(mktemp -d)"
trap 'rm -rf "$STAGE"' EXIT

echo ">> Exporting committed source tree (tracked files only) ..."
git archive --format=tar --prefix="${PREFIX}/" HEAD | tar -x -C "$STAGE"

echo ">> Exporting git submodules ..."
# Read submodule paths straight from .gitmodules. We deliberately do NOT use
# `git submodule status`, which can silently omit an initialized submodule
# (that is exactly how kklib/mimalloc slipped through the previous packaging).
git config --file .gitmodules --get-regexp '^submodule\..*\.path$' \
  | awk '{print $2}' \
  | while read -r sm; do
      if git -C "$sm" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
        echo "   + $sm"
        git -C "$sm" archive --format=tar --prefix="${PREFIX}/${sm}/" HEAD \
          | tar -x -C "$STAGE"
      else
        echo "   ! skipping uninitialized submodule: $sm" >&2
        echo "     (run: git submodule update --init --recursive, then re-run)" >&2
      fi
    done

# kklib/mimalloc is required to build the Koka runtime — fail loudly if absent.
if [ ! -f "$STAGE/${PREFIX}/kklib/mimalloc/CMakeLists.txt" ]; then
  echo "ERROR: kklib/mimalloc is missing from the staged archive." >&2
  echo "       Run: git submodule update --init --recursive   and try again." >&2
  exit 1
fi

echo ">> Overlaying cached benchmark results from $RESULTS_CACHE ..."
DEST="$STAGE/${PREFIX}/benchmarks/results-cached"
if [ -d "$RESULTS_CACHE" ]; then
  rm -rf "$DEST"                       # drop the empty gitlink placeholder, if any
  mkdir -p "$DEST"
  cp -R "$RESULTS_CACHE"/. "$DEST"/    # copy cache *contents* (dmcfae/ dmcfar/ kcfa/ ...)
  rm -rf "$DEST/.git"                  # never ship a nested git repo
  CACHE_FILES="$(find "$DEST" -type f | wc -l | tr -d ' ')"
  echo "   + $CACHE_FILES result files"
else
  echo "ERROR: results cache not found at: $RESULTS_CACHE" >&2
  echo "       Pass the cache dir as the 2nd argument or set RESULTS_CACHE=..." >&2
  exit 1
fi

echo ">> Creating $OUT ..."
rm -f "$OUT"
( cd "$STAGE" && zip -q -r -X "$OUT" "$PREFIX" )

echo ">> Done."
# Materialize the entry list once and use here-strings for inspection: a piped
# `grep -q` would short-circuit and SIGPIPE its upstream, which `set -o pipefail`
# would then report as a (spurious) failure.
LISTING="$(unzip -Z1 "$OUT")"
printf '   archive : %s\n' "$OUT"
printf '   size    : %s\n' "$(du -h "$OUT" | cut -f1)"
printf '   entries : %s\n' "$(grep -c '' <<< "$LISTING")"
echo ">> Sanity checks:"
if grep -q "^${PREFIX}/kklib/mimalloc/CMakeLists.txt$" <<< "$LISTING"; then
  echo "   OK: ${PREFIX}/kklib/mimalloc/ is included"
else
  echo "   FAIL: kklib/mimalloc missing from final zip" >&2
  exit 1
fi
CACHE_IN_ZIP="$(grep -c "^${PREFIX}/benchmarks/results-cached/.*\.json$" <<< "$LISTING" || true)"
if [ "$CACHE_IN_ZIP" -gt 0 ]; then
  echo "   OK: ${PREFIX}/benchmarks/results-cached/ has $CACHE_IN_ZIP JSON result files"
else
  echo "   FAIL: no cached results in final zip" >&2
  exit 1
fi
