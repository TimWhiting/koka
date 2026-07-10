#!/usr/bin/env bash
# util/test-wasi.sh
#
# Smoke-test a curated subset of test/ under `--target=wasi` (compiled with
# wasi-sdk clang, run under wasmtime) and check that the output matches what
# we expect from the C target. Also runs one `--target=wasi-web` test
# (wasm32-wasip1 core module executed with `node`'s builtin `node:wasi`) to
# exercise std/async's inverted event loop -- see
# lib/std/async/api/wasiweb/evloop.c.
#
# Comparison strategy
# --------------------
# Two comparison modes are used, chosen per-test depending on what the
# existing `<test>.kk.out` file actually contains:
#
#   kkout  - compare wasi stdout directly against test/.../<test>.kk.out.
#            Used for plain `test/cgen/*.kk` tests: their .kk.out files are
#            captured stdout from running the compiled program (no compiler
#            banners, no "load:"/"parse:"/"check:" trace, no type-checker
#            decorations), so they line up 1:1 with `-e` output as long as
#            verbosity is turned off (`-v0`).
#
#   host   - compile+run the test on the *host* C target with the exact same
#            flags, capture its stdout, and diff the wasi output against
#            that instead of against <test>.kk.out. This is used for tests
#            whose .kk.out was produced by a different part of the test
#            harness (e.g. `test/parc/*.kk.out` files are dumps of typed
#            core from a `--core`-style check, not program stdout - most
#            parc/*.kk files don't even have a `main`, so they can't be run
#            at all) or where .kk.out contains harness-normalized textual
#            substitutions that plain `-e` doesn't reproduce (e.g.
#            test/lib/string.kk.out spells `.` as `@`, a markdown-doctest
#            artifact). In both cases the intent of this smoke suite is
#            "wasi behaves the same as the C target", so comparing against
#            fresh host output is the right (and only sound) check.
#
# Every "host" test below was manually verified beforehand to already match
# its intended behavior; this script re-derives host output on each run
# rather than baking in a second copy of expected text, so it can't rot out
# of sync with the C backend.
#
# Known noise this script must not choke on:
#   - mimalloc prints a one-line stderr warning under wasmtime ("page map
#     was committed but not zero initialized"); we always redirect stderr
#     to /dev/null and compare stdout only.
#   - koka's default verbosity (-v1) prints "load:"/"parse:"/"check:"/
#     "linking:"/"created:" trace lines to stdout for `-e`; we pass `-v0` to
#     suppress that so stdout contains only the program's own output.
set -u

# --- locate tools -----------------------------------------------------------

export WASI_SDK_PATH="${WASI_SDK_PATH:-$HOME/wasi-sdk-34.0-rc.1-arm64-macos}"

if [ ! -d "$WASI_SDK_PATH" ]; then
  echo "error: wasi-sdk not found at WASI_SDK_PATH=$WASI_SDK_PATH" >&2
  echo "       install wasi-sdk or set WASI_SDK_PATH to point at it" >&2
  exit 1
fi

if ! command -v wasmtime >/dev/null 2>&1; then
  echo "error: wasmtime not found on PATH (needed to run compiled wasi tests)" >&2
  exit 1
fi

if ! command -v stack >/dev/null 2>&1; then
  echo "error: stack not found on PATH (needed to run 'stack exec koka')" >&2
  exit 1
fi

if ! stack exec koka -- --version >/dev/null 2>&1; then
  echo "error: 'stack exec koka -- --version' failed; build koka first (stack build)" >&2
  exit 1
fi

if ! command -v timeout >/dev/null 2>&1; then
  echo "error: timeout not found on PATH (needed to limit koka build time)" >&2
  echo "       install coreutils (e.g., 'brew install coreutils' on macOS)" >&2
  exit 1
fi

if ! command -v node >/dev/null 2>&1; then
  echo "error: node not found on PATH (needed for the wasi-web test; use node >= 24, e.g. 'nvm use 24')" >&2
  exit 1
fi

# --- test list ---------------------------------------------------------------
# Each entry is "mode|path-without-extension". mode is "kkout" (compare wasi
# stdout to <test>.kk.out), "host" (compare wasi stdout to fresh host output),
# or "wasiweb" (like "kkout" but built+run with --target=wasi-web/node instead
# of --target=wasi/wasmtime -- exercises std/async's inverted event loop, see
# lib/std/async/api/wasiweb/evloop.c).

tests="
kkout|test/cgen/comments1
kkout|test/cgen/ctail11
kkout|test/cgen/assign1
kkout|test/cgen/rec1
kkout|test/cgen/dep1
kkout|test/cgen/mutual1
kkout|test/cgen/open1
kkout|test/cgen/box4
host|test/lib/string
host|test/parc/parc-leak1
host|test/parc/parc-leak1b
host|test/parc/parc23
wasiweb|test/wasiweb/sleep1
"

fail=0

run_koka() {
  # run_koka <target-flags...> -- <file>
  local file="$1"
  shift
  timeout 120 stack exec koka -- -v0 --console=raw "$@" -e "$file" 2>/dev/null
}

for entry in $tests; do
  mode="${entry%%|*}"
  base="${entry#*|}"
  kk="$base.kk"

  if [ ! -f "$kk" ]; then
    echo "FAIL $kk (source file missing)"
    fail=1
    continue
  fi

  case "$mode" in
    wasiweb) wasi_out=$(run_koka "$kk" --target=wasi-web) ;;
    *)       wasi_out=$(run_koka "$kk" --target=wasi) ;;
  esac
  wasi_status=$?
  if [ $wasi_status -ne 0 ]; then
    echo "FAIL $kk (koka wasi exit $wasi_status)"
    fail=1
    continue
  fi

  case "$mode" in
    kkout|wasiweb)
      expected_out=$(cat "$kk.out" 2>/dev/null)
      expected_desc="$kk.out"
      ;;
    host)
      expected_out=$(run_koka "$kk")
      host_status=$?
      if [ $host_status -ne 0 ]; then
        echo "FAIL $kk (koka host reference exit $host_status)"
        fail=1
        continue
      fi
      expected_desc="host C target output"
      ;;
    *)
      echo "FAIL $kk (unknown comparison mode '$mode')"
      fail=1
      continue
      ;;
  esac

  if [ "$wasi_out" = "$expected_out" ]; then
    echo "ok   $kk  (vs $expected_desc)"
  else
    echo "FAIL $kk  (vs $expected_desc)"
    echo "     --- expected ---"
    echo "$expected_out" | sed 's/^/     /'
    echo "     --- got (wasi) ---"
    echo "$wasi_out" | sed 's/^/     /'
    fail=1
  fi
done

exit $fail
