#!/usr/bin/env bash
# util/test-wasi.sh
#
# Smoke-test a curated subset of test/ under `--target=wasi` (compiled with
# wasi-sdk clang, run under wasmtime) and check that the output matches what
# we expect from the C target. Also runs a set of `--target=wasi-web` tests
# (wasm32-wasip1 core modules executed with `node`'s builtin `node:wasi`) to
# exercise std/async's inverted event loop -- from a single timer (sleep1) up
# to strand-heavy interleaving, `forking` supervisors parking on channels, and
# thousands of synchronous channel hops per host dispatch -- see
# lib/std/async/api/wasiweb/evloop.c and test/wasiweb/{inter2,forking1,pingpong}.kk.
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
wasiweb|test/wasiweb/inter2
wasiweb|test/wasiweb/forking1
wasiweb|test/wasiweb/pingpong
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

# --- ui/test headless UI tests (native; no window, display, or browser) -----
# The lib/ui test harness drives an app through its real channels/strands with
# deterministic text metrics; clicks dispatch through the shared `hit` walk.
for t in test/ui/*.kk; do
  [ -e "$t" ] || continue
  if out=$(timeout 300 stack exec koka -- -v0 --console=raw -itest/ui -e "$t" 2>/dev/null); then
    echo "ok   $t  (ui/test headless)"
  else
    echo "FAIL $t  (ui/test headless)"
    echo "$out" | sed 's/^/     /'
    fail=1
  fi
done

# --- ui/test headless on wasi-web: the FOURTH runtime for the same scripts --
# (wasm32-wasip1 core module under node:wasi; task #41 unblocked this tier).
# basic.kk only for now -- the other headless suites are expected to work but
# are unvalidated on this target; extend the list once someone has watched
# them pass. Needs node >= 24 (the runner's node:wasi surface).
node_major=$(node -v 2>/dev/null | sed 's/^v//' | cut -d. -f1)
if [ "${node_major:-0}" -ge 24 ]; then
  # `-e` does not propagate the child's exit code, so judge by output
  uiww_out=$(timeout 600 stack exec koka -- -v0 --console=raw -itest/ui --target=wasi-web -e test/ui/basic.kk 2>/dev/null)
  if echo "$uiww_out" | grep -q "checks passed" && ! echo "$uiww_out" | grep -q "FAIL"; then
    echo "ok   test/ui/basic.kk --target=wasi-web (ui/test headless, wasi core module)"
  else
    echo "FAIL test/ui/basic.kk --target=wasi-web"
    echo "$uiww_out" | sed 's/^/     /'
    fail=1
  fi
else
  echo "skip test/ui/basic.kk --target=wasi-web (node >= 24 required; found $(node -v 2>/dev/null || echo none))"
fi

# --- ui/test LIVE tiers: the same script against the real pipelines --------
# native: real impeller window + host-ring event injection (exit code)
if [ -e test/ui/live/build.sh ]; then
  if KOKA="stack exec koka --" timeout 700 ./test/ui/live/build.sh >/dev/null 2>&1 \
     && ( cd test/ui/live && timeout 120 ./test-live >/dev/null 2>&1 ); then
    echo "ok   test/ui/live  (native live: real impeller pipeline)"
  else
    echo "FAIL test/ui/live  (native live)"
    fail=1
  fi
  if ( cd test/ui/live && timeout 120 ./test-live windows >/dev/null 2>&1 ); then
    echo "ok   test/ui/live windows  (native live: real multi-window pipeline)"
  else
    echo "FAIL test/ui/live windows  (native live)"
    fail=1
  fi
fi

# --- native (Impeller) measure-path regression: rich-measure.kk ------------
# Calls the REAL `measure-native`/`measure-rich-native` directly (no window
# needed -- paragraph shaping is CPU-only). This is the regression for the
# `rich` text-loss bug that shipped past a fully green `test/ui/*.kk` loop
# above, because every one of those routes through `ui/test`'s deterministic
# measurer instead of the real backend -- see test/ui/native/rich-measure.kk's
# header comment. Needs the same Impeller SDK ccopts/cclib/cclinkopts
# `test/ui/live/build.sh` uses above, so it's gated the same way.
if [ -d "lib/ui/api/impeller/sdk/include" ]; then
  imp=lib/ui/api/impeller
  sdk=$imp/sdk
  if rm_out=$(timeout 120 stack exec koka -- -v0 --console=raw -e test/ui/native/rich-measure.kk \
       "--ccopts=-I$sdk/include -I$imp" "--cclib=impeller;impellerhost" \
       "--cclinkopts=-L$sdk/lib -L$imp -Wl,-rpath,$sdk/lib -Wl,-rpath,$imp" 2>&1); then
    echo "ok   test/ui/native/rich-measure.kk  (native: real measure-rich-native path)"
  else
    echo "FAIL test/ui/native/rich-measure.kk  (native measure-rich-native regression)"
    echo "$rm_out" | sed 's/^/     /'
    fail=1
  fi
else
  echo "skip test/ui/native/rich-measure.kk (Impeller SDK not present; run lib/ui/api/impeller/get-sdk.sh)"
fi

# --- web (jsweb) measure-path regression: rich-text-web.mjs -----------------
# Same rationale as the native rich-measure.kk block above, for the OTHER
# backend: calls the REAL `kk_dom_measure_rich_box` extern
# (lib/web-ui/api/jsweb/dom.js) directly, behind a small fixed-width DOM
# stub (no browser/Chrome needed -- just node). test/ui/rich-text.kk and
# every other headless suite above route through ui/test's deterministic
# measurer and never reach this extern at all.
if rtw_out=$(timeout 60 node test/ui/rich-text-web.mjs 2>&1); then
  echo "ok   test/ui/rich-text-web.mjs  (jsweb: real measure-rich-box path)"
else
  echo "FAIL test/ui/rich-text-web.mjs  (jsweb measure-rich-box regression)"
  echo "$rtw_out" | sed 's/^/     /'
  fail=1
fi

# --- framework SPA browser test (headless Chrome; skipped if unavailable) ----
# Builds samples/wasi-web/framework/todo and asserts its self-driving verify
# hook's title: routing, two components, async spawn, keyed reconciliation,
# and Perceus slot release on unmount. See that directory's readme.md.

chrome=""
for c in "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome" \
         "$(command -v google-chrome 2>/dev/null)" \
         "$(command -v chromium 2>/dev/null)"; do
  if [ -n "$c" ] && [ -x "$c" ]; then chrome="$c"; break; fi
done

spa_expected="spa:todos=1/2 done;counter=12;routefreed=yes;back=1/2 done;keyed=yes;drag=yes;coords=yes;stable=yes;theme=yes;detached=0"
spa_expected_js="spa:todos=1/2 done;counter=12;routefreed=n/a;back=1/2 done;keyed=yes;drag=yes;coords=yes;stable=yes;theme=yes;detached=0"
if [ -z "$chrome" ] || ! command -v python3 >/dev/null 2>&1; then
  echo "skip samples/web-ui/todos (headless Chrome or python3 not available)"
else
  spa_dir="samples/web-ui/todos"
  if ( cd "$spa_dir" && \
       KOKA="stack exec koka --" timeout 400 stack exec koka -- -v0 --console=raw -e build.kk ) >/dev/null 2>&1; then
    port=8641
    ( cd "$spa_dir/out" && python3 -m http.server $port >/dev/null 2>&1 ) &
    server=$!
    sleep 1
    title=$("$chrome" --headless=new --dump-dom --virtual-time-budget=8000 \
              "http://localhost:$port/" 2>/dev/null \
            | grep -oE "<title>[^<]*</title>" | sed -e 's|<title>||' -e 's|</title>||')
    kill $server 2>/dev/null
    if [ "$title" = "$spa_expected" ]; then
      echo "ok   $spa_dir (browser: $title)"
    else
      echo "FAIL $spa_dir (browser title '$title' != '$spa_expected')"
      fail=1
    fi
  else
    echo "FAIL $spa_dir (koka -e build.kk failed)"
    fail=1
  fi

  # same SPA on the javascript backend (no wasi-sdk involved)
  if ( cd "$spa_dir" && \
       KOKA="stack exec koka --" timeout 400 stack exec koka -- -v0 --console=raw -e build.kk -- jsweb ) >/dev/null 2>&1; then
    port=8642
    ( cd "$spa_dir/out-js" && python3 -m http.server $port >/dev/null 2>&1 ) &
    server=$!
    sleep 1
    title=$("$chrome" --headless=new --dump-dom --virtual-time-budget=8000 \
              "http://localhost:$port/" 2>/dev/null \
            | grep -oE "<title>[^<]*</title>" | sed -e 's|<title>||' -e 's|</title>||')
    kill $server 2>/dev/null
    if [ "$title" = "$spa_expected_js" ]; then
      echo "ok   $spa_dir --target=jsweb (browser: $title)"
    else
      echo "FAIL $spa_dir --target=jsweb (browser title '$title' != '$spa_expected_js')"
      fail=1
    fi
  else
    echo "FAIL $spa_dir --target=jsweb (koka -e build.kk -- jsweb failed)"
    fail=1
  fi
fi

# --- unified ui framework: the SAME widget code on both web backends --------
# samples/ui/todos is a portable widget<msg> SPA (text input, keyed list,
# routing, async, theme). Its self-driver (index.html ?drive) types two
# items, marks one done, and switches to the counter page. The native
# backend (Impeller) is smoke-checked separately below.

ui_expected="ui-spa:added=2;done=yes;counter=yes;expand=yes"
if [ -n "$chrome" ] && command -v python3 >/dev/null 2>&1; then
  ui_dir="samples/ui/todos"
  run_ui_web() {   # <target-flag> <outdir> <port>
    local flag="$1" outdir="$2" port="$3" label="$4"
    if ( cd "$ui_dir" && \
         KOKA="stack exec koka --" timeout 400 stack exec koka -- -v0 --console=raw -e build.kk $flag ) >/dev/null 2>&1; then
      ( cd "$ui_dir/$outdir" && python3 -m http.server $port >/dev/null 2>&1 ) &
      local server=$!
      sleep 1
      local title=$("$chrome" --headless=new --dump-dom --virtual-time-budget=8000 \
                "http://localhost:$port/?drive" 2>/dev/null \
              | grep -oE "<title>[^<]*</title>" | sed -e 's|<title>||' -e 's|</title>||')
      kill $server 2>/dev/null
      if [ "$title" = "$ui_expected" ]; then
        echo "ok   $ui_dir --target=$label (browser: $title)"
      else
        echo "FAIL $ui_dir --target=$label ('$title' != '$ui_expected')"
        fail=1
      fi
    else
      echo "FAIL $ui_dir --target=$label (build failed)"
      fail=1
    fi
  }
  run_ui_web "" out 8643 wasi-web
  run_ui_web "-- jsweb" out-js 8644 jsweb
else
  echo "skip samples/ui/todos (headless Chrome or python3 not available)"
fi

# --- ui/overlay: the portable overlay layer (context menu / dropdown / modal) --
# samples/ui/overlay floats context menus, a dropdown and a dimmed modal dialog
# via ui/overlay (all composited at the root as a `stack`, no backend change).
# Its ?drive self-driver opens a cursor-anchored menu (on-click-at), clicks an
# item (dispatch + close), dismisses via a scrim click, opens the dropdown menu,
# and opens/closes the modal (with a dimmed scrim). jsweb only (standalone).

ovl_expected="overlay:menu=yes;pick=yes;menuclosed=yes;scrim=yes;dropdown=yes;sorted=yes;dialog=yes;dim=yes;dialogclosed=yes;drop=yes"
if [ -n "$chrome" ] && command -v python3 >/dev/null 2>&1; then
  ovl_dir="samples/ui/overlay"
  if ( cd "$ovl_dir" && \
       KOKA="stack exec koka --" timeout 400 stack exec koka -- -v0 --console=raw -e build.kk -- jsweb ) >/dev/null 2>&1; then
    port=8645
    ( cd "$ovl_dir/out-js" && python3 -m http.server $port >/dev/null 2>&1 ) &
    server=$!
    sleep 1
    title=$("$chrome" --headless=new --dump-dom --virtual-time-budget=10000 \
              "http://localhost:$port/?drive" 2>/dev/null \
            | grep -oE "<title>[^<]*</title>" | sed -e 's|<title>||' -e 's|</title>||')
    kill $server 2>/dev/null
    if [ "$title" = "$ovl_expected" ]; then
      echo "ok   $ovl_dir --target=jsweb (browser: $title)"
    else
      echo "FAIL $ovl_dir --target=jsweb ('$title' != '$ovl_expected')"
      fail=1
    fi
  else
    echo "FAIL $ovl_dir --target=jsweb (build failed)"
    fail=1
  fi
else
  echo "skip samples/ui/overlay (headless Chrome or python3 not available)"
fi

# --- ui/threads: data-offload threading (compute on a worker thread) --------
# samples/ui/threads offloads a heavy pure fib(38) via `compute` (a libuv
# threadpool thread natively; a cooperative strand on web). Its ?drive self-test
# presses Compute and asserts the offloaded result returns AND the tick loop ran.
# jsweb only here (the "UI stays live during compute" property is native).

thr_expected="threads:result=yes;ticked=yes"
if [ -n "$chrome" ] && command -v python3 >/dev/null 2>&1; then
  thr_dir="samples/ui/threads"
  if ( cd "$thr_dir" && \
       KOKA="stack exec koka --" timeout 400 stack exec koka -- -v0 --console=raw -e build.kk -- jsweb ) >/dev/null 2>&1; then
    port=8646
    ( cd "$thr_dir/out-js" && python3 -m http.server $port >/dev/null 2>&1 ) &
    server=$!
    sleep 1
    title=$("$chrome" --headless=new --dump-dom --virtual-time-budget=15000 \
              "http://localhost:$port/?drive" 2>/dev/null \
            | grep -oE "<title>[^<]*</title>" | sed -e 's|<title>||' -e 's|</title>||')
    kill $server 2>/dev/null
    if [ "$title" = "$thr_expected" ]; then
      echo "ok   $thr_dir --target=jsweb (browser: $title)"
    else
      echo "FAIL $thr_dir --target=jsweb ('$title' != '$thr_expected')"
      fail=1
    fi
  else
    echo "FAIL $thr_dir --target=jsweb (build failed)"
    fail=1
  fi
else
  echo "skip samples/ui/threads (headless Chrome or python3 not available)"
fi

# --- std/async threading primitive: thread-safe channel + spawn-thread -------
# test/async/xthread spawns a persistent worker thread (its own async loop) that
# xemits values across the thread boundary into a channel the main loop receives.
# Real OS threads -> native host only (skipped under wasi).
xthr_expected="received: [10,20,30,40,50]
sum: 150"
xthr_got=$(run_koka "test/async/xthread.kk")
if [ "$xthr_got" = "$xthr_expected" ]; then
  echo "ok   test/async/xthread  (native: thread-safe channel + spawn-thread)"
else
  echo "FAIL test/async/xthread  (native threading primitive)"
  echo "     --- expected ---"; echo "$xthr_expected" | sed 's/^/     /'
  echo "     --- got ---";      echo "$xthr_got"      | sed 's/^/     /'
  fail=1
fi

# --- native (Impeller) smoke: build + auto-close each ui sample -------------
# Skipped unless the Impeller SDK is present (lib/ui/api/impeller/sdk).
if [ -d "lib/ui/api/impeller/sdk/include" ]; then
  for s in counter conway flying todos material scroll site overlay threads windows lazy gallery; do
    if ( cd "samples/ui/$s" && \
         KOKA="stack exec koka --" timeout 400 stack exec koka -- -v0 --console=raw -e build.kk -- native ) >/dev/null 2>&1 \
       && ( cd "samples/ui/$s" && KOKA_IMP_FRAMES=30 timeout 30 ./app-native ) >/dev/null 2>&1; then
      echo "ok   samples/ui/$s --target=native (built + ran 30 frames)"
    else
      echo "FAIL samples/ui/$s --target=native"
      fail=1
    fi
  done
else
  echo "skip samples/ui/* --target=native (Impeller SDK not present; run lib/ui/api/impeller/get-sdk.sh)"
fi

# --- ui/test web LIVE tier: real DOM events in headless Chrome --------------
# (chrome/python detection above; probe = the page title set by test-report)
if [ -n "$chrome" ] && command -v python3 >/dev/null 2>&1; then
  if ( cd test/ui/live && KOKA="stack exec koka -- -i.." timeout 700 stack exec koka -- -v0 --console=raw -e build.kk -- jsweb ) >/dev/null 2>&1 \
     && [ -d test/ui/live/out-js ]; then
    ( cd test/ui/live/out-js && python3 -m http.server 8647 > /dev/null 2>&1 ) &
    live_srv=$!
    sleep 1
    live_title=$(timeout 150 "$chrome" --headless --disable-gpu --virtual-time-budget=120000 \
                   --dump-dom http://localhost:8647/index.html 2>/dev/null | grep -oE '<title>[^<]*' | head -1)
    kill $live_srv 2>/dev/null
    case "$live_title" in
      *uitest:pass:20*) echo "ok   test/ui/live --target=jsweb (web live: $live_title)" ;;   # 20 = shared-scenario count (15, matches headless/native-live) + async-image-web's 5 (task 4, web parity)
      *) echo "FAIL test/ui/live --target=jsweb (title '$live_title')"; fail=1 ;;
    esac
  else
    echo "FAIL test/ui/live --target=jsweb (build)"
    fail=1
  fi
else
  echo "skip test/ui/live --target=jsweb (headless Chrome or python3 not available)"
fi

exit $fail
