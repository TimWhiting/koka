#!/bin/sh
# Build the LIVE tier of the ui tests (real impeller pipeline + injected
# events). Mirrors lib/web-ui/project.kk build-native, plus -i.. so the live
# main can import the shared app+script from test/ui/basic.kk.
set -e
cd "$(dirname "$0")"
root=../../..
imp=$root/lib/ui/api/impeller
sdk=$imp/sdk
[ -d "$sdk/include" ] || { echo "Impeller SDK not found: run $imp/get-sdk.sh first" >&2; exit 1; }
clang -x objective-c -fobjc-arc -dynamiclib $imp/host.m -o $imp/libimpellerhost.dylib \
  -I$sdk/include -I/opt/homebrew/include -L$sdk/lib -L/opt/homebrew/lib -limpeller -lglfw \
  -framework Cocoa -framework Metal -framework QuartzCore -install_name @rpath/libimpellerhost.dylib
# -O1 on purpose: a startup cross-thread refcount race under the platform
# split used to trip HERE deterministically (task #44). It no longer
# reproduces (500+ clean runs at -O1/-O2; best account: structurally
# eliminated by the handler-local uistate store, 071584508) -- building
# optimized keeps this tier the standing regression canary for it.
${KOKA:-koka} --console=raw -O1 -i.. main.kk \
  "--ccopts=-I$sdk/include -I$imp" "--cclib=impeller;impellerhost" \
  "--cclinkopts=-L$sdk/lib -L$imp -Wl,-rpath,$sdk/lib -Wl,-rpath,$imp" \
  -o test-live
echo "built: ./test-live"
