#!/usr/bin/env bash
# Fetch the Impeller standalone SDK (impeller.h + libimpeller.dylib) for the
# pinned Flutter engine commit. No Dart, no engine build -- prebuilt per
# engine commit; see lib readme. The install name is fixed to @rpath so the
# sample binary can carry its own rpath.
set -euo pipefail
sha="83675ed27633283e7fc296c8bca22e841224c096"   # engine.version of flutter stable 2026-07
platform="darwin-arm64"
here="$(cd "$(dirname "$0")" && pwd)"
mkdir -p "$here/sdk"
cd "$here/sdk"
curl -sfLo impeller_sdk.zip "https://storage.googleapis.com/flutter_infra_release/flutter/$sha/$platform/impeller_sdk.zip"
unzip -o -q impeller_sdk.zip
install_name_tool -id @rpath/libimpeller.dylib lib/libimpeller.dylib
echo "sdk ready: $here/sdk (engine $sha, $platform)"
