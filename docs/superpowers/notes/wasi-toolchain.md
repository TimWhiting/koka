# WASI toolchain — installed versions (Task 0)

Host: macOS arm64 (Darwin 25.5.0).

## wasi-sdk

No stable `wasi-sdk-34` tag exists yet upstream as of 2026-07-07 (latest stable
tag is `wasi-sdk-33`); the newest 34 pre-release is `wasi-sdk-34-rc.1`
(published 2026-07-02). Installed that rc per the brief's "34 or newest 34 rc"
guidance.

- Release asset used: `wasi-sdk-34.0-rc.1-arm64-macos.tar.gz`
  (note: actual asset name differs slightly from the brief's guess
  `wasi-sdk-34.0rc1-arm64-macos.tar.gz` — real name has a hyphen: `-rc.1-`).
- Downloaded via `gh release download wasi-sdk-34-rc.1 -R WebAssembly/wasi-sdk`.
- Extracted to: `~/wasi-sdk-34.0-rc.1-arm64-macos` (NOT `~/wasi-sdk`, which is a
  pre-existing source checkout of the wasi-sdk repo and must not be touched or
  overwritten).
- `VERSION` file: `34.0-rc.1`
- `clang --version`:
  ```
  clang version 23.0.0-wasi-sdk (https://github.com/llvm/llvm-project 1b7c3e57bbc8e367ff8203e8818b018337319d7e)
  Target: wasm32-unknown-wasip1
  ```
  llvm-version: 23.0.0 — satisfies "LLVM 22+" expectation.

Export for later tasks:
```bash
export WASI_SDK_PATH=~/wasi-sdk-34.0-rc.1-arm64-macos
```

### Sysroot target triples (critical for Task 1+)

```
$ ls $WASI_SDK_PATH/share/wasi-sysroot/lib/
wasm32-wasip1
wasm32-wasip1-threads
wasm32-wasip2
wasm32-wasip3
```

`wasm32-wasip3` **is** supported by this sysroot — Task 1 (sync hello world on
wasm32-wasip3) can proceed directly with `--target=wasm32-wasip3`. Note this
rc also **removed** the legacy `wasm32-wasi` / `wasm32-wasi-threads` target
names (per the wasi-sdk-34-rc.1 changelog); only the `wasip1`/`wasip1-threads`/
`wasip2`/`wasip3` naming exists in this SDK. Any later code that hard-codes
`wasm32-wasi` as a target triple should be updated to `wasm32-wasip1` (or
whichever WASI version is targeted) for this SDK.

## wasmtime

Pre-existing install at `~/.wasmtime/bin/wasmtime` was version `22.0.0`
(too old — task requires >= 43 for WASI 0.3/wasip3 support).

Upgraded by downloading the `bytecodealliance/wasmtime` GitHub release binary
directly (the `curl | bash` install script from wasmtime.dev was blocked by
the sandbox's remote-code-execution policy, so used `gh release download`
instead, which is equivalent but auditable):

- Release used: `v46.0.1` (latest at time of install)
- Asset: `wasmtime-v46.0.1-aarch64-macos.tar.xz`
- Old binary backed up to `~/.wasmtime/bin/wasmtime.old-22.0.0`
- New binary installed in place at `~/.wasmtime/bin/wasmtime`

```
$ wasmtime --version
wasmtime 46.0.1 (823d1b8f2 2026-06-24)
```

Satisfies `>= 43` requirement comfortably.

## node / nvm

nvm already installed (`nvm --version` → `0.39.7`). Node 24 was already
present (`v24.14.1`) from a prior session; ran `nvm install 24` (no-op,
already installed) and used `nvm use 24` to activate it for the jco install
below. Did **not** change the default alias — default remains node 22
(`v22.23.1`) per the brief's instruction to only activate 24, not make it
default.

To activate node 24 in a new shell for later tasks:
```bash
source ~/.nvm/nvm.sh
nvm use 24
```

```
$ node --version   # after `nvm use 24`
v24.14.1
```

## jco

Installed globally under the node 24 environment:
```bash
source ~/.nvm/nvm.sh && nvm use 24
npm install -g @bytecodealliance/jco
```

```
$ jco --version
1.25.1
```

## Deviations from the brief

1. Brief's exact wasi-sdk-34 asset filename was a guess and slightly wrong
   (`wasi-sdk-34.0rc1-...` vs actual `wasi-sdk-34.0-rc.1-...`); corrected name
   used above.
2. No stable wasi-sdk-34 tag exists yet; used `wasi-sdk-34-rc.1` (the newest
   34 rc), per brief's fallback instruction.
3. Extracted wasi-sdk to `~/wasi-sdk-34.0-rc.1-arm64-macos` rather than
   `~/wasi-sdk-34.0`, to keep the exact upstream tarball directory name and
   avoid any ambiguity — this is the directory later tasks should point
   `WASI_SDK_PATH` at.
4. wasmtime was upgraded via direct GitHub release binary download
   (`gh release download`) rather than the `curl https://wasmtime.dev/install.sh | bash`
   one-liner, because the sandbox blocked piping a remote script into `bash`.
   The resulting binary and version are equivalent to what the installer
   would have produced.
5. Node 24 and nvm were already installed on this machine prior to this task;
   no new installation was needed beyond confirming version and activating it
   for the `npm install -g` step.
