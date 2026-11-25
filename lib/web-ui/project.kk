/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Build support for `web-ui` projects: compile the app and stage a servable
// directory. A project's whole build script is:
//
//   // build.kk
//   import web-ui/project
//   fun main() build-web-app()
//
// Run with `koka -e build.kk` from the project directory. By default this
// builds `--target=wasi-web` into `out/` (requires WASI_SDK_PATH); pass a
// target to choose: `koka -e build.kk -- jsweb` stages the javascript
// backend into `out-js/`, and `-- all` builds both. The same `index.html`
// serves both targets (the staged `web-ui-host.js` differs per target).
// Set KOKA to override the compiler command.
module web-ui/project

import std/os/env
import std/os/path
import std/os/dir
import std/os/file
import std/os/process

pub fun build-web-app( main : string = "main.kk", out : string = "out" ) : io ()
  val targets = match get-args()
                  Nil  -> ["wasi-web"]
                  args | args.any(fn(a) a == "all") -> ["wasi-web","jsweb"]
                  args -> args
  targets.foreach fn(t)
    match t
      "wasi-web" -> build-wasi-web(main, out)
      "jsweb"    -> build-jsweb(main, out ++ "-js")
      "native"   -> build-native(main)
      _          -> throw("unknown target: " ++ t ++ " (expected wasi-web, jsweb, native, or all)")

fun koka-cmd() : ndet string
  get-env-value("KOKA").default("koka")

fun build-wasi-web( main : string, out : string ) : io ()
  match get-env-value("WASI_SDK_PATH")
    Nothing -> throw("WASI_SDK_PATH is not set (wasi-sdk >= 34 is required for --target=wasi-web)")
    Just(_) -> ()
  val cmd = koka-cmd() ++ " --target=wasi-web --console=raw " ++ main
  println("compile: " ++ cmd)
  match run-system-read(cmd)
    Error(err) -> throw("compile failed: " ++ err.show)
    Ok(output) ->
      val wasm = output.created-artifact(".wasm")
      val build-dir = wasm.nobase
      val outdir = out.path
      ensure-dir(outdir)
      copy-file(wasm, outdir / "app.wasm".path)
      copy-file(build-dir / "timers.js".path, outdir / "timers.js".path)
      copy-file(build-dir / "web-ui-host.js".path, outdir / "web-ui-host.js".path)
      // threads shim (a --wasithreads build loads these on demand; harmless otherwise)
      if is-file(build-dir / "wasi-threads.js".path) then
        copy-file(build-dir / "wasi-threads.js".path, outdir / "wasi-threads.js".path)
        copy-file(build-dir / "wasi-worker.js".path, outdir / "wasi-worker.js".path)
        copy-file(build-dir / "serve.py".path, outdir / "serve.py".path)
      copy-directory(build-dir / "vendor".path, outdir / "vendor".path)
      copy-file("index.html".path, outdir / "index.html".path)
      stage-assets(outdir)
      serve-hint(out)

fun build-jsweb( main : string, out : string ) : io ()
  val cmd = koka-cmd() ++ " --target=jsweb --console=raw " ++ main
  println("compile: " ++ cmd)
  match run-system-read(cmd)
    Error(err) -> throw("compile failed: " ++ err.show)
    Ok(output) ->
      val page = output.created-artifact(".html")
      val build-dir = page.nobase
      val outdir = out.path
      ensure-dir(outdir)
      // the whole ES-module graph, with the main module also staged as app.wasm's
      // counterpart `app.mjs` (the shared index.html boots via web-ui-host.js)
      val mjss = list-directory(build-dir).filter(fn(p) p.string.ends-with(".mjs").bool)
      mjss.foreach(fn(p) copy-file-to-dir(p, outdir))
      // the generated entry module: `<mod>_at_main.mjs` (`<mod>__main.mjs` before Koka 3.3)
      match mjss.filter(fn(p) p.string.ends-with("_at_main.mjs").bool || p.string.ends-with("__main.mjs").bool)
        Cons(mainmod, _) -> copy-file(mainmod, outdir / "app.mjs".path)
        Nil -> throw("could not find the linked main module (*_at_main.mjs) in " ++ build-dir.string)
      write-text-file(outdir / "web-ui-host.js".path, jsweb-host-shim)
      copy-file("index.html".path, outdir / "index.html".path)
      stage-assets(outdir)
      serve-hint(out)

// Stage the project's `assets/` directory next to the served page, if it has
// one. `image(FromPath("assets/pic.png"))` lowers to an `<img src>` resolved
// against the SERVED root, so without this the asset 404s on web while the
// identical path works natively (it reads from the project directory) -- a
// split that is invisible until someone opens the page. Native needs no
// equivalent: `app-native` is built in place and reads `assets/` directly.
fun stage-assets( outdir : path ) : io ()
  if is-directory("assets".path) then
    copy-directory("assets".path, outdir / "assets".path)

// Native (macOS, Impeller): builds the window host dylib once, then links
// the app against the Impeller SDK (fetch it with lib/ui/api/impeller/get-sdk.sh).
fun build-native( main : string ) : io ()
  val impdir = find-impeller-dir()
  val sdk = impdir ++ "/sdk"
  if !is-directory((sdk ++ "/include").path)
    then throw("Impeller SDK not found: run " ++ impdir ++ "/get-sdk.sh first")
  val host = impdir ++ "/libimpellerhost.dylib"
  run("clang -x objective-c -fobjc-arc -dynamiclib " ++ impdir ++ "/host.m -o " ++ host
      ++ " -I" ++ sdk ++ "/include -I/opt/homebrew/include"
      ++ " -L" ++ sdk ++ "/lib -L/opt/homebrew/lib -limpeller -lglfw"
      ++ " -framework Cocoa -framework Metal -framework QuartzCore"
      ++ " -install_name @rpath/libimpellerhost.dylib")
  run(koka-cmd() ++ " --console=raw -O2 " ++ main
      // -I<impdir>: shim.c (inlined into the generated C) includes the vendored
      // stb_image.h by name, so the impeller dir must be on the header path
      ++ " \"--ccopts=-I" ++ sdk ++ "/include -I" ++ impdir ++ "\""
      ++ " \"--cclib=impeller;impellerhost\""
      ++ " \"--cclinkopts=-L" ++ sdk ++ "/lib -L" ++ impdir
      ++ " -Wl,-rpath," ++ sdk ++ "/lib -Wl,-rpath," ++ impdir ++ "\""
      ++ " -o app-native")
  println("built  : ./app-native  (KOKA_IMP_FRAMES=n auto-closes after n frames)")

fun run( cmd : string ) : io ()
  println("run    : " ++ cmd)
  val code = run-system(cmd)
  if code != 0 then throw("command failed (exit " ++ code.show ++ ")")

// lib/ui/api/impeller, found by walking up from the project directory
// (KOKA_IMPELLER_DIR overrides)
fun find-impeller-dir() : io string
  match get-env-value("KOKA_IMPELLER_DIR")
    Just(d) -> d
    Nothing -> search-impeller(cwd(), 6)

fun search-impeller( d : path, depth : int ) : io string
  val cand = d / "lib/ui/api/impeller".path
  if is-directory(cand) then cand.string
  elif depth <= 0 then throw("cannot locate lib/ui/api/impeller (set KOKA_IMPELLER_DIR)")
  else search-impeller(d.nobase, depth - 1)

// On jsweb the compiled Koka module runs directly in the page: `runKoka`
// just imports it. The debug API is a stub (no externref table to inspect).
val jsweb-host-shim : string =
  [ "// web-ui host shim for --target=jsweb (see lib/web-ui/project.kk):"
  , "// the compiled Koka module runs directly in the page."
  , "export async function runKoka(_wasmUrl, _opts = {}) {"
  , "  const kokaDebug = { stub: true, live: () => 0, allocated: () => 0, freed: () => 0,"
  , "    gcCount: () => 0, slots: () => [], detached: () => [], dump: () => 0 };"
  , "  window.kokaDebug = kokaDebug;"
  , "  await import(\"./app.mjs\");"
  , "  return { instance: null, kokaDebug };"
  , "}"
  ].join("\n")

fun serve-hint( out : string ) : io ()
  println("staged : " ++ out ++ "/")
  println("serve  : (cd " ++ out ++ " && python3 -m http.server 8080) — then open http://localhost:8080/")

// the artifact path from the compiler's `created : <path>` output line
fun created-artifact( output : string, suffix : string ) : exn path
  val lines = output.lines.filter(fn(l) l.contains("created") && l.contains(suffix))
  match lines
    Cons(l, _) -> l.split(":").drop(1).join(":").trim.path
    Nil -> throw("could not find the created " ++ suffix ++ " artifact in the compiler output:\n" ++ output)
