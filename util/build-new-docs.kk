/*-----------------------------------------------------------------------------
Build Koka documentation for the new site structure.
This script:
1. Pre-processes .mdk files through Koka as .kk.md to get rich tooltips.
2. Runs Madoko on the resulting files to generate the final HTML.
-----------------------------------------------------------------------------*/
import std/os/path
import std/os/dir
import std/os/file
import std/os/process
import std/text/regex

fun main()
  val root = "docs2".path
  val out = "out".path
  val gen = out / "gen"
  
  println("Creating output directories...")
  [out, gen,
    out / "concepts", out / "styles", out / "images", out / "scripts",
   out / "guides", out / "topics", out / "tutorial", out / "reference", out / "blog", out / "learn",
    gen / "concepts", gen / "styles", gen / "images", gen / "scripts",
   gen / "guides", gen / "topics", gen / "tutorial", gen / "reference", gen / "blog", gen / "learn"
  ].map(fn(d) if !d.is-directory then ensure-dir(d))

  println("Copying assets...")
  copy-dir(root / "lang", out / "lang")
  copy-dir(root / "styles", out / "styles")
  copy-dir(root / "images", out / "images")
  copy-dir(root / "scripts", out / "scripts")
  copy-dir(root / "lang", gen / "lang")
  copy-dir(root / "styles", gen / "styles")
  copy-dir(root / "images", gen / "images")
  copy-dir(root / "scripts", gen / "scripts")

  println("Staging all source files to generation folder...")
  copy-recursive(root, gen)

  // Copy static files that don't go through Madoko
  copy-file(root / "404.html", out / "404.html")
  copy-file(root / "koka.bib", out / "koka.bib")
  copy-file(root / "koka.bib", gen / "koka.bib")

  val root-files = ["index", "install"]
  val sub-files = [("learn", ["index", "basics", "types", "effects", "fbip"]),
                   ("concepts", ["index", "general", "effects-and-handlers", "perceus-and-fbip"]),
                   ("guides", ["index", "functions", "types", "adts", "overloading", "pattern-matching", "effect-types", "effect-handlers", "implicits", "advanced-handlers", "fbip", "performance-fbip"]),
                   ("reference", ["index", "spec", "repl-and-tooling", "effect-semantics", "type-and-representation", "handlers-advanced"]),
                   ("tutorial", ["index", "getting-started", "functions", "lists", "types", "effects", "custom-effects", "calculator", "calculator-interactive"]),
                   ("blog", ["index", "koka-3-2", "koka-3-1", "koka-3-0", "koka-2-6"])]

  // Process root files
  root-files.map fn(name)
    process-file(root, out, gen, "", name)

  // Process subdirectories
  sub-files.map fn(dir-pair)
    val (subdir, subnames) = dir-pair
    subnames.map fn(name)
      process-file(root, out, gen, subdir, name)
  println("Done.")

fun mangle( name : string ) : string
  name.replace-all(regex("-"),"_dash_")

fun copy-recursive(src : path, dst : path) : io ()
  if src.is-directory then
    ensure-dir(dst)
    val entries = list-directory(src)
    entries.foreach fn(p)
      val p-str = p.basename
      if p-str != "styles" && p-str != "images" && p-str != ".koka" && p-str != "out" then
        val src-f = src / p-str
        val dst-f = dst / p-str
        if src-f.is-file then
          copy-file(src-f, dst-f)
        elif src-f.is-directory then
          copy-recursive(src-f, dst-f)

fun copy-dir(src : path, dst : path) : io ()
  if src.is-directory then
    ensure-dir(dst)
    val entries = list-directory(src)
    entries.foreach fn(p)
      val src-f = src / p.basename
      val dst-f = dst / p.basename
      if src-f.is-file then
        println("Copying file: " ++ src-f.string ++ " -> " ++ dst-f.string)
        copy-file(src-f, dst-f)
      elif src-f.is-directory then
        copy-dir(src-f, dst-f)

fun process-file(root : path, out : path, gen : path, subdir : string, name : string) : io ()
  val subpath = if subdir == "" then "".path else subdir.path
  val src-file = root / subpath / (name ++ ".mdk")
  val koka-src-file = root / subpath / (name ++ ".kk")
  val tmp-file = gen / subpath / (name ++ ".kk.md")
  val target-dir = out / subpath
  val target-html = out / subpath / (name ++ ".html")
  
  if !src-file.is-file then
    if name != "common" then
      println("Skipping missing file: " ++ src-file.string)
    return ()

  if ! (gen / subpath).is-directory then
    ensure-dir(gen / subpath)

  val deps = [src-file,
              root / "koka.bib",
              root / "lang" / "koka.json",
              root / "lang" / "unchecked.json",
              root / "styles" / "modern.css",
              root / "scripts" / "docs.js",
              root / "sidebar.mdk",
              root / "sidebar-sub.mdk"] ++
             (if koka-src-file.is-file then [koka-src-file] else [])

  if target-up-to-date(target-html, deps) then
    println("Skipping unchanged: " ++ target-html.string)
    return ()
  
  println("Processing: " ++ name ++ (if subdir != "" then " in " ++ subdir else ""))
  
  // 1a. Copy .mdk to .kk.md in gen folder
  copy-file(src-file, tmp-file)
  if koka-src-file.is-file then
    copy-file(koka-src-file, gen / subpath / (name ++ ".kk"))
    copy-file(koka-src-file, out / subpath / (name ++ ".kk"))

  // 1b. Copy koka.json and styles if they exist near the source
  val koka-json = root / "lang" / "koka.json"
  val unchecked-json = root / "lang" / "unchecked.json"
  if koka-json.is-file then
    copy-file(koka-json, gen / subpath / "koka.json")
    copy-file(unchecked-json, gen / subpath / "unchecked.json")

  // 2. Run Koka to generate rich markdown
  val koka-cmd = "cd " ++ (gen / subpath).string ++ " && stack run koka -- -c -v0 -l --html --outputdir=. " ++ (name ++ ".kk.md")
  run-system(koka-cmd)

  // 3. Find the generated .md file (Koka mangles hyphens to _dash_)
  val mangled-name = mangle(name)
  val generated-md = gen / subpath / (mangled-name ++ ".md")
  val final-md = gen / subpath / (name ++ ".md")
  
  if mangled-name != name && generated-md.is-file then
    // Rename mangled files back to original names so Madoko produces the right HTML names
    move-file(generated-md, final-md)
    val generated-dimx = gen / subpath / (mangled-name ++ ".dimx")
    if generated-dimx.is-file then
      move-file(generated-dimx, gen / subpath / (name ++ ".dimx"))
    val generated-dimx-html = gen / subpath / (mangled-name ++ ".dimx.html")
    if generated-dimx-html.is-file then
      move-file(generated-dimx-html, gen / subpath / (name ++ ".dimx.html"))

  // 4. Run Madoko on the generated markdown
  // Add lang directory to search path for language definitions using -mPath
  val abs-root = root.realpath
  val abs-gen = gen.realpath
  val abs-out = out.realpath
  val abs-target-dir = target-dir.realpath
  
  val options = " --odir=" ++ abs-target-dir.string ++ " -mPath:" ++ (abs-root / "lang").string
  if final-md.is-file then
    val madoko-cmd = "cd " ++ (abs-gen / subpath).string ++ " && madoko" ++ options ++ " " ++ name ++ ".md"
    run-echo(madoko-cmd)
  else
    println("  Warning: Koka failed to generate " ++ (name ++ ".md") ++ ". Falling back to original .mdk.")
    val fallback-cmd = "cd " ++ (abs-gen / subpath).string ++ " && madoko" ++ options ++ " " ++ src-file.realpath.string
    run-echo(fallback-cmd)

fun run-echo(cmd : string) : io ()
  val exit-code = run-system(cmd)
  if exit-code != 0 then
    println("Command failed with exit code " ++ exit-code.show ++ ": " ++ cmd)

fun target-up-to-date(target : path, deps : list<path>) : io bool
  if !target.is-file then False
  else deps-not-newer(target,deps)

fun deps-not-newer(target : path, deps : list<path>) : io bool
  match deps
    Nil -> True
    Cons(dep,rest) ->
      if dep.is-file && path-is-newer(dep,target) then False
      else deps-not-newer(target,rest)

fun path-is-newer(a : path, b : path) : io bool
  run-system("test " ++ a.string ++ " -nt " ++ b.string) == 0

fun move-file(src : path, dst : path) : io ()
  run-system("mv " ++ src.string ++ " " ++ dst.string)
  ()
