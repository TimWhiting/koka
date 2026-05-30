import std/os/process
import std/text/regex
import std/num/float64
import std/os/file
import std/os/path
import std/os/env
import std/os/dir

val suite-files = ["basic", "nondet", "nested", "multi-effect", "recursion", "state-handler", "complex-flow", "nested-nondet"]
val handler-files = ["yield", "vec", "unix", "nim", "ambient", "scoped"]
val rosetta-files = ["nums0/pr4rings", "j/jump-anywhere", "m/monads-writer"] // "n/nim"
val kokagen-files = ["build", "interp", "interp2", "mini-ppl", "music", "scheduler", "ukanren", "coop-communication"] // release, coop-communication 
val float-files = ["handlers/nim", "koka-gen/mini-ppl", "rosetta/rosetta/0-nums/pr100prisoners", "rosetta/rosetta/0-nums/pr2048", "rosetta/rosetta/0-nums/pr24game", "rosetta/rosetta/g/gamma", "rosetta/rosetta/m/monads-writer"]
val files = suite-files.map(fn(f) "suite/" ++ f) ++ handler-files.map(fn(f) "handlers/" ++ f) ++
            rosetta-files.map(fn(f) "rosetta/rosetta/" ++ f) ++ kokagen-files.map(fn(f) "koka-gen/" ++ f)

val header = "Analysis,File/Example,D,M(K),Precise,NEval,SumEval,PrecEval,NApply,SumApply,PrecApply,NK,SumK,PrecK,NS,SumS,PrecS,Time1,Time2,Time3"

type analysis
  DMCFAR
  DMCFAE
  KCFA

fun sensitivities(a: analysis)
  match a
    DMCFAR -> list(0,2).flatmap( fn(d) list(0,2).map( fn(m) (d,m))).remove(fn(e) e == (0,0)) // ++
                // [(100,2000)] // ++ [(20, 2), (2, 20), (100, 100)] 
    DMCFAE -> list(0,0).flatmap( fn(d) list(0, 0).map( fn(m) (d,m))) // ++ 
                //  [(100,2000)]// ++ [(20, 2), (2, 20), (100, 100)]
    KCFA -> list(0,2).map( fn(k) (0,k) ).remove(fn(e) e == (0,0))// ++ 
              // [(0,10000)]

fun show(a: analysis)
  match a
    DMCFAR -> "dmcfar"
    DMCFAE -> "dmcfae"
    KCFA -> "kcfa"
fun flag(a: analysis) "--" ++ a.show

fun run-benchmarks(files: list<string> = files, analyses: list<analysis> = [DMCFAR, DMCFAE, KCFA], force: bool = False, precise=False)
  analyses.foreach fn(a)
    files.foreach fn(f)
      run-file(a, f, if precise then [(100, 2000)] else a.sensitivities, force)

fun filter-matches( xs : list<list<sslice>> ) : list<list<sslice>>
  match xs
    Cons(_,Cons(m,mm)) -> Cons(m,filter-matches(mm))
    _                  -> Nil

fun int(s: sslice): exn int
  s.string.parse-int.unjust

fun run-file(a: analysis, f: string, sens: list<(int, int)>, force: bool)
  val sens-to-run = sens.filter fn((d,m))
    if force then True else 
      val folder = cwd() / "benchmarks/results".path / a.show / d.show / m.show / "analysis" / "benchmarks" / f.path
      println("Checking folder: " ++ folder.show ++ " exists: " ++ folder.is-directory().show)
      !folder.is-directory()
      
  if sens-to-run.is-empty then
    println("Skipping " ++ f ++ " " ++ a.show ++ " (all results exist)")
    return ()

  val cmd = "stack run koka -- -l analysis/benchmarks/" ++ f ++ ".kk " ++ a.flag ++ " "
  val sens-flags = sens-to-run.map(fn((d,m)) "--sensitivity=\"(" ++ d.show ++ "," ++ m.show ++ ")\"").join(" ")
  val full-cmd = cmd ++ sens-flags ++ " 2>&1"
  
  match sens-to-run.last
    Just((d,m)) ->
      val debug-cmd = cmd ++ "--sensitivity=\"(" ++ d.show ++ "," ++ m.show ++ ")\" 2>&1" 
      println("Debug command:\n" ++ debug-cmd)
    Nothing -> ()
  run-system-read(full-cmd)
  ()

fun main()
  val args = get-args()    
  val force = args.find(_ == "--force").is-just
  val only-floats = args.find(_ == "--floats").is-just
  val run-files = if only-floats then float-files else files
  run-benchmarks(files=run-files, analyses=[DMCFAR, DMCFAE, KCFA], force=force)
  // run-benchmarks(files=run-files, analyses=[DMCFAR, DMCFAE, KCFA], force=force, precise=True)
  // run-benchmarks(["handlers/nim"], [DMCFAR])
  // run-benchmarks(["handlers/unix"], [DMCFAR], force=force)