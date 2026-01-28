import std/os/process
import std/text/regex
import std/num/float64
import std/os/file
import std/os/path
import std/os/env
import std/os/dir

val suite-files = ["basic", "nondet", "nested", "multi-effect", "recursion", "state-handler", "complex-flow", "nested-nondet"]
val handler-files = ["yield", "vec", "unix", "nim", "ambient", "scoped"]
val rosetta-files = ["0-nums/pr4rings", "j/jump-anywhere", "m/monads-writer"] // "n/nim"
val kokagen-files = ["build", "interp", "interp2", "mini-ppl", "music", "scheduler", "ukanren", "coop-communication"] // release, coop-communication 
val float-files = ["handlers/nim", "koka-gen/mini-ppl", "rosetta/rosetta/0-nums/pr100prisoners", "rosetta/rosetta/0-nums/pr2048", "rosetta/rosetta/0-nums/pr24game", "rosetta/rosetta/g/gamma", "rosetta/rosetta/m/monads-writer"]
val files = suite-files.map(fn(f) "suite/" ++ f) ++ handler-files.map(fn(f) "handlers/" ++ f) ++
            rosetta-files.map(fn(f) "rosetta/rosetta/" ++ f) ++ kokagen-files.map(fn(f) "koka-gen/" ++ f)

val header = "Analysis,File/Example,D,M(K),Precise,NEval,SumEval,PrecEval,NApply,SumApply,PrecApply,NK,SumK,PrecK,NS,SumS,PrecS,Time1,Time2,Time3"

effect out
  fun write(s: string): ()

type analysis
  DMCFA
  DMCFA-EXP
  KCFA

fun flag(a: analysis)
  match a
    DMCFA -> "--dmcfa"
    DMCFA-EXP -> "--analyze"
    KCFA -> "--kcfa" 

fun sensitivities(a: analysis)
  match a
    DMCFA -> list(0,3).flatmap( fn(d) list(0,3).map( fn(m) (d,m)))  ++ [(20, 2), (2, 20), (100, 100)] 
    DMCFA-EXP -> list(0,3).flatmap( fn(d) list(0,3).map( fn(m) (d,m))) ++ [(20, 2), (2, 20), (100, 100)]
    KCFA -> list(0,3).map( fn(k) (0,k) )

fun show(a: analysis)
  match a
    DMCFA -> "dmcfa"
    DMCFA-EXP -> "dmcfae"
    KCFA -> "kcfa"

fun run-benchmarks(files: list<string> = files, analyses: list<analysis> = [DMCFA, DMCFA-EXP, KCFA], force: bool = False)
  analyses.foreach fn(a)
    files.foreach fn(f)
      run-file(a, f, a.sensitivities, force)


fun filter-matches( xs : list<list<sslice>> ) : list<list<sslice>>
  match xs
    Cons(_,Cons(m,mm)) -> Cons(m,filter-matches(mm))
    _                  -> Nil

fun int(s: sslice): exn int
  s.string.parse-int.unjust

fun run-file(a: analysis, f: string, sens: list<(int, int)>, force: bool)
  val sens-to-run = sens.filter fn((d,m))
    if force then True else !("benchmarks/results".path / a.show / d.show / m.show / f.path).is-directory()
      
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
  val force = args.find(fn(a) a == "--force").is-just
  val only-floats = args.find(fn(a) a == "--floats").is-just
  val run-files = if only-floats then float-files else files
  run-benchmarks(files=run-files, analyses=[DMCFA, DMCFA-EXP], force=force)
  // run-benchmarks(["handlers/nim"], [DMCFA])
  // run-benchmarks(["handlers/unix"], [DMCFA], force=force)