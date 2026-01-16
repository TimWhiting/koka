import std/os/process
import std/text/regex
import std/num/float64
import std/os/file
import std/os/path
import std/os/dir

val suite-files = ["basic", "nondet", "nested", "multi-effect", "recursion", "state-handler", "complex-flow", "nested-nondet"]
val handler-files = ["yield", "vec", "unix", "nim", "ambient", "scoped"]
val rosetta-files = ["0-nums/pr4rings", "j/jump-anywhere", "m/monads-writer"] // "n/nim"
val kokagen-files = ["build"] // "n/nim"
val files = suite-files.map(fn(f) "suite/" ++ f) ++ handler-files.map(fn(f) "handlers/" ++ f) ++
            rosetta-files.map(fn(f) "rosetta/rosetta/" ++ f) ++ kokagen-files.map(fn(f) "koka-gen/" ++ f)

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

fun run-benchmarks(files: list<string> = files, analyses: list<analysis> = [DMCFA, DMCFA-EXP, KCFA])
  analyses.foreach fn(a)
    files.foreach fn(f)
      run-file(a, f, a.sensitivities)


fun filter-matches( xs : list<list<sslice>> ) : list<list<sslice>>
  match xs
    Cons(_,Cons(m,mm)) -> Cons(m,filter-matches(mm))
    _                  -> Nil

fun int(s: sslice): exn int
  s.string.parse-int.unjust

fun run-file(a: analysis, f: string, sens: list<(int, int)>)
  val sens-to-run = sens.filter fn((d,m))
    val file = "benchmarks/results".path / f / (a.show ++ "-" ++ d.show ++ "-" ++ m.show ++ ".csv")
    !file.is-file

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

  match run-system-read(full-cmd)
    Ok(res) -> 
      val lines = res.split("\n").filter(fn(l) l.contains(a.show ++ ",") && l.split(",").length >= 5).map(fn(l) a.show ++ l.split(a.show).tail.join(a.show))
      
      var contents : list<(string,string)> := []
      lines.foreach fn(line)
        val parts = line.split(",")
        // Analysis,File,D,M,...
        if parts.length >= 4 then
          val d = parts.drop(2).head("").trim
          val m = parts.drop(3).head("").trim
          val key = a.show ++ "-" ++ d ++ "-" ++ m ++ ".csv"
          match contents.find(fn(kv) kv.fst == key)
            Just((_,curr)) -> contents := contents.map(fn(kv) if kv.fst == key then (key, curr ++ "\n" ++ line) else kv)
            Nothing        -> contents := Cons((key,line), contents)
      
      contents.foreach fn((key, content))
          val file = "benchmarks/results".path / f / key
          val header = "Analysis,File/Example,D,M(K),Precise,NEval,NApply,AvgEval,AvgApply,AvgK,AvgS,Time1,Time2,Time3"
          write-text-file(file, header ++ "\n" ++ content ++ "\n", create-dir=True)

    Error(err) -> throw-exn(err)

fun main()
  run-benchmarks(analyses=[DMCFA, DMCFA-EXP])
  // run-benchmarks(["handlers/nim"], [DMCFA])
  // run-benchmarks(["handlers/unix"], [DMCFA, DMCFA-EXP])