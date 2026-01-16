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
    if force then True else
      val file = "benchmarks/results".path / d.show / m.show / (f ++ ".csv")
      if file.is-file then
        val content = read-text-file(file)
        !content.contains(a.show ++ ",")
      else True

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
          val key = d ++ "/" ++ m ++ "/" ++ f ++ ".csv"
          match contents.find(fn(kv) kv.fst == key)
            Just((_,curr)) -> contents := contents.map(fn(kv) if kv.fst == key then (key, curr ++ "\n" ++ line) else kv)
            Nothing        -> contents := Cons((key,line), contents)
      
      contents.foreach fn((key, content))
          val file = "benchmarks/results".path / key
          val header = "Analysis,File/Example,D,M(K),Precise,NEval,NApply,AvgEval,AvgApply,AvgK,AvgS,Time1,Time2,Time3"
          if file.is-file then
             val current = read-text-file(file)
             val clean-current = 
               if force then 
                 current.split("\n").filter(fn(l) !l.starts-with(a.show ++ ",").bool).join("\n")
               else current
             val sep = if clean-current.is-empty then "" else "\n"
             write-text-file(file, clean-current ++ sep ++ content ++ "\n", create-dir=True)
          else 
             write-text-file(file, header ++ "\n" ++ content ++ "\n", create-dir=True)

    Error(err) -> throw-exn(err)

fun main()
  val args = get-args()
  val force = args.find(fn(a) a == "--force").is-just
  run-benchmarks(analyses=[DMCFA, DMCFA-EXP], force=force)
  // run-benchmarks(["handlers/nim"], [DMCFA])
  // run-benchmarks(["handlers/unix"], [DMCFA, DMCFA-EXP])