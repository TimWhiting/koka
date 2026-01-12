import std/os/process
import std/text/regex
import std/num/float64
import std/os/file
import std/os/path
import std/os/dir

val suite-files = ["basic", "nondet", "nested", "multi-effect", "recursion", "state-handler", "complex-flow", "nested-nondet"]
val handler-files = ["yield", "vec", "unix", "nim", "ambient", "scoped"]
val rosetta-files = ["0-nums/pr4rings", "j/jump-anywhere", "m/monads-writer"] // "n/nim"
val files = suite-files.map(fn(f) "suite/" ++ f) ++ handler-files.map(fn(f) "handlers/" ++ f) ++
            rosetta-files.map(fn(f) "rosetta/rosetta/" ++ f)

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
    DMCFA -> (4, 4)
    DMCFA-EXP -> (4, 4)
    KCFA -> (0, 6)

fun show(a: analysis)
  match a
    DMCFA -> "dmcfa"
    DMCFA-EXP -> "dmcfae"
    KCFA -> "kcfa"

fun run-benchmarks(files: list<string> = files, analyses: list<analysis> = [DMCFA, DMCFA-EXP, KCFA])
  analyses.foreach fn(a)
    files.foreach fn(f)
      val sens = a.sensitivities
      val file = "benchmarks/results".path / f / (a.show ++ "-" ++ sens.fst.show ++ "-" ++ sens.snd.show ++ ".csv")
      if file.is-file then return ()
      var result := ""
      with handler
        fun write(s)
          result := result ++ s ++ "\n"
        return(x)
          write-text-file(file, result, create-dir=True)
      run-file(a, "stack run koka -- -l " ++ a.flag ++ " analysis/benchmarks/" ++ f ++ ".kk ", sens)


fun filter-matches( xs : list<list<sslice>> ) : list<list<sslice>>
  match xs
    Cons(_,Cons(m,mm)) -> Cons(m,filter-matches(mm))
    _                  -> Nil

fun int(s: sslice): exn int
  s.string.parse-int.unjust

fun run-file(a: analysis, cmd: string, (df, mf): (int, int))
  val full-cmd = cmd ++ "--sweep --ma=" ++ mf.show ++ " --da=" ++ df.show ++ " 2>&1"
  println("Debug command:\n" ++ cmd ++ "--ma=" ++ mf.show ++ " --da=" ++ df.show ++ " 2>out.kk")
  write("Analysis,File/Example,D,M(K),Precise,NEval,NApply,AvgEval,AvgApply,AvgK,AvgS,Time1,Time2,Time3")
  match run-system-read(full-cmd)
    Ok(res) -> 
      write(res.split("\n").filter(_.contains(a.show ++ ",")).filter(fn(l) l.split(",").length >= 5).map(a.show ++ _.split(a.show).tail.join(a.show)).join("\n"))
    Error(err) -> throw-exn(err)

fun main()
  run-benchmarks()
  // run-benchmarks(["handlers/nim"], [DMCFA])
  // run-benchmarks(["handlers/unix"], [DMCFA, DMCFA-EXP])