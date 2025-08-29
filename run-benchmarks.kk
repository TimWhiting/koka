import std/os/process
import std/text/regex
import std/num/float64

val files = ["benchmarks", "handlers/yield", "handlers/vec"] // , "handlers/unix"]

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
    DMCFA -> (2, 6)
    DMCFA-EXP -> (2, 6)
    KCFA -> (0, 6)

fun show(a: analysis)
  match a
    DMCFA -> "dmcfa"
    DMCFA-EXP -> "dmcfae"
    KCFA -> "kcfa"

fun run-benchmarks(files: list<string> = files, analyses: list<analysis> = [DMCFA, DMCFA-EXP, KCFA])
  analyses.map fn(a)
    files.map fn(f)
      (a, f, run-file(a, "stack run koka -- -l " ++ a.flag ++ " analysis/benchmarks/" ++ f ++ ".kk ", a.sensitivities))
  .concat

fun filter-matches( xs : list<list<sslice>> ) : list<list<sslice>>
  match xs
    Cons(_,Cons(m,mm)) -> Cons(m,filter-matches(mm))
    _                  -> Nil

fun int(s: sslice): exn int
  s.string.parse-int.unjust

fun run-file(a: analysis, cmd: string, (df, mf): (int, int))
  val full-cmd = cmd ++ "--sweep --ma=" ++ mf.show ++ " --da=" ++ df.show ++ " 2>&1"
  println("Running command: " ++ full-cmd)
  match run-system-read(full-cmd)
    Ok(res) -> 
      match a
        KCFA -> 
          val results = r"k=(\d)\nResult ([\d]+) / ([\d]+)\nResult [\d\.\%]+, time: ([\d\.]+)s".regex.exec-all(res).filter-matches
          results.map(fn([_, k, correct, all, time]) (0, k.int, correct.int, all.int, time.string.parse-float64.unjust))
        _ -> 
          val results = r"d=(\d),m=(\d)\nResult ([\d]+) / ([\d]+)\nResult [\d\.\%]+, time: ([\d\.]+)s".regex.exec-all(res).filter-matches
          results.map(fn([_, d, m, correct, all, time]) (d.int, m.int, correct.int, all.int, time.string.parse-float64.unjust))
    Error(err) -> throw-exn(err)

fun format-results(results: list<(analysis, string, list<(int, int, int, int, float64)>)>): console ()
  println("Analysis results (correct/total) [time in seconds]")
  results.foreach fn(res: (analysis, string, list<(int, int, int, int, float64)>))
    println(res.fst.show ++ " " ++ res.snd)
    val r : list<(int, int, int, int, float64)> = res.thd
    r.map(tuple5/show).join("\n").println

fun main()
  run-benchmarks().format-results
  // run-benchmarks(["handlers/unix"]).format-results 
  // run-benchmarks(["handlers/unix"], [DMCFA, DMCFA-EXP]).format-results