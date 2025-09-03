import std/os/process
import std/text/regex
import std/num/float64
import std/os/file
import std/os/path
import std/os/dir

val files = ["benchmarks", "handlers/yield", "handlers/vec", "handlers/unix", "handlers/nim", "handlers/ambient"]

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
    DMCFA -> (4, 6)
    DMCFA-EXP -> (4, 6)
    KCFA -> (0, 10)

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
  println("Running command: " ++ full-cmd)
  write("Analysis, File/Example, D, M(K), Precise, Time")
  match run-system-read(full-cmd)
    Ok(res) -> write(a.show ++ "," ++ res.split(a.show ++ ",").tail.join(a.show ++ ","))
    Error(err) -> throw-exn(err)

fun format-results(results: list<(analysis, string, list<(int, int, int, int, float64)>)>): out ()
  // println("Analysis results (correct/total) [time in seconds]")
  
  results.foreach fn(res: (analysis, string, list<(int, int, int, int, float64)>))
    val r : list<(int, int, int, int, float64)> = res.thd
    r.foreach fn((i, j, c, t, time))
      write([res.fst.show, res.snd, i.show, j.show, c.show, t.show, time.show].join(","))

fun main()
  run-benchmarks()
  // run-benchmarks(["handlers/nim"], [DMCFA])
  // run-benchmarks(["handlers/unix"], [DMCFA, DMCFA-EXP])