import std/os/process
import std/text/regex
import std/num/float64
import std/os/file
import std/os/path
import std/os/dir
import std/core/undiv
import run-benchmarks

struct result
  a: string
  name: string
  d: int
  mk: int
  precise: int
  num-eval: int
  num-apply: int
  avg-e: float64
  avg-a: float64
  avg-mk: float64
  avg-k: float64
  avg-s: float64
  time: maybe<float64>

// Automatically generated.
// Shows a string representation of the `result` type.
pub fun result/show(this : result) : e string
  match this
    Result(a, name, d, mk, precise, num-eval, num-apply, avg-e, avg-a, avg-mk, avg-k, avg-s, time) -> "Result(a: " ++ a.show ++ ", name: " ++ name.show ++ ", d: " ++ d.show ++ ", mk: " ++ mk.show ++ ", precise: " ++ precise.show ++ ", num-eval: " ++ num-eval.show ++ ", num-apply: " ++ num-apply.show ++ ", avg-e: " ++ avg-e.show ++ ", avg-a: " ++ avg-a.show ++ ", avg-mk: " ++ avg-mk.show ++ ", avg-k: " ++ avg-k.show ++ ", avg-s: " ++ avg-s.show ++ ", time: " ++ time.show ++ ")"


fun string/int(s: string): exn int
  s.parse-int.expect("not an int: " ++ s)

fun string/float64(s: string): exn float64
  s.parse-float64.expect("not a float64: " ++ s)

fun fetch-files(files: list<string> = files, analyses: list<analysis> = [DMCFA, DMCFA-EXP, KCFA])
  files.flatmap fn(f)
    analyses.flatmap fn(a)
      val sens = a.sensitivities
      val file = "benchmarks/results".path / f / (a.show ++ "-" ++ sens.fst.show ++ "-" ++ sens.snd.show ++ ".csv")
      if !file.is-file then return []
      read-text-file(file).split("\n").map-indexed fn(i, line)
        if i == 0 then Nothing
        else
          match line.trim.split(",")
            [an, name, d, mk, pre, ne, na, avge, avga, avgmk, avgk, avgs, time] ->  
              Just(Result(an, name, 
                  d.int, mk.int, pre.int, ne.int, na.int, 
                  avge.float64, avga.float64, avgmk.float64, avgk.float64, avgs.float64, time.parse-float64))
            [] -> Nothing
            [""] -> Nothing
            _ -> throw("bad line in " ++ file.show ++ ": " ++ line.trim.show)
    .flatmap-maybe(id)


fun sort( xs : list<a>, f: a -> b, ?cmp: (b, b) -> order ) : list<a>
  match(xs)
    Cons(x,xx) ->
      val (ys, zs) = xx.partition fn(el) cmp(f(el), f(x)).is-lt 
      sort(ys.pretend-decreasing, f) ++ [x] ++ sort(zs.pretend-decreasing, f)
    Nil -> Nil

fun group-by(l : list<a>, f: a -> b, ?(==): (b, b) -> bool, ?sort: (list<a>, (a -> b)) -> list<a>) : list<(b, list<a>)>
  l.sort(f).foldl([]) fn(acc, x)
    match acc
      [] -> [(f(x), [x])]
      Cons((k, v), kvs) -> 
        if k == f(x) then Cons((k, Cons(x, v)), kvs)
        else Cons((f(x), [x]), Cons((k, v), kvs))

fun analyze(files: list<string>, metric: list<result> -> c): io list<(int, int, string, c)>
  val dm = fetch-files(files).group-by(fn(r) (r.d, r.mk, r.a), ?(==)= fn(a, b) a == b).sort(fn((k, _)) k)
  dm.map(fn(((d, m, a), v)) (d, m, a, v.metric))

fun float/average(l: list<float64>): maybe<float64>
  if l.is-empty then Nothing
  else Just(l.sum / l.length.float64)

fun int/average(l: list<int>): maybe<float64>
  if l.is-empty then Nothing
  else Just(l.sum.float64 / l.length.float64)

fun main()
  val koka = files.remove(_ == "benchmarks")
  val bench = files.filter(_ == "benchmarks")
  "\n\n\n\nBenchmark results\n\n\n\n".println
  bench.analyze(_.flatmap-maybe(time).average).map(tuple4/show).join("\n").println
  "\n\n\n\nBenchmark precision\n\n\n\n".println
  bench.analyze(_.map(precise).sum).map(tuple4/show).join("\n").println


  "\n\n\n\nKoka result\n\n\n\n".println
  koka.analyze(_.map(fn(a) a.time.default(100.0)).average).map(tuple4/show).join("\n").println
  "\n\n\n\nKoka precision\n\n\n\n".println
  koka.analyze(_.map(precise).sum).map(tuple4/show).join("\n").println
  "\n\n\n\nKoka precision\n\n\n\n".println
  koka.analyze(_.map(precise).average).map(tuple4/show).join("\n").println
