//---------------------------------------------------------------------------
// Copyright 2021, Daan Leijen.
//---------------------------------------------------------------------------

// ----------------------------------------------------
// Benchmark script
// ----------------------------------------------------

import std/num/float64
import std/os/file
import std/os/path
import std/os/env
import std/os/dir
import std/os/process
import std/os/flags

// ----------------------------------------------------
// Flags
// ----------------------------------------------------
val all-test-names = ["rbtree", "sfib", "tak"].flatmap fn(tv) [tv, tv ++ "_optimized"]
// val all-test-names = ["int", "mstate", "nqueens", "pyth", "hamming", "rbtree", "sfib", "tak"].flatmap fn(tv) [tv, tv ++ "_optimized"]
// val all-test-names = ["effects", "effects_1", "effects_2", "effects_2_poly"].flatmap fn(tv) [tv, tv ++ "_optimized"]
val all-test-variants = [
  TestVariants("int", "integers", [Variant("int", "full-int", True), Variant("int32", "precise-int")]),
  TestVariants("mstate", "integers", [Variant("mstate-int", "full-int", True), Variant("mstate", "precise-int")]),
  TestVariants("nqueens", "integers", [Variant("nqueens-int", "full-int", True), Variant("nqueens", "precise-int")]),
  TestVariants("nqueens8", "integers", [Variant("nqueens-int", "full-int", True), Variant("nqueens-int8", "precise-int8")]),
  TestVariants("pyth", "integers", [Variant("pyth-int", "full-int", True), Variant("pyth", "precise-int")]),
  TestVariants("tak", "integers", [Variant("tak-int", "full-int", True), Variant("tak", "precise-int")]),
  TestVariants("sfib", "integers", [Variant("sfib-int", "full-int", True), Variant("sfib", "precise-int")]),
  TestVariants("rbtree", "integers", [Variant("rbtree-int", "full-int", True), Variant("rbtree", "precise-int")]),
  TestVariants("hamming", "integers", [Variant("hamming-int", "full-int", True), Variant("hamming", "precise-int")]),
  TestVariants("effects", "linear_effs", 
    [Variant("nonlinear", "linear-in-practice", True), Variant("linear", "linear-keyword")]),
  TestVariants("effects_1", "linear_effs", 
    [Variant("nonlinear_1", "linear-in-practice", True), Variant("linear_1", "linear-keyword")]),
  TestVariants("effects_2", "linear_effs", 
    [Variant("nonlinear_2", "linear-in-practice", True), Variant("linear_2", "linear-keyword")]),
  TestVariants("effects_2_poly", "linear_effs", 
    [Variant("nonlinear_2_poly", "linear-in-practice", True), Variant("linear_2_poly", "linear-keyword")])
].flatmap fn(tv) 
  val newVars = tv.variants.map(fn(v) { v(file=v.file ++ "_optimized")})
  [tv, tv(variants=newVars, name=tv.name ++ "_optimized")]

struct testVariants
  name: string
  subdir: string
  variants: list<variant>

struct variant
  file: string
  kind: string
  isDefault: bool = False

struct iflags {
  tests : string = ""
  iter  : int  = 3
  chart : bool = False
  normalize : bool = False
  help  : bool = False
}

val flag-descs : list<flag<iflags>> = {
  fun set-tests( f : iflags, s : string ) : iflags { f(tests = s) }
  fun set-norm( f : iflags, b : bool ) : iflags { f(normalize = b) }
  fun set-chart( f : iflags, b : bool ) : iflags { f(chart = b) }
  fun set-help( f : iflags, b : bool ) : iflags { f(help = b) }
  fun set-iter( f : iflags, i : string ) : iflags { f(iter = i.parse-int().default(1)) }
  [ Flag( "t", ["test"], Req(set-tests,"test"),  "comma separated list of tests" ),
    Flag( "i", ["iter"], Req(set-iter,"N"),      "use N (=1) iterations per test"),
    Flag( "c", ["chart"], Bool(set-chart),       "generate latex chart"),
    Flag( "n", ["norm"], Bool(set-norm),         "normalize results relative to Koka"),
    Flag( "h", ["help"], Bool(set-help),         "show this information"),
  ]
}

fun flag-usage() {
  flag-descs.usage("usage:\n koka -e bench.kk [options]\n\noptions:").println
  println([
    "\nnotes:",
    "  tests    : " ++ all-test-names.join(", "),
  ].unlines)
}

pub fun process-flags() : <ndet,console> maybe<iflags> {
  val (flags,args,errs) = parse( Iflags(), flag-descs, get-args() )
  if (flags.help) then {
    flag-usage()
    Nothing
  }
  elif (errs.is-nil && args.is-nil) then {
    Just(flags)
  }
  else {
    println( errs.join("\n") )
    flag-usage()
    Nothing
  }
}


// ----------------------------------------------------
// Test structure
// ----------------------------------------------------

struct test {
  name: string
  variant: variant
  size: int = 0
  elapsed: float64 = 0.0
  elapsed-sdev : float64 = 0.0
  rss: int = 0
  err: string = ""
  norm-elapsed: float64 = 0.0
  norm-rss: float64 = 0.0
  norm-elapsed-sdev : float64 = 0.0
  norm-size : float64 = 0.0
}

fun rss-float64(t : test) : float64 {
  t.rss.float64
}

fun show( test : test ) {
  val xs = if (test.err.is-empty) then [
    "" ++ test.elapsed.core/show(5).pad-left(5) ++ "s ~" ++ test.elapsed-sdev.core/show-fixed(3),
    "" ++ test.rss.core/show ++ "kb," ++
    " size: " ++ (test.size / 1000).core/show ++ "kb"
  ] else ["error: " ++ test.err]
  ([test.name, test.variant.file] ++ xs).join(", ")
}

fun show-norm( test : test ) {
  val xs = if (test.err.is-empty) then [
      "" ++ test.norm-elapsed.core/show(5).pad-left(5) ++ "x ~" ++ test.elapsed-sdev.core/show-fixed(3),
      "" ++ test.norm-rss.core/show(2) ++ "x," ++
      " size: " ++ test.norm-size.core/show(5) ++ "x"
    ] else ["error: " ++ test.err]
  ([test.name, test.variant.file] ++ xs).join(", ")
}

// ----------------------------------------------------
// main
// ----------------------------------------------------
pub fun main()
  match (process-flags())
    Nothing -> ()
    Just(flags) ->
      val test-names = if (flags.tests.is-empty) then all-test-names
                        else flags.tests.split(",")
      run-tests(test-names,flags.chart,flags.iter,flags.normalize)


fun run-tests(test-names : list<string>, gen-chart : bool, iterations : int, normalize : bool ) {
  println("tests    : " ++ test-names.join(", "))

  // run tests
  val alltests = test-names.flatmap fn(test-name){
                   val test = all-test-variants.find(fn(x) x.name == test-name).unjust
                   test.variants.map fn(variant){
                     run-test( variant, test.subdir, test-name, iterations )
                   }
                 }

  // todo: average over multiple runs

  // show test results
  test-names.foreach fn(test-name){
    val tests = alltests.filter(fn(t){ t.name == test-name })
    println("\n--- " ++ test-name ++ " ----------------")
    println(tests.map(show).join("\n"))
  }

  // normalize tests
  val all-ntests = test-names.flatmap fn(test-name){
    val tests = alltests.filter(fn(t){ t.name == test-name })

    // normalize to default variant
    val def = match(tests.filter(fn(t){t.variant.isDefault})) { Cons(t,Nil) -> t }
    val ntests = tests.map fn(t) {
      val norm = if (def.elapsed==0.0) then 1.0 else t.elapsed / def.elapsed
      val s = t.size.float64 / def.size.float64
      t(norm-elapsed = norm,
        norm-rss     = if (def.rss==0) then 1.0 else t.rss.float64 / def.rss.float64,
        norm-elapsed-sdev = norm * t.elapsed-sdev,
        norm-size = s)
    }
    println("\n--- normalized " ++ test-name ++ " ----------------")
    println(ntests.map(show-norm).join("\n"))
    ntests
  }

  // group by test
  val kind-ntests = ["full-int", "precise-int"].map(fn(l) {
    (l, all-ntests.filter(fn(t:test){ t.variant.kind == l }))
  })

  // emit latex chart
  if (gen-chart) then {
    val ymax       = 3.0
    val chart-desc = r"16-core AMD 5950X at 3.4Ghz\\Ubuntu 20.04, gcc 9.3.0"
    val chart-elapsed = if (normalize)
                          then chart("time", True, norm-elapsed, norm-elapsed-sdev, elapsed, test-names, kind-ntests, ymax, chart-desc)
                          else chart("time", False, elapsed, elapsed-sdev, elapsed, test-names, kind-ntests, ymax, chart-desc)
    val chart-rss     = if (True || normalize)
                          then chart("rss", True, norm-rss, fn(t){ 0.0 }, rss-float64, test-names, kind-ntests, ymax, chart-desc)
                          else chart("rss", False, rss-float64, fn(t){ 0.0 }, rss-float64, test-names, kind-ntests, ymax, chart-desc)
    println("\n<!-- chart elapsed --------------- -->")
    println(chart-elapsed)
    println("\n<!-- chart rss --------------- -->")
    println(chart-rss)
  }
  ()
}


// ----------------------------------------------------
// Latex chart
// ----------------------------------------------------
fun chart( kind : string, normalize : bool, norm : test -> float64, norm-sdev : test -> float64, abs : test -> float64, test-names : list<string>, kind-ntests : list<(string,list<test>)>, ymax : float64 = 2.0, desc : string = "" ) : string {
  [ tikz-header(test-names,".bench" ++ kind)
  , kind-ntests.flatmap(fn(l){ tikz-data(kind, normalize, norm, norm-sdev, abs, l, ymax = ymax ) })
  , tikz-picture(kind, normalize, test-names, kind-ntests.map(fst), ymax = ymax, desc = desc )
  , tikz-footer(test-names) ].concat.join("\n")
}


fun tikz-header( test-names : list<string>, attr : string ) : list<string> {
  ["~ Begin Snippet { .benchmark " ++ attr ++ " }",
   "\\pgfplotsset{",
   "  xticklabels = {" ++ test-names.map(fn(n){ "\\strut " ++ n.replace-all("_","\\_")}).join(",") ++ "}",
   "}"]
}

fun tikz-footer( test-names : list<string> ) : list<string> {
  [ "~ End Snippet" ]
}

fun tikz-picture( kind : string, normalize : bool, test-names : list<string>, kind-names : list<string>, ymax : float64 = 5.0, 
                  desc : string = "", height:string = "5cm", width:string = "6cm" ) {
  val n = test-names.length - 1
  val header = [
    r"",
    r"\begin{tikzpicture}\sffamily",
    r"\begin{axis}[Chart" ++ (if (normalize) then "norm" else "abs") ++ kind ++ ",ymax=" ++ ymax.show(1) ++ ",height=" ++ height ++ ",xmax=" ++ n.show ++ ".5,width=" ++ width ++ "]",
    if (normalize) then r"  \draw (axis cs:-0.5,1) -- (axis cs:" ++ n.show ++ ".5,1);" else ""
  ]
  val mid = kind-names.map(fn(l){ r"  \draw" ++ kind ++ r"{color" ++ l ++ r"}{\data" ++ kind ++ l ++ "};"})
  val footer = [
     if (kind=="time") then r"  \legend{" ++ kind-names.map(fn(l){ "\\kind" ++ l }).join(",") ++ "};"
                       else "",
     // if (desc.is-empty) then "" else r"  \chartdesc{" ++ desc.replace-all("\n",r"\\") ++ "};",
     r"\end{axis}",
     r"\end{tikzpicture}"
  ]
  (header ++ mid ++ footer)
}


fun tikz-data( kind:string, normalize : bool, norm : test -> float64, norm-sdev : test -> float64, abs : test -> float64, kind-ntests : (string,list<test>), ymax : float64 = 5.0 ) : list<string> {
  val (k,ntests) = kind-ntests
  ["",
   r"\pgfplotstableread{",
   r"x y y-error meta"] ++
    ntests.map-indexed(fn(i:int,t:test){
      val tval = if (normalize) then t.norm else t.abs
      if (t.err.is-empty) then {
        [i.show,
         if (tval <= ymax) then tval.show-fixed(3) else ymax.show-fixed(3),
         if (tval > ymax || t.norm-sdev < 0.001) then "0.000" else t.norm-sdev.show-fixed(3),
         if (tval <= ymax) 
           then (if (normalize) then (
                   if (k == "int-full") 
                   then (if (kind=="rss") 
                            then r"{\absrssnormlabel{" ++ (t.abs / 1024.0).round.int.show ++ "mb}}" // megabytes  
                            else r"{\absnormlabel{" ++ t.abs.show-fixed(2) ++ "}}" )
                   else r"{\normlabel{" ++ t.norm.show-fixed(2) ++ "}}" )
                else r"{\abslabel{" ++ t.abs.show-fixed(2) ++ "}}")
           else (if (normalize) 
                   then (r"{\outernormlabel{" ++ t.norm.show(2) ++ "}}")
                   else (r"{\outerlabel{" ++ t.abs.show(2) ++ "}}"))
         ].join(" ")
      }
      else "" // ("" ++ i.show ++ r" 0.100 0.000 " ++ (if (i==0) then "0" elif (t.err=="NA") then "{NA}" else r"{\ensuremath{\times}}"))
    }) ++
    [r"}\data" ++ kind]
}


// ----------------------------------------------------
// Run a single test
// ----------------------------------------------------
fun insert(xs:list<float64>, y :float64) : list<float64> {
  match(xs) {
    Cons(x,xx) | y > x -> Cons(x,xx.insert(y))
    _  -> Cons(y,xs)               
  }
}

fun sort(xs : list<float64> ) : list<float64> {
  match(xs) {
    Cons(x,xx) -> xx.sort.insert(x)
    Nil -> Nil
  }
}

fun median( xs : list<float64> ) : float64 {
  val n = xs.length
  val ys = xs.sort
  match(ys.drop(n/2 - 1)) {
    Cons(x1,Cons(x2)) -> (x1 + x2)/2.0
    Cons(x,Nil)       -> x
    _                 -> 0.0
  }
}

fun run-test( variant : variant, subdir: string, test-name : string, iterations : int ) : io test {
  val pre  = "" ++ variant.file.pad-left(4) ++ ", " ++ test-name.pad-left(12) ++ ", "
  // val dir  = "out/" ++ lang
  val dir  = "build" ++ "/" ++ subdir
  val base = variant.file
  val prog = dir ++ "/out/bench/" ++ base
  val envvars  =  ""
  val progpath = prog.path
  println("\nrun: " ++ prog)

  if (!is-file(progpath)) then {
    return Test(test-name,variant,err="NA")
  }

  val results = list(1,iterations)
                .map( fn(i){ execute-test(i,base,prog,envvars)} )
                .map( fn(r){
                   match(r) {
                     Left(err)            -> Test(test-name,variant,err=err)
                     Right((elapsed,rss,size)) -> {
                       // println("elapsed: " ++ elapsed.show ++ ", rss: " ++ rss.show ++ "k")
                       Test(test-name,variant,elapsed = elapsed, rss = rss, size=size)
                     }
                 }})
  match(results.filter(fn(t){ !t.err.is-empty })) {
    Cons(t) -> return t
    _       -> ()
  }

  val melapsed   = results.map(elapsed).median
  val mrss       = results.map(fn(t){ t.rss.float64 }).median.int
  val sdev       = sqrt( results.map( fn(t){ sqr(t.elapsed - melapsed) } ).sum / results.length.float64 )
  val size = results.head.unjust.size
  // println("melapsed: " ++ melapsed.show ++ ", mrss: " ++ mrss.show ++ "k")

  Test(test-name, variant, elapsed=melapsed, rss=mrss, elapsed-sdev=sdev, size=size)  
}

fun test-sum( t1 : test, t2 : test) : test {
  t1( elapsed = t1.elapsed + t2.elapsed, rss = t1.rss + t2.rss )
}

fun execute-test( run : int, base : string, prog : string, envvars : string ) : io either<string,(float64,int,int)> 
  val timef= "out/time-" ++ base ++ ".txt"
  val cmd  = (prog ++ " --kktime 2> " ++ timef)
  ensure-dir("out".path)
  run-system("sleep 1")
  val out  = run-system-read(cmd).exn
  val st:fstat = prog.path.fstat
  val s = st.size
  print(out)
  val time = read-text-file(timef.path).split("\n").head
  if time.is-nothing return Left("no output")
  match time.unjust.parseKKTime() 
    Just((elapsed, rss)) ->
      println("" ++ run.show ++ ": elapsed: " ++ elapsed.show ++ "s, rss: " ++ rss.show ++ "kb" )
      Right( (elapsed, rss, s) )
    _ -> Left("bad format got " ++ time.unjust)


fun parseKKTime(s: string): io maybe<(float64, int)>
  val segs = s.split(",")
  if (segs.length != 4) then Nothing
  else {
    val elstr = segs[0].unjust.replace-all("info: elapsed: ", "").replace-all("s", "")
    val elapsed = elstr.parse-float64().default(0.0)
    val rstr = segs[3].unjust.replace-all(" rss : ", "")
    if rstr.contains("mb") then
      Just((elapsed, rstr.replace-all("mb", "").parse-int.default(0) * 1000))
    else
      Just((elapsed, rstr.replace-all("kb", "").parse-int.default(0)))
  }
  
