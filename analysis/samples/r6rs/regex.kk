import std/core/undiv

type regex
  Null
  Blank
  Atom(atom: string)
  Alt(re1: regex, re2: regex)
  Seq(re1: regex, re2: regex)
  Rep(re: regex)

fun debug-trace()
  trace("do-nothing")

fun (==)(re1: regex, re2: regex): bool
  match (re1, re2)
    (Null, Null) -> True
    (Blank, Blank) -> True
    (Atom(a1), Atom(a2)) -> a1 == a2
    (Alt(r1, r2), Alt(r3, r4)) -> r1.pretend-decreasing == r3 && r2.pretend-decreasing == r4
    (Seq(r1, r2), Seq(r3, r4)) -> r1.pretend-decreasing == r3 && r2.pretend-decreasing == r4
    (Rep(r1), Rep(r2)) -> r1.pretend-decreasing == r2
    _ -> False

fun match-seq(re: regex, f: (regex, regex) -> e regex): e bool
  match re
    Seq(re1, re2) ->
      match f(re1, re2)
        Null -> False
        _ -> True
    _ -> False

fun match-alt(re: regex, f: (regex, regex) -> e regex): e bool
  match re
    Alt(re1, re2) ->
      match f(re1, re2)
        Null -> False
        _ -> True
    _ -> False

fun match-rep(re: regex, f: (regex) -> e regex): e bool
  match re
    Rep(re1) ->
      match f(re1)
        Null -> False
        _ -> True
    _ -> False

fun seq(pat1: regex, pat2: regex) 
  if pat1.is-null then
    Null
  elif pat2.is-null then
    Null
  elif pat1.is-blank then
    pat2
  elif pat2.is-blank then
    pat1
  else
    Seq(pat1, pat2)

fun alt(pat1: regex, pat2: regex)
  if pat1.is-null then
    pat2
  elif pat2.is-null then
    pat1
  else
    Alt(pat1, pat2)

fun rep(pat: regex)
  if pat.is-null then
    Blank
  elif pat.is-blank then
    Blank
  else
    Rep(pat)

fun bool/regex(b: bool): regex
  if b then Blank else Null

fun regex/bool(r: regex): bool
  r.is-blank

fun empty(re: regex): <div> bool
  match re
    Blank -> True
    Null -> False
    Atom -> False
    Seq(pat1, pat2) -> seq(pat1.empty.regex, pat2.empty.regex).bool
    Alt(pat1, pat2) -> alt(pat1.empty.regex, pat2.empty.regex).bool
    Rep(_) -> True

fun derivative(re, c)
  debug-trace()
  match re
    Blank -> Null
    Null -> Null
    _ | c == re -> Blank
    Atom -> Null
    Seq(pat1, pat2) -> alt(seq(derivative(pat1, c), pat2), seq(pat1.empty.regex, derivative(pat2, c)))
    Alt(pat1, pat2) -> alt(derivative(pat1, c), derivative(pat2, c))
    Rep(pat) -> seq(derivative(pat, c), rep(pat))

fun regex-match(pattern: regex, data: list<string>): <div> bool
  match data
    Nil -> is-blank(pattern.empty.regex)
    Cons(c, cs) -> regex-match(derivative(pattern, Atom(c)), cs)

fun check(c: a, b: a, ?(==): (a,a) -> bool): bool
  c == b


fun main()
  val r = regex-match(Seq(Atom("foo"), Rep(Atom("bar"))), ["foo", "bar"])
  check(r.show, "True")