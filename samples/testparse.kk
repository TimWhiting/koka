import std/text/pparse
import std/text/regex

type tree<a>
  Leaf(v: a)
  Branch(bs: list<tree<a>>)

fun treeL(): parse<string> tree<string>
  Leaf(takeAlphanum1())

fun treeB(): <div,parse<string>> tree<string>
  Branch(between(openParen,closeParen,treeP))

fun treeP(): <div,parse<string>> list<tree<string>>
  many1({or(treeL, treeB)})
  
fun main()
  match run(treeP, "((Hello(there))(world))")
  // match run(treeP, "(c)(d)(a)(a)")
    Left(e: perror<string>) -> println("Error: " ++ show(e, show))
    Right(a) -> println("Success " ++ show(a, show))

  // match run(treeB, "(abcde)")
  //   Left(e: perror<string>) -> println("Error: " ++ show(e, show))
  //   Right(_) -> println("Success")

fun show(t: list<tree<a>>, f: a -> string): <div> string
  map(t, fn(s) show(s, f)).join(",") 

fun show(t: tree<a>, f: a -> string): <div> string
  match t
    Leaf(v) -> "Leaf(" ++ f(v) ++ ")"
    Branch(bs) -> "Branch(" ++ show(bs, f) ++ ")"