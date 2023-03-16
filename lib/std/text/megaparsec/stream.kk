module std/text/megaparsec/stream

struct istream<s,t,c>
  tokenToChunk: (t) -> c
  tokensToChunk: (list<t>) -> c
  take1: (s) -> maybe<(t,s)>;

struct stream<s,t,c>
  st: s
  iface: istream<s,t,c>;

fun take1(s: stream<s,t,c>): maybe<(t,s)>
  s.iface.take1()(s.st)

pub fun mkStream<s,t,c>(s: s, tokensToChunk: (list<t>) -> c, take1: (s) -> maybe<(t,s)>): stream<s,t,c>
  val ttC = fn(s1) tokensToChunk([s1])
  Stream(s, Istream(ttC, tokensToChunk, take1))

fun getSingle(l: list<s>): maybe<(s, list<s>)>
  match l 
    Cons(h, tl) -> Just((h, tl))
    Nil -> Nothing

fun main()
  val s = mkStream("abcd".list, fn(s1) s1, getSingle)
  match s.take1
    Just((c, _)) -> println(c.show)
    Nothing -> println("nothing")
