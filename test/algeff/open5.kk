alias map<k,v,e::E> = list<(k, v, () -> e ())>
fun do-something(?something: map<k,v,e>, ?k/show: (k) -> e string, ?v/show: (v) -> e string): e string
  something.map(fn((k, v, _)) show(k) ++ " -> " ++ show(v)).join("")

val basic/something : map<int,int,<>> = []

fun main(): console ()
  val r = do-something()
  r.println
