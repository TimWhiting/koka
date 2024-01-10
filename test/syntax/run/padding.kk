fun decode-char(c : char) : exn int
  throw("decode: invalid character")

pub fun decode(s : sslice, padding : bool = True) : <div, exn> list<int>
  val _ = decode-char('a')
  val _ = padding && s.count == 2 && s.string == "=="
  val _ = padding && s.count == 1 && s.string == "="
  decode(s, padding)

pub fun main()
  "Hello this is something".slice.decode(False).println