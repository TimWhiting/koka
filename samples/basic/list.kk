pub fun show(l: list<a>, showA: (a) -> e string): e string
  l.foldl("[", fn (s, a) s ++ showA(a)) ++ "]"