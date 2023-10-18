effect xeff
  fun doA(a: int, b: int, c: int, d: int, e: int, f: int): string
  fun doB(a: int, b: int, c: int, d: int, e: int): string
  fun doC(a: int, b: int, c: int, d: int): string
  fun doD(a: int, b: int, c: int): string
  fun doE(a: int, b: int): string
  fun doF(a: int): string
  fun doG(): string

fun main()
  with handler
    fun doA(a, b, c, d, e, f)
      [a, b, c, d, e, f].show
    fun doB(a, b, c, d, e)
      [a, b, c, d, e].show
    fun doC(a, b, c, d)
      [a, b, c, d].show
    fun doD(a, b, c)
      [a, b, c].show
    fun doE(a, b)
      "(" ++ show(a) ++ ", " ++ show(b) ++ ")"
    fun doF(a)
      a.show
    fun doG()
      "G"
  val result = doA(1, 2, 3, 4, 5, 6) ++ doB(7, 8, 9, 10, 11) ++ doC(12, 13, 14, 15) ++ doD(16, 17, 18) ++ doE(19, 20) ++ doF(21) ++ doG()
  result.println