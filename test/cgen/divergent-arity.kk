// No parameter of `spin` ever decreases, so it is divergent; deciding that must
// not examine every ordering of its twelve parameters.
fun spin(n : int, a : int, b : int, c : int, d : int, e : int, f : int, g : int, h : int, i : int, j : int, k : int)
  if n <= 0 then a + b + c + d + e + f + g + h + i + j + k
  else spin(n - 1, b, c, d, e, f, g, h, i, j, k, a)

fun main()
  println(spin(3, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11))
