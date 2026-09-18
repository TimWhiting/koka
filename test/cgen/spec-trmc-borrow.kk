// Specializing `map(xs, ^f)` on `f` used to keep map's parameter infos
// `[Own, Borrow]` on the specialized definition. TRMC then appended its
// accumulator into the borrowed slot, so the accumulator was dup'ed (every
// extend copied the context) and dropped after the recursive call (no tail
// call): this segfaulted on the C stack.
fun main()
  println(list(1, 200000).map(fn(x) x + 1).length)
