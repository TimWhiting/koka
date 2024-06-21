fun main()
  (fn(f) 
    (fn(g) 
      (fn(do) 
        (fn(x) if x then f(1) else g(2))
      )(True)
    )(fn(z) z)
  )fn(y) y