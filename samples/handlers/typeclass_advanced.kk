effect plus<a, b, c>
  (+)(a: a, b: b): c;

default handler // plus<int, int, int>
  (+)(a: int, b: int)
    add(a,b)

default handler // plus<int, float64, float64>
  (+)(a: int, b: float64) 
    add(tofloat64(a),b)

// Haskell Version
// -- POST GHC-2021
// class Plus a b c | a b -> c where
//    (+) :: a -> b -> c
// instance Plus where
//    (+) :: int -> int -> int
//    (+) a, b = add(a,b)
// instance Plus where
//    (+) :: float -> float -> float
//    (+) a, b = add(a,b)

// -- PRE GHC-2021
// class Plus a where
//    (+) :: a -> a -> a
// instance Plus where
//    (+) :: int -> int -> int
//    (+) a, b = add(a,b)
// instance Plus where
//    (+) :: float -> float -> float
//    (+) a, b = add(a,b)