// Mathematical routines.

// extended-gcd(a,b) = (x,y), such that a*x + b*y = gcd(a,b)
fun extended-gcd(a: int, b)
  if a % b == 0 then
    (0, 1)
  else
    val (x, y) = extended-gcd(b, a % b)
    (y, x - (y * (a / b)))

// modulo-inverse(a,n) = b, such that a*b = 1 [mod n].
fun modulo-inverse(a, n)
  extended-gcd(a, n).fst % n

// totient(n) = (p - 1)*(q - 1), 
// where pq is the prime factorization of n.
fun totient(p, q)
  (p - 1) * (q - 1)

// square(x) = x^2
fun square(x: int)
  x * x

// modulo-power(base,exp,n) = base^exp [mod n]
fun modulo-power(base: int, exp, n)
  if exp == 0 then
    1
  elif exp.is-odd then
    (base * modulo-power(base, exp - 1, n)) % n
  else
    square(modulo-power(base, exp / 2, n)) % n

fun gcd( x : int, y : int )
  if (x>y) then gcd(x - y, y)
  elif (x < y) then gcd(x,y - x)
  else x

// RSA routines.
// A legal public exponent e is between
// 1 and totient(n), and gcd(e,totient(n)) = 1
fun is-legal-public-exponent(e, p, q)
  (1 < e) && (e < totient(p, q)) && (1 == gcd(e, totient(p, q)))

// The private exponent is the inverse of the public exponent, mod n.
fun private-exponent(e, p, q)
  if is-legal-public-exponent(e, p, q) then
    modulo-inverse(e, totient(p, q))
  else
    throw("Not a legal public exponent for that modulus.")

// An encrypted message is c = m^e [mod n].
fun encrypt(m: int, e, n)
  if m > n then
    throw("The modulus is too small to encrypt the message.")
  else
    modulo-power(m, e, n)

// A decrypted message is m = c^d [mod n].
fun decrypt(c: int, d, n)
  modulo-power(c, d, n)

// RSA example.

fun analyze()
  val p = 41 // A "large" prime.
  val q = 47 // Another "large" prime.
  val n = p * q // The public modulus

  val e = 7 // The public exponent
  val d = private-exponent(e, p, q) // The private exponent
  
  val plaintext = 42
  val ciphertext = encrypt(plaintext, e, n)
  decrypt(ciphertext, d, n)

fun main()
  val p = 41 // A "large" prime.
  val q = 47 // Another "large" prime.
  val n = p * q // The public modulus

  val e = 7 // The public exponent
  val d = private-exponent(e, p, q) // The private exponent
  
  val plaintext = 42
  val ciphertext = encrypt(plaintext, e, n)
  val decrypted-ciphertext = decrypt(ciphertext, d, n)
  if decrypted-ciphertext != plaintext then
    throw("RSA fail!")
  else
    println("RSA success!")