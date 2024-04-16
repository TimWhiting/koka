import std/num/random
import std/num/float64
// Fermat and Solovay-Strassen primality testing in Koka.

// Translation: Tim Whiting
// Original Author: Matthew Might (in Scheme)
// Site:   http://matt.might.net/


// Mathematical support.

// square(x) = x^2
fun square(x: int) 
  x * x

// modulo-power: a fast modular exponentiation routine.
// modulo-power(base,exp,n) = base^exp [mod n]
fun modulo-power(base: int, exp, n)
  if exp == 0 then 1
  else
    if exp.is-odd then
      (base * modulo-power(base, exp - 1, n)) % n
    else
      square(modulo-power(base, exp / 2, n)) % n

// Primality tests.

// is-trivial-composite?: divisibility tests with the first few primes.
fun is-trivial-composite(n)
  n % 2 == 0 ||
  n % 3 == 0 ||
  n % 5 == 0 ||
  n % 7 == 0 ||
  n % 11 == 0 ||
  n % 13 == 0 ||
  n % 17 == 0 ||
  n % 19 == 0 ||
  n % 23 == 0

// is-fermat-prime?:
// Check, for many values of a:
//  a^(n-1) = 1 [mod n] ?  
//   If yes, could be prime.  
//   If no, then composite.
// Warning: Some Carmichael numbers (though rare) defeat this test.
fun is-fermat-prime(n: int, iterations: int)
  if iterations <= 0 then True
  else
    val byte-size = ceiling(ln(n.float64) / ln(2.0)).int
    val a = random-int() % byte-size
    if modulo-power(a, n - 1, n) == 1 then
      is-fermat-prime(n, iterations - 1)
    else False
      
// Prime generation.

// generate-fermat-prime(byte-size) yields a prime satisfying the Fermat test.
fun generate-fermat-prime(byte-size, iterations)
  val n = random-int() % byte-size
  if !n.is-trivial-composite && is-fermat-prime(n, iterations) then n
  else generate-fermat-prime(byte-size, iterations)

// Example

val iterations = 10
val byte-size = 15

fun analyze()
  generate-fermat-prime(byte-size,iterations)

fun main()
  val res = generate-fermat-prime(byte-size, iterations)
  res.println