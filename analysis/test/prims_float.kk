module analysis/test/prims_float
import std/num/int64
import std/num/float64

fun analyze-convert()
    42.float64

fun result-convert()
    42.0

fun analyze-bits-identity()
    val f = 1.234
    float64-from-bits(float64-to-bits(f))

fun result-bits-identity()
    1.234

fun analyze-bits-val()
    // 0x3FF0000000000000 is 1.0 in IEEE 754
    float64-from-bits(0x3FF0000000000000.int64)

fun result-bits-val()
    1.0
