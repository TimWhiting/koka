module analysis/test/prims_bitwise
import std/num/int32
import std/num/int64

fun analyze-and()
    and(0x0F0F.int64, 0xFF00.int64)

fun result-and()
    0x0F00.int64

fun analyze-shl()
    shl(1.int64, 10)

fun result-shl()
    1024.int64

fun analyze-hilo()
    hilo32/int64(1.int32, 1.int32)

fun result-hilo()
    0x100000001.int64

fun analyze-xor()
    xor(0xAAAA.int64, 0x5555.int64)

fun result-xor()
    0xFFFF.int64
