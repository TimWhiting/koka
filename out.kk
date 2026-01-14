koka-3.2.3: unregistering (local file changes: src/Core/FlowAnalysis/FixpointMonad.hs)
koka> build (lib + exe) with ghc-9.6.6
Preprocessing library for koka-3.2.3..
Building library for koka-3.2.3..
[ 15 of 141] Compiling Core.FlowAnalysis.FixpointMonad [Source file changed]
[ 90 of 141] Compiling Core.FlowAnalysis.Literals [Core.FlowAnalysis.FixpointMonad changed]
[ 91 of 141] Compiling Core.FlowAnalysis.Demand.AbstractValue [Core.FlowAnalysis.FixpointMonad changed]
[ 93 of 141] Compiling Core.FlowAnalysis.Monad [Core.FlowAnalysis.FixpointMonad changed]
[ 94 of 141] Compiling Core.FlowAnalysis.Syntax [Core.FlowAnalysis.FixpointMonad changed]
[ 95 of 141] Compiling Core.FlowAnalysis.Full.KCFA.AbstractValue [Core.FlowAnalysis.FixpointMonad changed]
[ 96 of 141] Compiling Core.FlowAnalysis.Full.KCFA.Monad [Core.FlowAnalysis.FixpointMonad changed]
[ 97 of 141] Compiling Core.FlowAnalysis.Full.DMCFAR.AbstractValue [Core.FlowAnalysis.FixpointMonad changed]
[ 98 of 141] Compiling Core.FlowAnalysis.Full.DMCFAR.Monad [Core.FlowAnalysis.FixpointMonad changed]
[ 99 of 141] Compiling Core.FlowAnalysis.Full.DMCFA.AbstractValue [Core.FlowAnalysis.FixpointMonad changed]
[100 of 141] Compiling Core.FlowAnalysis.Full.DMCFA.Monad [Core.FlowAnalysis.FixpointMonad changed]
[101 of 141] Compiling Core.FlowAnalysis.Full.AbstractValue [Core.FlowAnalysis.FixpointMonad changed]
[102 of 141] Compiling Core.FlowAnalysis.Full.AAC.Monad [Core.FlowAnalysis.FixpointMonad changed]
[103 of 141] Compiling Core.FlowAnalysis.Demand.DemandMonad [Core.FlowAnalysis.FixpointMonad changed]
[116 of 141] Compiling Core.FlowAnalysis.Full.PrimitivesOld [Core.FlowAnalysis.FixpointMonad changed]
[117 of 141] Compiling Core.FlowAnalysis.Full.AAC.AAC [Core.FlowAnalysis.FixpointMonad changed]
[118 of 141] Compiling Core.FlowAnalysis.Full.AAC.Syntax [Core.FlowAnalysis.FixpointMonad changed]
[119 of 141] Compiling Core.FlowAnalysis.Full.KCFA.Primitives [Core.FlowAnalysis.FixpointMonad changed]
[120 of 141] Compiling Core.FlowAnalysis.Full.KCFA.KCFA [Core.FlowAnalysis.FixpointMonad changed]
[121 of 141] Compiling Core.FlowAnalysis.Full.KCFA.Syntax [Core.FlowAnalysis.FixpointMonad changed]
[122 of 141] Compiling Core.FlowAnalysis.Full.DMCFAR.Primitives [Core.FlowAnalysis.FixpointMonad changed]
[123 of 141] Compiling Core.FlowAnalysis.Full.DMCFAR.DMCFA [Core.FlowAnalysis.FixpointMonad changed]
[124 of 141] Compiling Core.FlowAnalysis.Full.DMCFAR.Syntax [Core.FlowAnalysis.FixpointMonad changed]
[125 of 141] Compiling Core.FlowAnalysis.Full.DMCFA.Primitives [Core.FlowAnalysis.FixpointMonad changed]
[126 of 141] Compiling Core.FlowAnalysis.Full.DMCFA.DMCFA [Core.FlowAnalysis.FixpointMonad changed]
[127 of 141] Compiling Core.FlowAnalysis.Full.DMCFA.Syntax [Core.FlowAnalysis.FixpointMonad changed]
[128 of 141] Compiling Core.FlowAnalysis.Demand.DemandAnalysis [Core.FlowAnalysis.FixpointMonad changed]
[129 of 141] Compiling Core.FlowAnalysis.Demand.Primitives [Core.FlowAnalysis.FixpointMonad changed]
[130 of 141] Compiling Core.FlowAnalysis.Demand.Syntax [Core.FlowAnalysis.FixpointMonad changed]
[131 of 141] Compiling Core.FlowAnalysis.Demand.ConstantProp [Core.FlowAnalysis.FixpointMonad changed]
[138 of 141] Compiling Compile.Build [Core.FlowAnalysis.Full.DMCFA.Syntax changed]
Warning: The following header files listed in the main library's c-sources
will not be used: src/Platform/cpp/Platform/cconsole.h.
Header files should be in the 'include' or 'install-include' stanza.
See https://cabal.readthedocs.io/en/3.10/cabal-package.html#pkg-field-includes
Preprocessing executable 'koka' for koka-3.2.3..
Building executable 'koka' for koka-3.2.3..
[18 of 18] Linking .stack-work/dist/aarch64-osx/ghc-9.6.6/build/koka/koka [Library changed]
koka> copy/register
Installing library in /Users/timwhiting/koka/.stack-work/install/aarch64-osx/50e7567ab93459510bfd412b9898f4e9df3111e36f9d2dfd4eb8cba51d1770ee/9.6.6/lib/aarch64-osx-ghc-9.6.6/koka-3.2.3-JKPkVdIR1OY3NjAC7CLiJ8
Installing executable koka in /Users/timwhiting/koka/.stack-work/install/aarch64-osx/50e7567ab93459510bfd412b9898f4e9df3111e36f9d2dfd4eb8cba51d1770ee/9.6.6/bin
Registering library for koka-3.2.3..
]4;0;?\[6nparse   : .../std/core/types.kk
parse   : .../std/core/undiv.kk
parse   : .../std/core/order.kk
parse   : .../std/core/hnd.kk
parse   : .../std/core/exn.kk
parse   : .../std/core/bool.kk
parse   : .../std/core/unsafe.kk
parse   : .../std/core/int.kk
parse   : .../std/core/char.kk
parse   : .../std/core/string.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/maybe2.kk
parse   : .../std/core/maybe.kk
parse   : .../std/core/list.kk
parse   : .../std/core/tuple.kk
parse   : .../std/core/lazy.kk
parse   : .../std/core/either.kk
parse   : .../std/core/show.kk
parse   : .../std/core/debug.kk
parse   : .../std/core/console.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core.kk
parse   : .../std/core/delayed.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
check   : std/core/types
check   : std/core/int
check   : std/core/bool
check   : std/core/lazy
check   : std/core/unsafe
check   : std/core/undiv
check   : std/core/hnd
check   : std/core/char
check   : std/core/order
check   : std/core/tuple
check   : std/core/exn
check   : std/core/delayed
check   : std/core/either
check   : std/core/maybe2
check   : std/core/maybe
check   : std/core/vector
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow
dmcfa,analysis/benchmarks/suite/complex-flow/complex-layers,0,0,0,180,62,1.011111111111111,1.096774193548387,1.2,1.06993006993007,0.01001,0.010349,0.006594
dmcfa,analysis/benchmarks/suite/complex-flow/complex-nested-interleave,0,0,1,128,14,1.0,1.0,1.0,1.009009009009009,0.002294,0.002589,0.002086
dmcfa,analysis/benchmarks/suite/complex-flow/complex-non-tail-call,0,0,0,78,4,1.0,1.0,1.0,1.0606060606060606,0.001415,0.001024,0.001558
dmcfa,analysis/benchmarks/suite/complex-flow/complex-recursive,0,0,0,99,14,1.0909090909090908,1.3571428571428572,2.3333333333333335,1.1645569620253164,0.00338,0.002975,0.003994
dmcfa,analysis/benchmarks/suite/complex-flow/complex-resume-func,0,0,1,74,5,1.0,1.0,1.0,1.0,0.001031,0.00178,0.000807
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-call,0,0,1,72,4,1.0,1.0,1.0,1.0,0.001356,0.001546,0.001376
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-effect,0,0,1,61,4,1.0,1.0,1.0,1.0,0.001517,0.000718,0.000599
dmcfa,analysis/benchmarks/suite/complex-flow/complex-layers,0,1,0,231,68,1.0,1.0,1.0,1.0923913043478262,0.009091,0.00945,0.010361
dmcfa,analysis/benchmarks/suite/complex-flow/complex-nested-interleave,0,1,1,144,16,1.0,1.0,1.0,1.0,0.00513,0.002773,0.002495
dmcfa,analysis/benchmarks/suite/complex-flow/complex-non-tail-call,0,1,1,83,4,1.0,1.0,1.0,1.0,0.001195,0.001484,0.001087
dmcfa,analysis/benchmarks/suite/complex-flow/complex-recursive,0,1,0,160,23,1.13125,2.217391304347826,2.7142857142857144,1.1517857142857142,0.00795,0.008223,0.007819
dmcfa,analysis/benchmarks/suite/complex-flow/complex-resume-func,0,1,1,74,5,1.0,1.0,1.0,1.0,0.001219,0.001402,0.00099
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-call,0,1,1,72,4,1.0,1.0,1.0,1.0,0.001191,0.00092,0.001223
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-effect,0,1,1,61,4,1.0,1.0,1.0,1.0,0.000744,0.001096,0.000777
dmcfa,analysis/benchmarks/suite/complex-flow/complex-layers,0,2,1,243,69,1.0,1.0,1.0,1.0,0.008419,0.008249,0.008212
dmcfa,analysis/benchmarks/suite/complex-flow/complex-nested-interleave,0,2,1,144,16,1.0,1.0,1.0,1.0,0.002894,0.002967,0.002673
dmcfa,analysis/benchmarks/suite/complex-flow/complex-non-tail-call,0,2,1,83,4,1.0,1.0,1.0,1.0,0.001193,0.001592,0.001528
dmcfa,analysis/benchmarks/suite/complex-flow/complex-recursive,0,2,0,312,83,1.1346153846153846,4.024096385542169,2.3333333333333335,1.1844660194174756,0.054986,0.065457,0.054242
dmcfa,analysis/benchmarks/suite/complex-flow/complex-resume-func,0,2,1,74,5,1.0,1.0,1.0,1.0,0.001555,0.001,0.001303
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-call,0,2,1,72,4,1.0,1.0,1.0,1.0,0.00096,0.001435,0.001001
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-effect,0,2,1,61,4,1.0,1.0,1.0,1.0,0.001073,0.00087,0.001115
dmcfa,analysis/benchmarks/suite/complex-flow/complex-layers,0,3,1,243,69,1.0,1.0,1.0,1.0,0.008458,0.008083,0.00798
dmcfa,analysis/benchmarks/suite/complex-flow/complex-nested-interleave,0,3,1,144,16,1.0,1.0,1.0,1.0,0.002804,0.00278,0.002865
dmcfa,analysis/benchmarks/suite/complex-flow/complex-non-tail-call,0,3,1,83,4,1.0,1.0,1.0,1.0,0.001464,0.001598,0.001173
dmcfa,analysis/benchmarks/suite/complex-flow/complex-recursive,0,3,1,314,40,1.0,1.075,1.0666666666666667,1.0131004366812226,0.010473,0.011394,0.010756
dmcfa,analysis/benchmarks/suite/complex-flow/complex-resume-func,0,3,1,74,5,1.0,1.0,1.0,1.0,0.00123,0.001624,0.001052
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-call,0,3,1,72,4,1.0,1.0,1.0,1.0,0.00129,0.001415,0.001081
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-effect,0,3,1,61,4,1.0,1.0,1.0,1.0,0.001251,0.000997,0.000936
dmcfa,analysis/benchmarks/suite/complex-flow/complex-layers,0,4,1,243,69,1.0,1.0,1.0,1.0,0.008131,0.008367,0.008333
dmcfa,analysis/benchmarks/suite/complex-flow/complex-nested-interleave,0,4,1,144,16,1.0,1.0,1.0,1.0,0.002879,0.003058,0.002892
dmcfa,analysis/benchmarks/suite/complex-flow/complex-non-tail-call,0,4,1,83,4,1.0,1.0,1.0,1.0,0.00159,0.001285,0.001543
dmcfa,analysis/benchmarks/suite/complex-flow/complex-recursive,0,4,1,330,28,1.0,1.0,1.0,1.0,0.01009,0.01058,0.009579
dmcfa,analysis/benchmarks/suite/complex-flow/complex-resume-func,0,4,1,74,5,1.0,1.0,1.0,1.0,0.001371,0.001365,0.001048
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-call,0,4,1,72,4,1.0,1.0,1.0,1.0,0.001302,0.001014,0.001346
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-effect,0,4,1,61,4,1.0,1.0,1.0,1.0,0.000879,0.001194,0.00089
dmcfa,analysis/benchmarks/suite/complex-flow/complex-layers,1,0,0,217,69,1.0092165898617511,1.0724637681159421,1.125,1.0773480662983426,0.009608,0.009422,0.009319
dmcfa,analysis/benchmarks/suite/complex-flow/complex-nested-interleave,1,0,1,141,16,1.0,1.0,1.0,1.008130081300813,0.003211,0.003111,0.003507
dmcfa,analysis/benchmarks/suite/complex-flow/complex-non-tail-call,1,0,0,78,4,1.0,1.0,1.0,1.0606060606060606,0.001075,0.001292,0.0009
dmcfa,analysis/benchmarks/suite/complex-flow/complex-recursive,1,0,0,137,17,1.102189781021898,1.6470588235294117,2.0,1.174757281553398,0.005397,0.005968,0.005545
dmcfa,analysis/benchmarks/suite/complex-flow/complex-resume-func,1,0,1,74,5,1.0,1.0,1.0,1.0,0.001237,0.001382,0.00109
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-call,1,0,1,72,4,1.0,1.0,1.0,1.0,0.001066,0.000803,0.001104
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-effect,1,0,1,61,4,1.0,1.0,1.0,1.0,0.000719,0.000919,0.000677
dmcfa,analysis/benchmarks/suite/complex-flow/complex-layers,1,1,0,232,70,1.0,1.0,1.0,1.07,0.013117,0.011251,0.009886
dmcfa,analysis/benchmarks/suite/complex-flow/complex-nested-interleave,1,1,1,144,16,1.0,1.0,1.0,1.0,0.003971,0.003826,0.003534
dmcfa,analysis/benchmarks/suite/complex-flow/complex-non-tail-call,1,1,1,83,4,1.0,1.0,1.0,1.0,0.001632,0.001302,0.001657
dmcfa,analysis/benchmarks/suite/complex-flow/complex-recursive,1,1,0,198,21,1.1313131313131313,2.142857142857143,2.272727272727273,1.1521739130434783,0.012392,0.012642,0.012356
dmcfa,analysis/benchmarks/suite/complex-flow/complex-resume-func,1,1,1,74,5,1.0,1.0,1.0,1.0,0.001559,0.001215,0.001451
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-call,1,1,1,72,4,1.0,1.0,1.0,1.0,0.001018,0.001678,0.001696
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-effect,1,1,1,61,4,1.0,1.0,1.0,1.0,0.001246,0.001131,0.001233
dmcfa,analysis/benchmarks/suite/complex-flow/complex-layers,1,2,1,243,71,1.0,1.0,1.0,1.0,0.012965,0.013303,0.012678
dmcfa,analysis/benchmarks/suite/complex-flow/complex-nested-interleave,1,2,1,144,16,1.0,1.0,1.0,1.0,0.005252,0.004583,0.004465
dmcfa,analysis/benchmarks/suite/complex-flow/complex-non-tail-call,1,2,1,83,4,1.0,1.0,1.0,1.0,0.001878,0.001359,0.00171
dmcfa,analysis/benchmarks/suite/complex-flow/complex-recursive,1,2,0,467,80,1.1413276231263383,3.8625,2.1147540983606556,1.1764705882352942,0.098049,0.098186,0.097323
dmcfa,analysis/benchmarks/suite/complex-flow/complex-resume-func,1,2,1,74,5,1.0,1.0,1.0,1.0,0.001468,0.002104,0.0017
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-call,1,2,1,72,4,1.0,1.0,1.0,1.0,0.001569,0.001279,0.00146
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-effect,1,2,1,61,4,1.0,1.0,1.0,1.0,0.001169,0.001409,0.001181
dmcfa,analysis/benchmarks/suite/complex-flow/complex-layers,1,3,1,243,71,1.0,1.0,1.0,1.0,0.013768,0.013655,0.012781
dmcfa,analysis/benchmarks/suite/complex-flow/complex-nested-interleave,1,3,1,144,16,1.0,1.0,1.0,1.0,0.004541,0.005303,0.005145
dmcfa,analysis/benchmarks/suite/complex-flow/complex-non-tail-call,1,3,1,83,4,1.0,1.0,1.0,1.0,0.00192,0.001467,0.001692
dmcfa,analysis/benchmarks/suite/complex-flow/complex-recursive,1,3,1,327,27,1.0,1.0,1.0,1.0040816326530613,0.015785,0.015404,0.014244
dmcfa,analysis/benchmarks/suite/complex-flow/complex-resume-func,1,3,1,74,5,1.0,1.0,1.0,1.0,0.001698,0.00173,0.001406
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-call,1,3,1,72,4,1.0,1.0,1.0,1.0,0.001414,0.001218,0.001571
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-effect,1,3,1,61,4,1.0,1.0,1.0,1.0,0.001122,0.001464,0.001099
dmcfa,analysis/benchmarks/suite/complex-flow/complex-layers,1,4,1,243,71,1.0,1.0,1.0,1.0,0.013307,0.014022,0.012754
dmcfa,analysis/benchmarks/suite/complex-flow/complex-nested-interleave,1,4,1,144,16,1.0,1.0,1.0,1.0,0.005001,0.004913,0.004622
dmcfa,analysis/benchmarks/suite/complex-flow/complex-non-tail-call,1,4,1,83,4,1.0,1.0,1.0,1.0,0.00148,0.001743,0.001909
dmcfa,analysis/benchmarks/suite/complex-flow/complex-recursive,1,4,1,330,28,1.0,1.0,1.0,1.0,0.015598,0.016161,0.015462
dmcfa,analysis/benchmarks/suite/complex-flow/complex-resume-func,1,4,1,74,5,1.0,1.0,1.0,1.0,0.001747,0.001492,0.001825
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-call,1,4,1,72,4,1.0,1.0,1.0,1.0,0.001491,0.001242,0.001518
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-effect,1,4,1,61,4,1.0,1.0,1.0,1.0,0.001104,0.001356,0.001124
dmcfa,analysis/benchmarks/suite/complex-flow/complex-layers,2,0,0,217,69,1.0092165898617511,1.0724637681159421,1.125,1.0773480662983426,0.011123,0.011401,0.011457
dmcfa,analysis/benchmarks/suite/complex-flow/complex-nested-interleave,2,0,1,141,16,1.0,1.0,1.0,1.008130081300813,0.003355,0.003331,0.003244
dmcfa,analysis/benchmarks/suite/complex-flow/complex-non-tail-call,2,0,0,78,4,1.0,1.0,1.0,1.0606060606060606,0.001211,0.001211,0.000881
dmcfa,analysis/benchmarks/suite/complex-flow/complex-recursive,2,0,0,137,17,1.102189781021898,1.6470588235294117,2.0,1.174757281553398,0.005722,0.00545,0.005656
dmcfa,analysis/benchmarks/suite/complex-flow/complex-resume-func,2,0,1,74,5,1.0,1.0,1.0,1.0,0.001188,0.000943,0.001405
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-call,2,0,1,72,4,1.0,1.0,1.0,1.0,0.001141,0.000884,0.001267
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-effect,2,0,1,61,4,1.0,1.0,1.0,1.0,0.000692,0.000947,0.00069
dmcfa,analysis/benchmarks/suite/complex-flow/complex-layers,2,1,0,232,70,1.0,1.0,1.0,1.07,0.012075,0.011982,0.011425
dmcfa,analysis/benchmarks/suite/complex-flow/complex-nested-interleave,2,1,1,144,16,1.0,1.0,1.0,1.0,0.003989,0.00399,0.004432
dmcfa,analysis/benchmarks/suite/complex-flow/complex-non-tail-call,2,1,1,83,4,1.0,1.0,1.0,1.0,0.00123,0.001531,0.001219
dmcfa,analysis/benchmarks/suite/complex-flow/complex-recursive,2,1,0,198,21,1.1313131313131313,2.142857142857143,2.272727272727273,1.1521739130434783,0.012018,0.012771,0.012692
dmcfa,analysis/benchmarks/suite/complex-flow/complex-resume-func,2,1,1,74,5,1.0,1.0,1.0,1.0,0.00126,0.001803,0.001362
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-call,2,1,1,72,4,1.0,1.0,1.0,1.0,0.001244,0.001057,0.001289
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-effect,2,1,1,61,4,1.0,1.0,1.0,1.0,0.000936,0.00128,0.001023
dmcfa,analysis/benchmarks/suite/complex-flow/complex-layers,2,2,1,243,71,1.0,1.0,1.0,1.0,0.014026,0.014395,0.014193
dmcfa,analysis/benchmarks/suite/complex-flow/complex-nested-interleave,2,2,1,144,16,1.0,1.0,1.0,1.0,0.005084,0.004901,0.004795
dmcfa,analysis/benchmarks/suite/complex-flow/complex-non-tail-call,2,2,1,83,4,1.0,1.0,1.0,1.0,0.001802,0.001411,0.001663
dmcfa,analysis/benchmarks/suite/complex-flow/complex-recursive,2,2,0,467,80,1.1413276231263383,3.8625,2.1147540983606556,1.1764705882352942,0.091535,0.091534,0.091864
dmcfa,analysis/benchmarks/suite/complex-flow/complex-resume-func,2,2,1,74,5,1.0,1.0,1.0,1.0,0.001435,0.001729,0.001379
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-call,2,2,1,72,4,1.0,1.0,1.0,1.0,0.001331,0.001634,0.001381
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-effect,2,2,1,61,4,1.0,1.0,1.0,1.0,0.001415,0.001102,0.001126
dmcfa,analysis/benchmarks/suite/complex-flow/complex-layers,2,3,1,243,71,1.0,1.0,1.0,1.0,0.015062,0.015708,0.015059
dmcfa,analysis/benchmarks/suite/complex-flow/complex-nested-interleave,2,3,1,144,16,1.0,1.0,1.0,1.0,0.005037,0.005195,0.004999
dmcfa,analysis/benchmarks/suite/complex-flow/complex-non-tail-call,2,3,1,83,4,1.0,1.0,1.0,1.0,0.001649,0.001413,0.001885
dmcfa,analysis/benchmarks/suite/complex-flow/complex-recursive,2,3,1,327,27,1.0,1.0,1.0,1.0040816326530613,0.014514,0.01422,0.013619
dmcfa,analysis/benchmarks/suite/complex-flow/complex-resume-func,2,3,1,74,5,1.0,1.0,1.0,1.0,0.001482,0.001842,0.00138
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-call,2,3,1,72,4,1.0,1.0,1.0,1.0,0.001388,0.001216,0.001454
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-effect,2,3,1,61,4,1.0,1.0,1.0,1.0,0.001088,0.001289,0.001075
dmcfa,analysis/benchmarks/suite/complex-flow/complex-layers,2,4,1,243,71,1.0,1.0,1.0,1.0,0.015466,0.0158,0.015806
dmcfa,analysis/benchmarks/suite/complex-flow/complex-nested-interleave,2,4,1,144,16,1.0,1.0,1.0,1.0,0.005099,0.005182,0.005068
dmcfa,analysis/benchmarks/suite/complex-flow/complex-non-tail-call,2,4,1,83,4,1.0,1.0,1.0,1.0,0.0017,0.001441,0.001683
dmcfa,analysis/benchmarks/suite/complex-flow/complex-recursive,2,4,1,330,28,1.0,1.0,1.0,1.0,0.014759,0.014973,0.014526
dmcfa,analysis/benchmarks/suite/complex-flow/complex-resume-func,2,4,1,74,5,1.0,1.0,1.0,1.0,0.001641,0.001801,0.001415
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-call,2,4,1,72,4,1.0,1.0,1.0,1.0,0.001384,0.001237,0.001487
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-effect,2,4,1,61,4,1.0,1.0,1.0,1.0,0.001099,0.001348,0.001089
dmcfa,analysis/benchmarks/suite/complex-flow/complex-layers,3,0,0,217,69,1.0092165898617511,1.0724637681159421,1.125,1.076086956521739,0.011162,0.011011,0.010436
dmcfa,analysis/benchmarks/suite/complex-flow/complex-nested-interleave,3,0,1,141,16,1.0,1.0,1.0,1.008130081300813,0.003336,0.003317,0.003527
dmcfa,analysis/benchmarks/suite/complex-flow/complex-non-tail-call,3,0,0,78,4,1.0,1.0,1.0,1.0606060606060606,0.000905,0.001207,0.000872
dmcfa,analysis/benchmarks/suite/complex-flow/complex-recursive,3,0,0,137,17,1.102189781021898,1.6470588235294117,2.0,1.174757281553398,0.005535,0.005519,0.005658
dmcfa,analysis/benchmarks/suite/complex-flow/complex-resume-func,3,0,1,74,5,1.0,1.0,1.0,1.0,0.001299,0.001372,0.001068
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-call,3,0,1,72,4,1.0,1.0,1.0,1.0,0.000993,0.000848,0.001058
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-effect,3,0,1,61,4,1.0,1.0,1.0,1.0,0.000685,0.000999,0.000688
dmcfa,analysis/benchmarks/suite/complex-flow/complex-layers,3,1,0,232,70,1.0,1.0,1.0,1.0689655172413792,0.013078,0.012973,0.012499
dmcfa,analysis/benchmarks/suite/complex-flow/complex-nested-interleave,3,1,1,144,16,1.0,1.0,1.0,1.0,0.003986,0.005033,0.003985
dmcfa,analysis/benchmarks/suite/complex-flow/complex-non-tail-call,3,1,1,83,4,1.0,1.0,1.0,1.0,0.001398,0.001584,0.001623
dmcfa,analysis/benchmarks/suite/complex-flow/complex-recursive,3,1,0,198,21,1.1313131313131313,2.142857142857143,2.272727272727273,1.1521739130434783,0.012724,0.01283,0.012557
dmcfa,analysis/benchmarks/suite/complex-flow/complex-resume-func,3,1,1,74,5,1.0,1.0,1.0,1.0,0.001345,0.001561,0.001588
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-call,3,1,1,72,4,1.0,1.0,1.0,1.0,0.001134,0.001426,0.001095
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-effect,3,1,1,61,4,1.0,1.0,1.0,1.0,0.001151,0.000999,0.000953
dmcfa,analysis/benchmarks/suite/complex-flow/complex-layers,3,2,1,243,71,1.0,1.0,1.0,1.0,0.015498,0.015808,0.016193
dmcfa,analysis/benchmarks/suite/complex-flow/complex-nested-interleave,3,2,1,144,16,1.0,1.0,1.0,1.0,0.005303,0.005075,0.004978
dmcfa,analysis/benchmarks/suite/complex-flow/complex-non-tail-call,3,2,1,83,4,1.0,1.0,1.0,1.0,0.001782,0.001454,0.001707
dmcfa,analysis/benchmarks/suite/complex-flow/complex-recursive,3,2,0,467,80,1.1413276231263383,3.8625,2.1147540983606556,1.1764705882352942,0.093908,0.092542,0.09453
dmcfa,analysis/benchmarks/suite/complex-flow/complex-resume-func,3,2,1,74,5,1.0,1.0,1.0,1.0,0.001556,0.001905,0.001801
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-call,3,2,1,72,4,1.0,1.0,1.0,1.0,0.00124,0.001474,0.00118
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-effect,3,2,1,61,4,1.0,1.0,1.0,1.0,0.001281,0.00112,0.001369
dmcfa,analysis/benchmarks/suite/complex-flow/complex-layers,3,3,1,243,71,1.0,1.0,1.0,1.0,0.016883,0.016658,0.01624
dmcfa,analysis/benchmarks/suite/complex-flow/complex-nested-interleave,3,3,1,144,16,1.0,1.0,1.0,1.0,0.005338,0.005322,0.005043
dmcfa,analysis/benchmarks/suite/complex-flow/complex-non-tail-call,3,3,1,83,4,1.0,1.0,1.0,1.0,0.001684,0.001416,0.001783
dmcfa,analysis/benchmarks/suite/complex-flow/complex-recursive,3,3,1,327,27,1.0,1.0,1.0,1.0040816326530613,0.014222,0.014282,0.014261
dmcfa,analysis/benchmarks/suite/complex-flow/complex-resume-func,3,3,1,74,5,1.0,1.0,1.0,1.0,0.00271,0.00269,0.001449
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-call,3,3,1,72,4,1.0,1.0,1.0,1.0,0.001565,0.002008,0.00187
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-effect,3,3,1,61,4,1.0,1.0,1.0,1.0,0.00272,0.00206,0.001328
dmcfa,analysis/benchmarks/suite/complex-flow/complex-layers,3,4,1,243,71,1.0,1.0,1.0,1.0,0.019493,0.018317,0.018375
dmcfa,analysis/benchmarks/suite/complex-flow/complex-nested-interleave,3,4,1,144,16,1.0,1.0,1.0,1.0,0.005034,0.005382,0.005312
dmcfa,analysis/benchmarks/suite/complex-flow/complex-non-tail-call,3,4,1,83,4,1.0,1.0,1.0,1.0,0.00182,0.001448,0.001832
dmcfa,analysis/benchmarks/suite/complex-flow/complex-recursive,3,4,1,330,28,1.0,1.0,1.0,1.0,0.015416,0.016192,0.014978
dmcfa,analysis/benchmarks/suite/complex-flow/complex-resume-func,3,4,1,74,5,1.0,1.0,1.0,1.0,0.001617,0.001833,0.001457
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-call,3,4,1,72,4,1.0,1.0,1.0,1.0,0.00146,0.001269,0.001709
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-effect,3,4,1,61,4,1.0,1.0,1.0,1.0,0.001142,0.001432,0.001114
dmcfa,analysis/benchmarks/suite/complex-flow/complex-layers,4,0,0,217,69,1.0092165898617511,1.0724637681159421,1.125,1.076086956521739,0.011666,0.01237,0.011164
dmcfa,analysis/benchmarks/suite/complex-flow/complex-nested-interleave,4,0,1,141,16,1.0,1.0,1.0,1.008130081300813,0.003812,0.003934,0.004127
dmcfa,analysis/benchmarks/suite/complex-flow/complex-non-tail-call,4,0,0,78,4,1.0,1.0,1.0,1.0606060606060606,0.000922,0.001367,0.000888
dmcfa,analysis/benchmarks/suite/complex-flow/complex-recursive,4,0,0,137,17,1.102189781021898,1.6470588235294117,2.0,1.174757281553398,0.006254,0.006269,0.006187
dmcfa,analysis/benchmarks/suite/complex-flow/complex-resume-func,4,0,1,74,5,1.0,1.0,1.0,1.0,0.001841,0.001686,0.000996
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-call,4,0,1,72,4,1.0,1.0,1.0,1.0,0.000986,0.000808,0.002371
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-effect,4,0,1,61,4,1.0,1.0,1.0,1.0,0.000883,0.002417,0.001585
dmcfa,analysis/benchmarks/suite/complex-flow/complex-layers,4,1,0,232,70,1.0,1.0,1.0,1.0689655172413792,0.013824,0.016914,0.013961
dmcfa,analysis/benchmarks/suite/complex-flow/complex-nested-interleave,4,1,1,144,16,1.0,1.0,1.0,1.0,0.004441,0.004453,0.004187
dmcfa,analysis/benchmarks/suite/complex-flow/complex-non-tail-call,4,1,1,83,4,1.0,1.0,1.0,1.0,0.001277,0.001984,0.001632
dmcfa,analysis/benchmarks/suite/complex-flow/complex-recursive,4,1,0,198,21,1.1313131313131313,2.142857142857143,2.272727272727273,1.1521739130434783,0.012759,0.013036,0.012744
dmcfa,analysis/benchmarks/suite/complex-flow/complex-resume-func,4,1,1,74,5,1.0,1.0,1.0,1.0,0.001346,0.00168,0.001651
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-call,4,1,1,72,4,1.0,1.0,1.0,1.0,0.00115,0.001516,0.001086
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-effect,4,1,1,61,4,1.0,1.0,1.0,1.0,0.00124,0.00097,0.001301
dmcfa,analysis/benchmarks/suite/complex-flow/complex-layers,4,2,1,243,71,1.0,1.0,1.0,1.0,0.016115,0.015285,0.015408
dmcfa,analysis/benchmarks/suite/complex-flow/complex-nested-interleave,4,2,1,144,16,1.0,1.0,1.0,1.0,0.00503,0.005104,0.004897
dmcfa,analysis/benchmarks/suite/complex-flow/complex-non-tail-call,4,2,1,83,4,1.0,1.0,1.0,1.0,0.001734,0.001791,0.001421
dmcfa,analysis/benchmarks/suite/complex-flow/complex-recursive,4,2,0,467,80,1.1413276231263383,3.8625,2.1147540983606556,1.1764705882352942,0.094581,0.098973,0.095859
dmcfa,analysis/benchmarks/suite/complex-flow/complex-resume-func,4,2,1,74,5,1.0,1.0,1.0,1.0,0.001928,0.001454,0.001716
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-call,4,2,1,72,4,1.0,1.0,1.0,1.0,0.001229,0.001516,0.001158
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-effect,4,2,1,61,4,1.0,1.0,1.0,1.0,0.001257,0.001046,0.001362
dmcfa,analysis/benchmarks/suite/complex-flow/complex-layers,4,3,1,243,71,1.0,1.0,1.0,1.0,0.016959,0.016332,0.016172
dmcfa,analysis/benchmarks/suite/complex-flow/complex-nested-interleave,4,3,1,144,16,1.0,1.0,1.0,1.0,0.005112,0.005142,0.004999
dmcfa,analysis/benchmarks/suite/complex-flow/complex-non-tail-call,4,3,1,83,4,1.0,1.0,1.0,1.0,0.001632,0.001873,0.001488
dmcfa,analysis/benchmarks/suite/complex-flow/complex-recursive,4,3,1,327,27,1.0,1.0,1.0,1.0040816326530613,0.014049,0.014293,0.014137
dmcfa,analysis/benchmarks/suite/complex-flow/complex-resume-func,4,3,1,74,5,1.0,1.0,1.0,1.0,0.001398,0.001781,0.001664
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-call,4,3,1,72,4,1.0,1.0,1.0,1.0,0.001213,0.001564,0.001255
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-effect,4,3,1,61,4,1.0,1.0,1.0,1.0,0.001313,0.001073,0.001373
dmcfa,analysis/benchmarks/suite/complex-flow/complex-layers,4,4,1,243,71,1.0,1.0,1.0,1.0,0.01715,0.017285,0.016962
dmcfa,analysis/benchmarks/suite/complex-flow/complex-nested-interleave,4,4,1,144,16,1.0,1.0,1.0,1.0,0.00511,0.005298,0.005052
dmcfa,analysis/benchmarks/suite/complex-flow/complex-non-tail-call,4,4,1,83,4,1.0,1.0,1.0,1.0,0.001721,0.001512,0.001767
dmcfa,analysis/benchmarks/suite/complex-flow/complex-recursive,4,4,1,330,28,1.0,1.0,1.0,1.0,0.015303,0.015683,0.01505
dmcfa,analysis/benchmarks/suite/complex-flow/complex-resume-func,4,4,1,74,5,1.0,1.0,1.0,1.0,0.001484,0.001806,0.001397
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-call,4,4,1,72,4,1.0,1.0,1.0,1.0,0.00123,0.001491,0.001235
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-effect,4,4,1,61,4,1.0,1.0,1.0,1.0,0.001315,0.001095,0.001093
load    : std/core
load    : std/core/undiv
load    : std/core/hnd
load    : std/core/types
load    : std/core/unsafe
load    : std/core/exn
load    : std/core/char
load    : std/core/bool
load    : std/core/order
load    : std/core/vector
load    : std/core/int
load    : std/core/list
load    : std/core/string
load    : std/core/either
load    : std/core/maybe2
load    : std/core/tuple
load    : std/core/maybe
load    : std/core/sslice
load    : std/core/lazy
load    : std/core/console
load    : std/core/debug
load    : std/core/delayed
load    : std/core/show
parse   : .../analysis/benchmarks/suite/complex-flow.kk
check   : analysis/benchmarks/suite/complex-flow
Loading new module std/core/types
load    : std/core/types
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/hnd
load    : std/core/exn
load    : std/core/int
load    : std/core/order
load    : std/core/char
load    : std/core/bool
load    : std/core/maybe
load    : std/core/vector
load    : std/core/list
load    : std/core/maybe2
load    : std/core/tuple
load    : std/core/either
load    : std/core/lazy
load    : std/core/debug
load    : std/core/sslice
load    : std/core/string
load    : std/core/delayed
load    : std/core/console
load    : std/core/show
load    : std/core
load    : std/core/undiv
load    : std/core/unsafe
parse   : .../std/core/types.kk
parse   : .../std/core/undiv.kk
parse   : .../std/core/order.kk
parse   : .../std/core/char.kk
parse   : .../std/core/hnd.kk
parse   : .../std/core/exn.kk
parse   : .../std/core/bool.kk
parse   : .../std/core/unsafe.kk
parse   : .../std/core/int.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/list.kk
parse   : .../std/core/maybe.kk
parse   : .../std/core/maybe2.kk
parse   : .../std/core/either.kk
parse   : .../std/core/tuple.kk
parse   : .../std/core/lazy.kk
parse   : .../std/core/show.kk
parse   : .../std/core/console.kk
parse   : .../std/core/debug.kk
parse   : .../std/core/delayed.kk
parse   : .../std/core.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/string.kk
check   : std/core/types
check   : std/core/int
check   : std/core/bool
check   : std/core/unsafe
check   : std/core/lazy
check   : std/core/undiv
check   : std/core/hnd
check   : std/core/order
check   : std/core/char
check   : std/core/exn
check   : std/core/either
check   : std/core/tuple
check   : std/core/delayed
check   : std/core/maybe
check   : std/core/maybe2
check   : std/core/vector
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/types [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
Loading new module std/core/types
load    : std/core/types
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/bool
load    : std/core/exn
load    : std/core/hnd
load    : std/core/string
load    : std/core/char
load    : std/core/order
load    : std/core/int
load    : std/core/vector
load    : std/core/sslice
load    : std/core/list
load    : std/core/either
load    : std/core/tuple
load    : std/core/maybe2
load    : std/core/show
load    : std/core/debug
load    : std/core/lazy
load    : std/core/console
load    : std/core
load    : std/core/delayed
load    : std/core/maybe
load    : std/core/undiv
load    : std/core/unsafe
parse   : .../std/core/types.kk
parse   : .../std/core/undiv.kk
parse   : .../std/core/hnd.kk
parse   : .../std/core/unsafe.kk
parse   : .../std/core/exn.kk
parse   : .../std/core/int.kk
parse   : .../std/core/bool.kk
parse   : .../std/core/order.kk
parse   : .../std/core/string.kk
parse   : .../std/core/char.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/maybe.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/maybe2.kk
parse   : .../std/core/either.kk
parse   : .../std/core/tuple.kk
parse   : .../std/core/lazy.kk
parse   : .../std/core/list.kk
parse   : .../std/core/show.kk
parse   : .../std/core/console.kk
parse   : .../std/core/debug.kk
parse   : .../std/core/delayed.kk
parse   : .../std/core.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
check   : std/core/types
check   : std/core/int
check   : std/core/unsafe
check   : std/core/bool
check   : std/core/undiv
check   : std/core/lazy
check   : std/core/hnd
check   : std/core/order
check   : std/core/char
check   : std/core/tuple
check   : std/core/either
check   : std/core/exn
check   : std/core/delayed
check   : std/core/vector
check   : std/core/maybe
check   : std/core/maybe2
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/types [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
Loading new module std/core/types
load    : std/core/types
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/hnd
load    : std/core/exn
load    : std/core/bool
load    : std/core/list
load    : std/core/int
load    : std/core/order
load    : std/core/char
load    : std/core/vector
load    : std/core/string
load    : std/core/maybe2
load    : std/core/either
load    : std/core/maybe
load    : std/core/tuple
load    : std/core/show
load    : std/core/lazy
load    : std/core/delayed
load    : std/core/debug
load    : std/core/sslice
load    : std/core
load    : std/core/console
load    : std/core/unsafe
load    : std/core/undiv
parse   : .../std/core/types.kk
parse   : .../std/core/undiv.kk
parse   : .../std/core/unsafe.kk
parse   : .../std/core/hnd.kk
parse   : .../std/core/exn.kk
parse   : .../std/core/order.kk
parse   : .../std/core/bool.kk
parse   : .../std/core/char.kk
parse   : .../std/core/int.kk
parse   : .../std/core/string.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/list.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/maybe.kk
parse   : .../std/core/maybe2.kk
parse   : .../std/core/lazy.kk
parse   : .../std/core/either.kk
parse   : .../std/core/show.kk
parse   : .../std/core/tuple.kk
check   : std/core/types
parse   : .../std/core/console.kk
parse   : .../std/core/debug.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
parse   : .../std/core.kk
parse   : .../std/core/delayed.kk
check   : std/core/int
check   : std/core/lazy
check   : std/core/bool
check   : std/core/unsafe
check   : std/core/undiv
check   : std/core/hnd
check   : std/core/char
check   : std/core/order
check   : std/core/exn
check   : std/core/either
check   : std/core/tuple
check   : std/core/delayed
check   : std/core/maybe2
check   : std/core/vector
check   : std/core/maybe
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/types [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
dmcfa,analysis/benchmarks/suite/complex-flow/complex-layers,0,0,0,180,62,1.011111111111111,1.096774193548387,1.2,1.06993006993007,0.79132,0.805091,0.795153
Loading new module std/core/int
load    : std/core/int
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/string
load    : std/core/order
load    : std/core/bool
load    : std/core/char
load    : std/core/vector
load    : std/core/exn
load    : std/core/hnd
load    : std/core/types
load    : std/core/list
load    : std/core/maybe2
load    : std/core/either
load    : std/core/maybe
load    : std/core/lazy
load    : std/core/show
load    : std/core/debug
load    : std/core/tuple
load    : std/core/console
load    : std/core
load    : std/core/delayed
load    : std/core/sslice
load    : std/core/undiv
load    : std/core/unsafe
parse   : .../std/core/char.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/list.kk
parse   : .../std/core/string.kk
parse   : .../std/core/order.kk
parse   : .../std/core/int.kk
parse   : .../std/core/show.kk
parse   : .../std/core/console.kk
parse   : .../std/core/debug.kk
parse   : .../std/core.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
check   : std/core/int
check   : std/core/char
check   : std/core/order
check   : std/core/vector
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/int [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
Loading new module std/core/int
load    : std/core/int
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/bool
load    : std/core/string
load    : std/core/vector
load    : std/core/char
load    : std/core/order
load    : std/core/exn
load    : std/core/hnd
load    : std/core/types
load    : std/core/list
load    : std/core/sslice
load    : std/core/either
load    : std/core/maybe
load    : std/core/maybe2
load    : std/core/tuple
load    : std/core/show
load    : std/core/lazy
load    : std/core/debug
load    : std/core/console
load    : std/core
load    : std/core/delayed
load    : std/core/undiv
load    : std/core/unsafe
parse   : .../std/core/int.kk
parse   : .../std/core/order.kk
parse   : .../std/core/char.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/list.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/string.kk
parse   : .../std/core/show.kk
parse   : .../std/core/console.kk
parse   : .../std/core/debug.kk
parse   : .../std/core.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
check   : std/core/int
check   : std/core/order
check   : std/core/char
check   : std/core/vector
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/int [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
Loading new module std/core/int
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/int
load    : std/core/hnd
load    : std/core/types
load    : std/core/string
load    : std/core/exn
load    : std/core/char
load    : std/core/bool
load    : std/core/order
load    : std/core/vector
load    : std/core/sslice
load    : std/core/maybe
load    : std/core/list
load    : std/core/tuple
load    : std/core/either
load    : std/core/maybe2
load    : std/core/lazy
load    : std/core/show
load    : std/core/delayed
load    : std/core
load    : std/core/console
load    : std/core/debug
load    : std/core/undiv
load    : std/core/unsafe
parse   : .../std/core/int.kk
parse   : .../std/core/order.kk
parse   : .../std/core/char.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/list.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/string.kk
parse   : .../std/core/show.kk
parse   : .../std/core/console.kk
parse   : .../std/core/debug.kk
parse   : .../std/core.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
check   : std/core/int
check   : std/core/vector
check   : std/core/order
check   : std/core/char
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/int [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
dmcfa,analysis/benchmarks/suite/complex-flow/complex-nested-interleave,0,0,1,128,14,1.0,1.0,1.0,1.009009009009009,0.415054,0.437699,0.44244
Loading new module std/core/int
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/int
load    : std/core/types
load    : std/core/hnd
load    : std/core/string
load    : std/core/order
load    : std/core/vector
load    : std/core/char
load    : std/core/bool
load    : std/core/exn
load    : std/core/maybe
load    : std/core/list
load    : std/core/either
load    : std/core/maybe2
load    : std/core/show
load    : std/core/tuple
load    : std/core/delayed
load    : std/core/lazy
load    : std/core/debug
load    : std/core/console
load    : std/core
load    : std/core/sslice
load    : std/core/unsafe
load    : std/core/undiv
parse   : .../std/core/int.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/order.kk
parse   : .../std/core/char.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/string.kk
parse   : .../std/core/list.kk
parse   : .../std/core/show.kk
parse   : .../std/core/console.kk
parse   : .../std/core/debug.kk
parse   : .../std/core.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
check   : std/core/int
check   : std/core/char
check   : std/core/order
check   : std/core/vector
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/int [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
Loading new module std/core/int
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/int
load    : std/core/types
load    : std/core/hnd
load    : std/core/string
load    : std/core/order
load    : std/core/exn
load    : std/core/bool
load    : std/core/char
load    : std/core/vector
load    : std/core/sslice
load    : std/core/list
load    : std/core/maybe
load    : std/core/maybe2
load    : std/core/lazy
load    : std/core/show
load    : std/core/tuple
load    : std/core/either
load    : std/core/debug
load    : std/core/console
load    : std/core/delayed
load    : std/core
load    : std/core/undiv
load    : std/core/unsafe
parse   : .../std/core/order.kk
parse   : .../std/core/int.kk
parse   : .../std/core/char.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/string.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/show.kk
parse   : .../std/core/console.kk
parse   : .../std/core/debug.kk
parse   : .../std/core/list.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
parse   : .../std/core.kk
check   : std/core/int
check   : std/core/vector
check   : std/core/char
check   : std/core/order
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/int [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
Loading new module std/core/int
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/int
load    : std/core/string
load    : std/core/char
load    : std/core/order
load    : std/core/bool
load    : std/core/vector
load    : std/core/types
load    : std/core/hnd
load    : std/core/exn
load    : std/core/sslice
load    : std/core/list
load    : std/core/maybe2
load    : std/core/maybe
load    : std/core/either
load    : std/core/lazy
load    : std/core/show
load    : std/core/tuple
load    : std/core/debug
load    : std/core/delayed
load    : std/core
load    : std/core/console
load    : std/core/undiv
load    : std/core/unsafe
parse   : .../std/core/order.kk
parse   : .../std/core/int.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/string.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/char.kk
parse   : .../std/core/list.kk
parse   : .../std/core/debug.kk
parse   : .../std/core/console.kk
parse   : .../std/core.kk
parse   : .../std/core/show.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
check   : std/core/int
check   : std/core/vector
check   : std/core/char
check   : std/core/order
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/int [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
dmcfa,analysis/benchmarks/suite/complex-flow/complex-non-tail-call,0,0,0,78,4,1.0,1.0,1.0,1.0606060606060606,0.458195,0.437242,0.441524
Loading new module std/core/int
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/int
load    : std/core/types
load    : std/core/string
load    : std/core/exn
load    : std/core/hnd
load    : std/core/bool
load    : std/core/order
load    : std/core/char
load    : std/core/vector
load    : std/core/maybe
load    : std/core/sslice
load    : std/core/either
load    : std/core/maybe2
load    : std/core/tuple
load    : std/core/show
load    : std/core/debug
load    : std/core/list
load    : std/core/lazy
load    : std/core/delayed
load    : std/core
load    : std/core/console
load    : std/core/unsafe
load    : std/core/undiv
parse   : .../std/core/int.kk
parse   : .../std/core/char.kk
parse   : .../std/core/order.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/string.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/list.kk
parse   : .../std/core/show.kk
parse   : .../std/core.kk
parse   : .../std/core/console.kk
parse   : .../std/core/debug.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
check   : std/core/int
check   : std/core/vector
check   : std/core/order
check   : std/core/char
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/int [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
Loading new module std/core/int
load    : std/core/int
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/hnd
load    : std/core/exn
load    : std/core/types
load    : std/core/order
load    : std/core/bool
load    : std/core/vector
load    : std/core/char
load    : std/core/string
load    : std/core/sslice
load    : std/core/list
load    : std/core/maybe
load    : std/core/tuple
load    : std/core/maybe2
load    : std/core/lazy
load    : std/core/either
load    : std/core/show
load    : std/core/debug
load    : std/core
load    : std/core/console
load    : std/core/delayed
load    : std/core/unsafe
load    : std/core/undiv
parse   : .../std/core/int.kk
parse   : .../std/core/order.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/string.kk
parse   : .../std/core/char.kk
parse   : .../std/core/list.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/debug.kk
parse   : .../std/core/show.kk
parse   : .../std/core/console.kk
parse   : .../std/core.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
check   : std/core/int
check   : std/core/vector
check   : std/core/char
check   : std/core/order
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/int [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
Loading new module std/core/int
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/int
load    : std/core/hnd
load    : std/core/types
load    : std/core/string
load    : std/core/bool
load    : std/core/char
load    : std/core/exn
load    : std/core/vector
load    : std/core/order
load    : std/core/sslice
load    : std/core/list
load    : std/core/maybe2
load    : std/core/either
load    : std/core/maybe
load    : std/core/tuple
load    : std/core/show
load    : std/core/lazy
load    : std/core/debug
load    : std/core/delayed
load    : std/core/console
load    : std/core
load    : std/core/unsafe
load    : std/core/undiv
parse   : .../std/core/char.kk
parse   : .../std/core/int.kk
parse   : .../std/core/string.kk
parse   : .../std/core/order.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/list.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/show.kk
parse   : .../std/core.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
parse   : .../std/core/console.kk
parse   : .../std/core/debug.kk
check   : std/core/int
check   : std/core/order
check   : std/core/char
check   : std/core/vector
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/int [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
dmcfa,analysis/benchmarks/suite/complex-flow/complex-recursive,0,0,0,99,14,1.0909090909090908,1.3571428571428572,2.3333333333333335,1.1645569620253164,0.441364,0.415563,0.446315
Loading new module std/core/int
load    : std/core/int
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/string
load    : std/core/hnd
load    : std/core/bool
load    : std/core/exn
load    : std/core/char
load    : std/core/order
load    : std/core/vector
load    : std/core/types
load    : std/core/list
load    : std/core/sslice
load    : std/core/tuple
load    : std/core/either
load    : std/core/lazy
load    : std/core/debug
load    : std/core/show
load    : std/core/maybe
load    : std/core/maybe2
load    : std/core
load    : std/core/console
load    : std/core/delayed
load    : std/core/unsafe
load    : std/core/undiv
parse   : .../std/core/int.kk
parse   : .../std/core/order.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/char.kk
parse   : .../std/core/string.kk
parse   : .../std/core/list.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/console.kk
parse   : .../std/core.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
parse   : .../std/core/debug.kk
parse   : .../std/core/show.kk
check   : std/core/int
check   : std/core/char
check   : std/core/vector
check   : std/core/order
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/int [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
Loading new module std/core/int
load    : std/core/int
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/hnd
load    : std/core/types
load    : std/core/exn
load    : std/core/string
load    : std/core/order
load    : std/core/bool
load    : std/core/char
load    : std/core/vector
load    : std/core/sslice
load    : std/core/either
load    : std/core/list
load    : std/core/lazy
load    : std/core/debug
load    : std/core/tuple
load    : std/core/show
load    : std/core/delayed
load    : std/core/console
load    : std/core
load    : std/core/maybe
load    : std/core/maybe2
load    : std/core/undiv
load    : std/core/unsafe
parse   : .../std/core/int.kk
parse   : .../std/core/order.kk
parse   : .../std/core/char.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/string.kk
parse   : .../std/core/list.kk
parse   : .../std/core/show.kk
parse   : .../std/core/console.kk
parse   : .../std/core/debug.kk
parse   : .../std/core.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
check   : std/core/int
check   : std/core/order
check   : std/core/vector
check   : std/core/char
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/int [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
Loading new module std/core/int
load    : std/core/int
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/string
load    : std/core/hnd
load    : std/core/types
load    : std/core/bool
load    : std/core/exn
load    : std/core/vector
load    : std/core/order
load    : std/core/char
load    : std/core/sslice
load    : std/core/list
load    : std/core/maybe
load    : std/core/either
load    : std/core/tuple
load    : std/core/maybe2
load    : std/core/debug
load    : std/core/show
load    : std/core/console
load    : std/core
load    : std/core/delayed
load    : std/core/lazy
load    : std/core/unsafe
load    : std/core/undiv
parse   : .../std/core/int.kk
parse   : .../std/core/order.kk
parse   : .../std/core/char.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/list.kk
parse   : .../std/core/string.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/console.kk
parse   : .../std/core/debug.kk
parse   : .../std/core.kk
parse   : .../std/core/show.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
check   : std/core/int
check   : std/core/vector
check   : std/core/order
check   : std/core/char
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/int [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
dmcfa,analysis/benchmarks/suite/complex-flow/complex-resume-func,0,0,1,74,5,1.0,1.0,1.0,1.0,0.409143,0.444165,0.462977
Loading new module std/core/int
load    : std/core/int
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/types
load    : std/core/exn
load    : std/core/hnd
load    : std/core/bool
load    : std/core/string
load    : std/core/char
load    : std/core/vector
load    : std/core/order
load    : std/core/sslice
load    : std/core/maybe
load    : std/core/either
load    : std/core/tuple
load    : std/core/show
load    : std/core/delayed
load    : std/core/debug
load    : std/core/console
load    : std/core/lazy
load    : std/core
load    : std/core/list
load    : std/core/maybe2
load    : std/core/undiv
load    : std/core/unsafe
parse   : .../std/core/order.kk
parse   : .../std/core/int.kk
parse   : .../std/core/char.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/string.kk
parse   : .../std/core/list.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/console.kk
parse   : .../std/core.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
parse   : .../std/core/show.kk
parse   : .../std/core/debug.kk
check   : std/core/int
check   : std/core/vector
check   : std/core/order
check   : std/core/char
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/int [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
Loading new module std/core/int
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/int
load    : std/core/types
load    : std/core/hnd
load    : std/core/bool
load    : std/core/order
load    : std/core/exn
load    : std/core/char
load    : std/core/string
load    : std/core/vector
load    : std/core/list
load    : std/core/sslice
load    : std/core/maybe
load    : std/core/maybe2
load    : std/core/either
load    : std/core/tuple
load    : std/core/lazy
load    : std/core/debug
load    : std/core/show
load    : std/core/delayed
load    : std/core/console
load    : std/core
load    : std/core/undiv
load    : std/core/unsafe
parse   : .../std/core/int.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/order.kk
parse   : .../std/core/string.kk
parse   : .../std/core/char.kk
parse   : .../std/core/list.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/show.kk
parse   : .../std/core/console.kk
parse   : .../std/core/debug.kk
parse   : .../std/core.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
check   : std/core/int
check   : std/core/vector
check   : std/core/char
check   : std/core/order
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/int [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
Loading new module std/core/int
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/int
load    : std/core/hnd
load    : std/core/string
load    : std/core/types
load    : std/core/exn
load    : std/core/bool
load    : std/core/order
load    : std/core/char
load    : std/core/vector
load    : std/core/list
load    : std/core/maybe2
load    : std/core/sslice
load    : std/core/maybe
load    : std/core/show
load    : std/core/debug
load    : std/core/delayed
load    : std/core/lazy
load    : std/core
load    : std/core/console
load    : std/core/tuple
load    : std/core/either
load    : std/core/unsafe
load    : std/core/undiv
parse   : .../std/core/int.kk
parse   : .../std/core/order.kk
parse   : .../std/core/char.kk
parse   : .../std/core/string.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/list.kk
parse   : .../std/core/console.kk
parse   : .../std/core/show.kk
parse   : .../std/core/debug.kk
parse   : .../std/core.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
check   : std/core/int
check   : std/core/order
check   : std/core/char
check   : std/core/vector
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/int [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-call,0,0,1,72,4,1.0,1.0,1.0,1.0,0.45584,0.461525,0.436675
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-effect,0,0,1,61,4,1.0,1.0,1.0,1.0,0.000697,0.0006,0.001319
Loading new module std/core/types
load    : std/core/types
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/hnd
load    : std/core/vector
load    : std/core/bool
load    : std/core/int
load    : std/core/char
load    : std/core/exn
load    : std/core/string
load    : std/core/order
load    : std/core/sslice
load    : std/core/maybe2
load    : std/core/tuple
load    : std/core/either
load    : std/core/lazy
load    : std/core/list
load    : std/core/delayed
load    : std/core/debug
load    : std/core/maybe
load    : std/core
load    : std/core/console
load    : std/core/show
load    : std/core/unsafe
load    : std/core/undiv
parse   : .../std/core/types.kk
parse   : .../std/core/undiv.kk
parse   : .../std/core/unsafe.kk
parse   : .../std/core/hnd.kk
parse   : .../std/core/bool.kk
parse   : .../std/core/int.kk
parse   : .../std/core/order.kk
parse   : .../std/core/exn.kk
parse   : .../std/core/char.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/string.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/list.kk
parse   : .../std/core/maybe2.kk
parse   : .../std/core/maybe.kk
parse   : .../std/core/lazy.kk
parse   : .../std/core/either.kk
parse   : .../std/core/show.kk
parse   : .../std/core/tuple.kk
parse   : .../std/core/debug.kk
parse   : .../std/core/delayed.kk
parse   : .../std/core/console.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
parse   : .../std/core.kk
check   : std/core/types
check   : std/core/int
check   : std/core/lazy
check   : std/core/bool
check   : std/core/undiv
check   : std/core/unsafe
check   : std/core/hnd
check   : std/core/order
check   : std/core/char
check   : std/core/either
check   : std/core/exn
check   : std/core/tuple
check   : std/core/delayed
check   : std/core/maybe2
check   : std/core/maybe
check   : std/core/vector
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/types [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
Loading new module std/core/types
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/types
load    : std/core/int
load    : std/core/hnd
load    : std/core/bool
load    : std/core/char
load    : std/core/string
load    : std/core/order
load    : std/core/exn
load    : std/core/sslice
load    : std/core/vector
load    : std/core/maybe
load    : std/core/maybe2
load    : std/core/lazy
load    : std/core/debug
load    : std/core/show
load    : std/core/either
load    : std/core/tuple
load    : std/core
load    : std/core/console
load    : std/core/delayed
load    : std/core/list
load    : std/core/undiv
load    : std/core/unsafe
parse   : .../std/core/types.kk
parse   : .../std/core/undiv.kk
parse   : .../std/core/int.kk
parse   : .../std/core/order.kk
parse   : .../std/core/char.kk
parse   : .../std/core/exn.kk
parse   : .../std/core/unsafe.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/bool.kk
parse   : .../std/core/hnd.kk
parse   : .../std/core/string.kk
parse   : .../std/core/list.kk
parse   : .../std/core/maybe2.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/maybe.kk
parse   : .../std/core/show.kk
parse   : .../std/core/console.kk
parse   : .../std/core/either.kk
parse   : .../std/core/tuple.kk
parse   : .../std/core/lazy.kk
parse   : .../std/core/debug.kk
parse   : .../std/core/delayed.kk
parse   : .../std/core.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
check   : std/core/types
check   : std/core/int
check   : std/core/bool
check   : std/core/unsafe
check   : std/core/lazy
check   : std/core/undiv
check   : std/core/hnd
check   : std/core/order
check   : std/core/char
check   : std/core/tuple
check   : std/core/delayed
check   : std/core/exn
check   : std/core/either
check   : std/core/maybe
check   : std/core/maybe2
check   : std/core/vector
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/types [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
Loading new module std/core/types
load    : std/core/types
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/hnd
load    : std/core/char
load    : std/core/int
load    : std/core/sslice
load    : std/core/exn
load    : std/core/bool
load    : std/core/string
load    : std/core/order
load    : std/core/maybe
load    : std/core/maybe2
load    : std/core/tuple
load    : std/core/lazy
load    : std/core/show
load    : std/core/debug
load    : std/core/either
load    : std/core/vector
load    : std/core
load    : std/core/delayed
load    : std/core/console
load    : std/core/list
load    : std/core/unsafe
load    : std/core/undiv
parse   : .../std/core/types.kk
parse   : .../std/core/undiv.kk
parse   : .../std/core/unsafe.kk
parse   : .../std/core/hnd.kk
parse   : .../std/core/exn.kk
parse   : .../std/core/order.kk
parse   : .../std/core/char.kk
parse   : .../std/core/bool.kk
parse   : .../std/core/int.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/string.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/list.kk
parse   : .../std/core/maybe.kk
parse   : .../std/core/lazy.kk
parse   : .../std/core/maybe2.kk
parse   : .../std/core/console.kk
parse   : .../std/core/debug.kk
parse   : .../std/core/delayed.kk
parse   : .../std/core/show.kk
parse   : .../std/core/tuple.kk
parse   : .../std/core.kk
parse   : .../std/core/either.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
check   : std/core/types
check   : std/core/undiv
check   : std/core/int
check   : std/core/lazy
check   : std/core/bool
check   : std/core/hnd
check   : std/core/unsafe
check   : std/core/order
check   : std/core/char
check   : std/core/either
check   : std/core/tuple
check   : std/core/exn
check   : std/core/delayed
check   : std/core/maybe2
check   : std/core/vector
check   : std/core/maybe
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/types [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
dmcfa,analysis/benchmarks/suite/complex-flow/complex-layers,0,1,0,231,68,1.0,1.0,1.0,1.0923913043478262,0.831133,0.839479,0.815547
Loading new module std/core/int
load    : std/core/int
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/string
load    : std/core/types
load    : std/core/hnd
load    : std/core/exn
load    : std/core/order
load    : std/core/char
load    : std/core/vector
load    : std/core/sslice
load    : std/core/list
load    : std/core/bool
load    : std/core/maybe
load    : std/core/either
load    : std/core/maybe2
load    : std/core/tuple
load    : std/core/lazy
load    : std/core/show
load    : std/core/debug
load    : std/core/delayed
load    : std/core/console
load    : std/core
load    : std/core/unsafe
load    : std/core/undiv
parse   : .../std/core/order.kk
parse   : .../std/core/int.kk
parse   : .../std/core/char.kk
parse   : .../std/core/string.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/list.kk
parse   : .../std/core/console.kk
parse   : .../std/core/debug.kk
parse   : .../std/core/show.kk
parse   : .../std/core.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
check   : std/core/int
check   : std/core/char
check   : std/core/order
check   : std/core/vector
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/int [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
Loading new module std/core/int
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/int
load    : std/core/types
load    : std/core/hnd
load    : std/core/string
load    : std/core/order
load    : std/core/bool
load    : std/core/exn
load    : std/core/char
load    : std/core/sslice
load    : std/core/vector
load    : std/core/list
load    : std/core/either
load    : std/core/debug
load    : std/core/lazy
load    : std/core/maybe
load    : std/core/console
load    : std/core/delayed
load    : std/core/tuple
load    : std/core
load    : std/core/maybe2
load    : std/core/show
load    : std/core/unsafe
load    : std/core/undiv
parse   : .../std/core/int.kk
parse   : .../std/core/order.kk
parse   : .../std/core/char.kk
parse   : .../std/core/string.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/list.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/show.kk
parse   : .../std/core.kk
parse   : .../std/core/console.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
parse   : .../std/core/debug.kk
check   : std/core/int
check   : std/core/vector
check   : std/core/char
check   : std/core/order
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/int [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
Loading new module std/core/int
load    : std/core/int
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/string
load    : std/core/order
load    : std/core/hnd
load    : std/core/char
load    : std/core/exn
load    : std/core/types
load    : std/core/bool
load    : std/core/vector
load    : std/core/maybe2
load    : std/core/maybe
load    : std/core/sslice
load    : std/core/tuple
load    : std/core/lazy
load    : std/core/either
load    : std/core/debug
load    : std/core/delayed
load    : std/core/show
load    : std/core
load    : std/core/console
load    : std/core/list
load    : std/core/undiv
load    : std/core/unsafe
parse   : .../std/core/int.kk
parse   : .../std/core/order.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/list.kk
parse   : .../std/core/char.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/string.kk
parse   : .../std/core/console.kk
parse   : .../std/core/show.kk
parse   : .../std/core.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
parse   : .../std/core/debug.kk
check   : std/core/int
check   : std/core/order
check   : std/core/char
check   : std/core/vector
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/int [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
dmcfa,analysis/benchmarks/suite/complex-flow/complex-nested-interleave,0,1,1,144,16,1.0,1.0,1.0,1.0,0.445529,0.46476,0.459364
Loading new module std/core/int
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/int
load    : std/core/types
load    : std/core/hnd
load    : std/core/bool
load    : std/core/order
load    : std/core/exn
load    : std/core/char
load    : std/core/string
load    : std/core/vector
load    : std/core/maybe
load    : std/core/maybe2
load    : std/core/sslice
load    : std/core/show
load    : std/core/either
load    : std/core/delayed
load    : std/core/debug
load    : std/core
load    : std/core/console
load    : std/core/lazy
load    : std/core/tuple
load    : std/core/list
load    : std/core/unsafe
load    : std/core/undiv
parse   : .../std/core/int.kk
parse   : .../std/core/order.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/char.kk
parse   : .../std/core/string.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/list.kk
parse   : .../std/core/show.kk
parse   : .../std/core/debug.kk
parse   : .../std/core/console.kk
parse   : .../std/core.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
check   : std/core/int
check   : std/core/order
check   : std/core/vector
check   : std/core/char
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/int [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
Loading new module std/core/int
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/int
load    : std/core/types
load    : std/core/hnd
load    : std/core/string
load    : std/core/exn
load    : std/core/char
load    : std/core/order
load    : std/core/vector
load    : std/core/list
load    : std/core/maybe
load    : std/core/lazy
load    : std/core/show
load    : std/core/debug
load    : std/core/tuple
load    : std/core/maybe2
load    : std/core/delayed
load    : std/core
load    : std/core/console
load    : std/core/bool
load    : std/core/either
load    : std/core/sslice
load    : std/core/unsafe
load    : std/core/undiv
parse   : .../std/core/order.kk
parse   : .../std/core/int.kk
parse   : .../std/core/string.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/list.kk
parse   : .../std/core/char.kk
parse   : .../std/core/show.kk
parse   : .../std/core/debug.kk
parse   : .../std/core.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
parse   : .../std/core/console.kk
check   : std/core/int
check   : std/core/order
check   : std/core/char
check   : std/core/vector
check   : std/core/string
check   : std/core/list
check   : std/core/sslice
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/int [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
Loading new module std/core/int
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/int
load    : std/core/exn
load    : std/core/types
load    : std/core/hnd
load    : std/core/string
load    : std/core/order
load    : std/core/bool
load    : std/core/char
load    : std/core/vector
load    : std/core/sslice
load    : std/core/list
load    : std/core/maybe2
load    : std/core/maybe
load    : std/core/either
load    : std/core/tuple
load    : std/core/lazy
load    : std/core/show
load    : std/core/debug
load    : std/core/delayed
load    : std/core/console
load    : std/core
load    : std/core/undiv
load    : std/core/unsafe
parse   : .../std/core/int.kk
parse   : .../std/core/char.kk
parse   : .../std/core/order.kk
parse   : .../std/core/list.kk
parse   : .../std/core/show.kk
parse   : .../std/core/console.kk
parse   : .../std/core/debug.kk
parse   : .../std/core.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/string.kk
check   : std/core/int
check   : std/core/char
check   : std/core/vector
check   : std/core/order
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/int [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
dmcfa,analysis/benchmarks/suite/complex-flow/complex-non-tail-call,0,1,1,83,4,1.0,1.0,1.0,1.0,0.460483,0.521374,0.445341
Loading new module std/core/int
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/int
load    : std/core/types
load    : std/core/hnd
load    : std/core/bool
load    : std/core/exn
load    : std/core/string
load    : std/core/order
load    : std/core/char
load    : std/core/vector
load    : std/core/list
load    : std/core/sslice
load    : std/core/maybe2
load    : std/core/maybe
load    : std/core/tuple
load    : std/core/either
load    : std/core/lazy
load    : std/core/show
load    : std/core/delayed
load    : std/core
load    : std/core/console
load    : std/core/debug
load    : std/core/undiv
load    : std/core/unsafe
parse   : .../std/core/char.kk
parse   : .../std/core/order.kk
parse   : .../std/core/int.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/string.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/list.kk
parse   : .../std/core/show.kk
parse   : .../std/core/console.kk
parse   : .../std/core.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
parse   : .../std/core/debug.kk
check   : std/core/int
check   : std/core/char
check   : std/core/vector
check   : std/core/order
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/int [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
Loading new module std/core/int
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/int
load    : std/core/types
load    : std/core/hnd
load    : std/core/exn
load    : std/core/bool
load    : std/core/string
load    : std/core/char
load    : std/core/vector
load    : std/core/order
load    : std/core/sslice
load    : std/core/maybe
load    : std/core/either
load    : std/core/tuple
load    : std/core/lazy
load    : std/core/show
load    : std/core/debug
load    : std/core/delayed
load    : std/core/console
load    : std/core
load    : std/core/maybe2
load    : std/core/list
load    : std/core/undiv
load    : std/core/unsafe
parse   : .../std/core/int.kk
parse   : .../std/core/order.kk
parse   : .../std/core/char.kk
parse   : .../std/core/string.kk
parse   : .../std/core/list.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/console.kk
parse   : .../std/core/debug.kk
parse   : .../std/core.kk
parse   : .../std/core/show.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
check   : std/core/int
check   : std/core/order
check   : std/core/char
check   : std/core/vector
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/int [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
Loading new module std/core/int
load    : std/core/int
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/string
load    : std/core/order
load    : std/core/exn
load    : std/core/bool
load    : std/core/hnd
load    : std/core/types
load    : std/core/char
load    : std/core/vector
load    : std/core/maybe
load    : std/core/tuple
load    : std/core/either
load    : std/core/debug
load    : std/core/show
load    : std/core/maybe2
load    : std/core/lazy
load    : std/core/delayed
load    : std/core/sslice
load    : std/core
load    : std/core/console
load    : std/core/list
load    : std/core/undiv
load    : std/core/unsafe
parse   : .../std/core/int.kk
parse   : .../std/core/order.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/string.kk
parse   : .../std/core/char.kk
parse   : .../std/core/list.kk
parse   : .../std/core/show.kk
parse   : .../std/core/console.kk
parse   : .../std/core/debug.kk
parse   : .../std/core.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
check   : std/core/int
check   : std/core/order
check   : std/core/char
check   : std/core/vector
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/int [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
dmcfa,analysis/benchmarks/suite/complex-flow/complex-recursive,0,1,0,160,23,1.13125,2.217391304347826,2.7142857142857144,1.1517857142857142,0.458299,0.474156,0.426035
Loading new module std/core/int
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/int
load    : std/core/hnd
load    : std/core/types
load    : std/core/string
load    : std/core/exn
load    : std/core/vector
load    : std/core/bool
load    : std/core/char
load    : std/core/order
load    : std/core/maybe
load    : std/core/sslice
load    : std/core/list
load    : std/core/maybe2
load    : std/core/either
load    : std/core/tuple
load    : std/core/show
load    : std/core/lazy
load    : std/core/debug
load    : std/core/delayed
load    : std/core/console
load    : std/core
load    : std/core/unsafe
load    : std/core/undiv
parse   : .../std/core/int.kk
parse   : .../std/core/order.kk
parse   : .../std/core/char.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/string.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/list.kk
parse   : .../std/core/show.kk
parse   : .../std/core/console.kk
parse   : .../std/core.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
parse   : .../std/core/debug.kk
check   : std/core/int
check   : std/core/vector
check   : std/core/char
check   : std/core/order
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/int [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
Loading new module std/core/int
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/int
load    : std/core/hnd
load    : std/core/string
load    : std/core/types
load    : std/core/exn
load    : std/core/bool
load    : std/core/vector
load    : std/core/char
load    : std/core/order
load    : std/core/list
load    : std/core/maybe
load    : std/core/sslice
load    : std/core/maybe2
load    : std/core/tuple
load    : std/core/either
load    : std/core/lazy
load    : std/core/debug
load    : std/core/show
load    : std/core/delayed
load    : std/core/console
load    : std/core
load    : std/core/unsafe
load    : std/core/undiv
parse   : .../std/core/int.kk
parse   : .../std/core/order.kk
parse   : .../std/core/char.kk
parse   : .../std/core/string.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/list.kk
parse   : .../std/core/show.kk
parse   : .../std/core/console.kk
parse   : .../std/core/debug.kk
parse   : .../std/core.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
check   : std/core/int
check   : std/core/vector
check   : std/core/char
check   : std/core/order
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/int [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
Loading new module std/core/int
load    : std/core/int
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/hnd
load    : std/core/exn
load    : std/core/string
load    : std/core/types
load    : std/core/order
load    : std/core/char
load    : std/core/vector
load    : std/core/bool
load    : std/core/list
load    : std/core/sslice
load    : std/core/maybe
load    : std/core/maybe2
load    : std/core/tuple
load    : std/core/lazy
load    : std/core/debug
load    : std/core/show
load    : std/core
load    : std/core/delayed
load    : std/core/either
load    : std/core/console
load    : std/core/undiv
load    : std/core/unsafe
parse   : .../std/core/order.kk
parse   : .../std/core/int.kk
parse   : .../std/core/char.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/list.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/string.kk
parse   : .../std/core/show.kk
parse   : .../std/core/debug.kk
parse   : .../std/core/console.kk
parse   : .../std/core.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
check   : std/core/int
check   : std/core/order
check   : std/core/vector
check   : std/core/char
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/int [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
dmcfa,analysis/benchmarks/suite/complex-flow/complex-resume-func,0,1,1,74,5,1.0,1.0,1.0,1.0,0.468935,0.429593,0.446851
Loading new module std/core/int
load    : std/core/int
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/hnd
load    : std/core/exn
load    : std/core/string
load    : std/core/order
load    : std/core/vector
load    : std/core/list
load    : std/core/maybe2
load    : std/core/either
load    : std/core/bool
load    : std/core/lazy
load    : std/core/maybe
load    : std/core/char
load    : std/core/sslice
load    : std/core/show
load    : std/core
load    : std/core/delayed
load    : std/core/console
load    : std/core/debug
load    : std/core/tuple
load    : std/core/types
load    : std/core/undiv
load    : std/core/unsafe
parse   : .../std/core/order.kk
parse   : .../std/core/int.kk
parse   : .../std/core/string.kk
parse   : .../std/core/char.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/list.kk
parse   : .../std/core/show.kk
parse   : .../std/core/console.kk
parse   : .../std/core/debug.kk
parse   : .../std/core.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
check   : std/core/int
check   : std/core/vector
check   : std/core/order
check   : std/core/char
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/int [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
Loading new module std/core/int
load    : std/core/int
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/string
load    : std/core/types
load    : std/core/hnd
load    : std/core/bool
load    : std/core/exn
load    : std/core/order
load    : std/core/vector
load    : std/core/char
load    : std/core/maybe2
load    : std/core/sslice
load    : std/core/list
load    : std/core/maybe
load    : std/core/either
load    : std/core/tuple
load    : std/core/lazy
load    : std/core/show
load    : std/core/delayed
load    : std/core/console
load    : std/core/debug
load    : std/core
load    : std/core/unsafe
load    : std/core/undiv
parse   : .../std/core/order.kk
parse   : .../std/core/int.kk
parse   : .../std/core/char.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/list.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/string.kk
parse   : .../std/core/show.kk
parse   : .../std/core/console.kk
parse   : .../std/core/debug.kk
parse   : .../std/core.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
check   : std/core/int
check   : std/core/char
check   : std/core/order
check   : std/core/vector
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/int [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
Loading new module std/core/int
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/int
load    : std/core/hnd
load    : std/core/types
load    : std/core/string
load    : std/core/order
load    : std/core/bool
load    : std/core/exn
load    : std/core/vector
load    : std/core/char
load    : std/core/list
load    : std/core/maybe2
load    : std/core/tuple
load    : std/core/maybe
load    : std/core/either
load    : std/core/show
load    : std/core/debug
load    : std/core/sslice
load    : std/core/delayed
load    : std/core
load    : std/core/console
load    : std/core/lazy
load    : std/core/undiv
load    : std/core/unsafe
parse   : .../std/core/int.kk
parse   : .../std/core/order.kk
parse   : .../std/core/char.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/string.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/show.kk
parse   : .../std/core/list.kk
parse   : .../std/core/debug.kk
parse   : .../std/core.kk
parse   : .../std/core/console.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
check   : std/core/int
check   : std/core/vector
check   : std/core/order
check   : std/core/char
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/int [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-call,0,1,1,72,4,1.0,1.0,1.0,1.0,0.442473,0.468189,0.423168
dmcfa,analysis/benchmarks/suite/complex-flow/complex-tail-effect,0,1,1,61,4,1.0,1.0,1.0,1.0,0.000894,0.000783,0.00132
Loading new module std/core/types
load    : std/core/types
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/exn
load    : std/core/hnd
load    : std/core/bool
load    : std/core/int
load    : std/core/char
load    : std/core/order
load    : std/core/string
load    : std/core/vector
load    : std/core/sslice
load    : std/core/list
load    : std/core/maybe
load    : std/core/maybe2
load    : std/core/show
load    : std/core/debug
load    : std/core/tuple
load    : std/core/lazy
load    : std/core
load    : std/core/either
load    : std/core/delayed
load    : std/core/console
load    : std/core/unsafe
load    : std/core/undiv
parse   : .../std/core/types.kk
parse   : .../std/core/exn.kk
parse   : .../std/core/undiv.kk
parse   : .../std/core/unsafe.kk
parse   : .../std/core/hnd.kk
parse   : .../std/core/bool.kk
parse   : .../std/core/int.kk
parse   : .../std/core/maybe.kk
parse   : .../std/core/order.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/maybe2.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/tuple.kk
parse   : .../std/core/char.kk
parse   : .../std/core/lazy.kk
parse   : .../std/core/show.kk
parse   : .../std/core/console.kk
parse   : .../std/core/debug.kk
parse   : .../std/core/list.kk
parse   : .../std/core/either.kk
parse   : .../std/core.kk
parse   : .../std/core/string.kk
parse   : .../std/core/delayed.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
check   : std/core/types
check   : std/core/lazy
check   : std/core/undiv
check   : std/core/unsafe
check   : std/core/bool
check   : std/core/int
check   : std/core/hnd
check   : std/core/char
check   : std/core/order
check   : std/core/exn
check   : std/core/either
check   : std/core/delayed
check   : std/core/tuple
check   : std/core/maybe
check   : std/core/maybe2
check   : std/core/vector
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/types [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
Loading new module std/core/types
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/hnd
load    : std/core/sslice
load    : std/core/order
load    : std/core/exn
load    : std/core/vector
load    : std/core/string
load    : std/core/list
load    : std/core/maybe2
load    : std/core/maybe
load    : std/core/either
load    : std/core/debug
load    : std/core/show
load    : std/core/tuple
load    : std/core
load    : std/core/console
load    : std/core/delayed
load    : std/core/unsafe
load    : std/core/undiv
load    : std/core/char
load    : std/core/bool
load    : std/core/int
load    : std/core/lazy
parse   : .../std/core/undiv.kk
parse   : .../std/core/types.kk
parse   : .../std/core/unsafe.kk
parse   : .../std/core/order.kk
parse   : .../std/core/hnd.kk
parse   : .../std/core/exn.kk
parse   : .../std/core/bool.kk
parse   : .../std/core/int.kk
parse   : .../std/core/char.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/list.kk
parse   : .../std/core/maybe.kk
parse   : .../std/core/string.kk
parse   : .../std/core/either.kk
parse   : .../std/core/tuple.kk
parse   : .../std/core/lazy.kk
parse   : .../std/core/show.kk
parse   : .../std/core/console.kk
parse   : .../std/core/debug.kk
parse   : .../std/core/delayed.kk
parse   : .../std/core.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
parse   : .../std/core/maybe2.kk
check   : std/core/types
check   : std/core/undiv
check   : std/core/bool
check   : std/core/unsafe
check   : std/core/lazy
check   : std/core/int
check   : std/core/hnd
check   : std/core/char
check   : std/core/order
check   : std/core/exn
check   : std/core/either
check   : std/core/delayed
check   : std/core/tuple
check   : std/core/vector
check   : std/core/maybe2
check   : std/core/maybe
check   : std/core/string
check   : std/core/sslice
check   : std/core/list
check   : std/core/show
check   : std/core/console
check   : std/core/debug
check   : std/core
check   : analysis/benchmarks/suite/complex-flow

Loaded module std/core/types [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/suite/complex-flow]
Loading new module std/core/types
load    : std/core/types
load    : analysis/benchmarks/suite/complex-flow
load    : std/core/order
load    : std/core/exn
load    : std/core/bool
load    : std/core/int
load    : std/core/maybe
load    : std/core/char
load    : std/core/list
load    : std/core/maybe2
load    : std/core/debug
load    : std/core/lazy
load    : std/core/show
load    : std/core/console
load    : std/core/delayed
load    : std/core
load    : std/core/either
load    : std/core/string
load    : std/core/vector
load    : std/core/unsafe
load    : std/core/undiv
parse   : .../std/core/types.kk
parse   : .../std/core/undiv.kk
parse   : .../std/core/unsafe.kk
parse   : .../std/core/hnd.kk
parse   : .../std/core/exn.kk
parse   : .../std/core/bool.kk
parse   : .../std/core/int.kk
parse   : .../std/core/order.kk
parse   : .../std/core/char.kk
parse   : .../std/core/string.kk
parse   : .../std/core/sslice.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/list.kk
parse   : .../std/core/maybe2.kk
parse   : .../std/core/maybe.kk
parse   : .../std/core/either.kk
parse   : .../std/core/tuple.kk
check   : std/core/types
parse   : .../std/core/lazy.kk
parse   : .../std/core/console.kk
parse   : .../std/core/debug.kk
parse   : .../std/core/show.kk
parse   : .../std/core/delayed.kk
parse   : .../std/core.kk
parse   : .../analysis/benchmarks/suite/complex-flow.kk
check   : std/core/lazy
check   : std/core/int
check   : std/core/bool
check   : std/core/unsafe
check   : std/core/undiv
check   : std/core/hnd
check   : std/core/order
check   : std/core/char
user interrupt
