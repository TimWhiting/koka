koka-3.2.3: unregistering (local file changes: src/Core/FlowAnalysis/Full/DMCFAR/DMCFA.hs)
koka> build (lib + exe) with ghc-9.6.6
Preprocessing library for koka-3.2.3..
Building library for koka-3.2.3..
[123 of 141] Compiling Core.FlowAnalysis.Full.DMCFAR.DMCFA [Source file changed]
[124 of 141] Compiling Core.FlowAnalysis.Full.DMCFAR.Syntax [Core.FlowAnalysis.Full.DMCFAR.DMCFA changed]
[138 of 141] Compiling Compile.Build [Core.FlowAnalysis.Full.DMCFAR.Syntax changed]
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
parse   : .../std/core/unsafe.kk
parse   : .../std/core/hnd.kk
parse   : .../std/core/order.kk
parse   : .../std/core/exn.kk
parse   : .../std/core/int.kk
parse   : .../std/core/bool.kk
parse   : .../std/core/char.kk
parse   : .../std/core/vector.kk
parse   : .../std/core/string.kk
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
parse   : .../analysis/benchmarks/koka-gen/coop-communication.kk
parse   : .../std/core.kk
check   : std/core/types
check   : std/core/bool
check   : std/core/int
check   : std/core/unsafe
check   : std/core/undiv
check   : std/core/lazy
check   : std/core/hnd
check   : std/core/char
check   : std/core/order
check   : std/core/delayed
check   : std/core/either
check   : std/core/exn
check   : std/core/tuple
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
check   : analysis/benchmarks/koka-gen/coop-communication
dmcfa,analysis/benchmarks/koka-gen/coop-communication/spawn,100,100,1,993,993,993,292,292,292,165,165,165,904,906,902,0.24043,0.239234,0.224454
linking : analysis/benchmarks/koka-gen/coop-communication/@main
compile : kklib from: /Users/timwhiting/koka/kklib
created : .koka/v3.2.3/clang-debug-1e5359/analysis_benchmarks_koka_dash_gen_coop_dash_communication__main
