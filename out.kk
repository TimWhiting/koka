koka-3.2.3: unregistering (local file changes: src/Core/FlowAnalysis/Full/DMCFA/Primitives.hs src/Core/FlowAnalysis/Full/DMCFAR/Primitives.hs sr...)
koka> build (lib + exe) with ghc-9.6.6
Preprocessing library for koka-3.2.3..
Building library for koka-3.2.3..
[ 63 of 141] Compiling Core.FlowAnalysis.Full.PrimComm [Source file changed]
[119 of 141] Compiling Core.FlowAnalysis.Full.KCFA.Primitives [Source file changed]
[120 of 141] Compiling Core.FlowAnalysis.Full.KCFA.KCFA [Core.FlowAnalysis.Full.PrimComm changed]
[122 of 141] Compiling Core.FlowAnalysis.Full.DMCFAR.Primitives [Source file changed]
[123 of 141] Compiling Core.FlowAnalysis.Full.DMCFAR.DMCFA [Core.FlowAnalysis.Full.PrimComm changed]
[125 of 141] Compiling Core.FlowAnalysis.Full.DMCFA.Primitives [Source file changed]
[126 of 141] Compiling Core.FlowAnalysis.Full.DMCFA.DMCFA [Core.FlowAnalysis.Full.PrimComm changed]
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
dmcfae,analysis/benchmarks/handlers/scoped/example1,4,4,timeout,0,0,0,0,0,0,0,timeout,timeout,timeout
dmcfae,analysis/benchmarks/handlers/scoped/example2,4,4,timeout,0,0,0,0,0,0,0,timeout,timeout,timeout
dmcfae,analysis/benchmarks/handlers/scoped/example3,4,4,timeout,0,0,0,0,0,0,0,timeout,timeout,timeout
dmcfae,analysis/benchmarks/handlers/scoped/example4,4,4,1,431,64,1.0,1.0,1.0,1.0,0.023782,0.024918,0.024196
External variable binding not found std/core/vector/@extern-unvlist
Variable not found: std/core/vector/@extern-unvlist
External variable binding not found std/core/vector/@extern-unvlist
Variable not found: std/core/vector/@extern-unvlist
Loaded module std/num/random [std/core/types,std/core/undiv,std/core/unsafe,std/core/hnd,std/core/exn,std/core/bool,std/core/int,std/core/order,std/core/char,std/core/vector,std/core/string,std/core/sslice,std/core/list,std/core/maybe,std/core/maybe2,std/core/either,std/core/tuple,std/core/lazy,std/core/show,std/core/console,std/core/debug,std/core/delayed,std/core,analysis/benchmarks/handlers/scoped]
Failed to compile analysis/benchmarks/handlers/scoped.kk
