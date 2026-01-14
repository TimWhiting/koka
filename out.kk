koka-3.2.3: unregistering (local file changes: src/Core/FlowAnalysis/Full/DMCFAR/DMCFA.hs)
koka> configure (lib + exe)
Configuring koka-3.2.3...
koka> build (lib + exe) with ghc-9.6.6
Preprocessing library for koka-3.2.3..
Building library for koka-3.2.3..
[123 of 141] Compiling Core.FlowAnalysis.Full.DMCFAR.DMCFA [Source file changed]
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
dmcfa,analysis/benchmarks/suite/basic/basic-exception,4,4,1,56,1,1.0,1.0,1.0,1.0,0.001533,0.001194,0.001699
dmcfa,analysis/benchmarks/suite/basic/basic-resume,4,4,1,69,4,1.0,1.0,1.0,1.0,0.001425,0.001224,0.001621
dmcfa,analysis/benchmarks/suite/basic/basic-resume-context,4,4,1,78,5,1.0,1.0,1.0,1.0,0.001814,0.001448,0.001684
dmcfa,analysis/benchmarks/suite/basic/basic-resume-op,4,4,1,78,4,1.0,1.0,1.0,1.0,0.001651,0.001378,0.001683
dmcfa,analysis/benchmarks/suite/basic/basic-resume-op-context,4,4,1,87,5,1.0,1.0,1.0,1.0,0.001789,0.002139,0.001659
