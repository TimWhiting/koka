koka-3.2.2: unregistering (local file changes: src/Core/FlowAnalysis/Full/DMCFA/DMCFA.hs)
koka> build (lib + exe) with ghc-9.6.6
Preprocessing library for koka-3.2.2..
Building library for koka-3.2.2..
[128 of 143] Compiling Core.FlowAnalysis.Full.DMCFA.DMCFA [Source file changed]
Warning: The following header files listed in the main library's c-sources
will not be used: src/Platform/cpp/Platform/cconsole.h.
Header files should be in the 'include' or 'install-include' stanza.
See https://cabal.readthedocs.io/en/3.10/cabal-package.html#pkg-field-includes
Preprocessing executable 'koka' for koka-3.2.2..
Building executable 'koka' for koka-3.2.2..
[18 of 18] Linking .stack-work/dist/x86_64-linux/ghc-9.6.6/build/koka/koka [Library changed]
koka> copy/register
Installing library in /home/tim/koka/.stack-work/install/x86_64-linux/caa2c2a0c9eec164a22324b7d83105503be009c866f84849897f47c50a8aa47d/9.6.6/lib/x86_64-linux-ghc-9.6.6/koka-3.2.2-8GBEfjISoFBMgz1sr3wgW
Installing executable koka in /home/tim/koka/.stack-work/install/x86_64-linux/caa2c2a0c9eec164a22324b7d83105503be009c866f84849897f47c50a8aa47d/9.6.6/bin
Registering library for koka-3.2.2..
 Analyzing "ex1"
result: ( lit: 1,⊥,⊥,⊥,fromList [])
expected: ( lit: 1,⊥,⊥,⊥,fromList [])
 Analyzing "ex10"
result: ( lit: 1,⊥,⊥,⊥,fromList [])
expected: ( lit: 1,⊥,⊥,⊥,fromList [])
 Analyzing "ex11"
result: ( lit: 2,⊥,⊥,⊥,fromList [])
expected: ( lit: 2,⊥,⊥,⊥,fromList [])
 Analyzing "ex12"
result: ( lit: ⊤,⊥,⊥,⊥,fromList [])
expected: ( lit: 2,⊥,⊥,⊥,fromList [])
 Analyzing "ex13"
result: ( lit: ⊤,⊥,⊥,⊥,fromList [])
expected: ( lit: 3,⊥,⊥,⊥,fromList [])
 Analyzing "ex2"
result: ( lit: ⊤,⊥,⊥,⊥,fromList [])
expected: ( lit: 3,⊥,⊥,⊥,fromList [])
 Analyzing "ex201"
result: ( lit: ⊤,⊥,⊥,⊥,fromList [])
expected: ( lit: 7,⊥,⊥,⊥,fromList [])
 Analyzing "ex21"
result: ( lit: ⊤,⊥,⊥,⊥,fromList [])
expected: ( lit: 5,⊥,⊥,⊥,fromList [])
 Analyzing "ex22"
result: ( lit: ⊤,⊥,⊥,⊥,fromList [])
expected: ( lit: 12,⊥,⊥,⊥,fromList [])
 Analyzing "ex23"
result: ( lit: ⊤,⊥,⊥,⊥,fromList [])
expected: ( lit: 28,⊥,⊥,⊥,fromList [])
d=10,m=10
Result 3 / 10
Result 30.0%, time: 0.313852311s
