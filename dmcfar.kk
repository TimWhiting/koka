koka-3.2.2: unregistering (local file changes: src/Core/FlowAnalysis/Full/DMCFAR/AbstractValue.hs src/Core/FlowAnalysis/Full/DMCFAR/DMCFA.hs)
koka> build (lib + exe) with ghc-9.6.6
Preprocessing library for koka-3.2.2..
Building library for koka-3.2.2..
[ 96 of 143] Compiling Core.FlowAnalysis.Full.DMCFAR.AbstractValue [Source file changed]
[ 97 of 143] Compiling Core.FlowAnalysis.Full.DMCFAR.Monad [Core.FlowAnalysis.Full.DMCFAR.AbstractValue changed]
[124 of 143] Compiling Core.FlowAnalysis.Full.DMCFAR.Primitives [Core.FlowAnalysis.Full.DMCFAR.AbstractValue changed]
[125 of 143] Compiling Core.FlowAnalysis.Full.DMCFAR.DMCFA [Source file changed]
[126 of 143] Compiling Core.FlowAnalysis.Full.DMCFAR.Syntax [Core.FlowAnalysis.Full.DMCFAR.AbstractValue changed]
[140 of 143] Compiling Compile.Build [Core.FlowAnalysis.Full.DMCFAR.Syntax changed]
[141 of 143] Compiling Compile.BuildContext [Compile.Build changed]
[142 of 143] Compiling Interpreter.Interpret [Compile.BuildContext changed]
[143 of 143] Compiling Main.Run [Compile.BuildContext changed]
Warning: The following header files listed in the main library's c-sources
will not be used: src/Platform/cpp/Platform/cconsole.h.
Header files should be in the 'include' or 'install-include' stanza.
See https://cabal.readthedocs.io/en/3.10/cabal-package.html#pkg-field-includes
Preprocessing executable 'koka' for koka-3.2.2..
Building executable 'koka' for koka-3.2.2..
[ 3 of 17] Compiling LanguageServer.Monad [Compile.BuildContext changed]
[ 4 of 17] Compiling LanguageServer.Handler.TextDocument [Compile.Build changed]
[ 5 of 17] Compiling LanguageServer.Handler.SignatureHelp [Compile.BuildContext changed]
[ 6 of 17] Compiling LanguageServer.Handler.Hover [Compile.BuildContext changed]
[ 7 of 17] Compiling LanguageServer.Handler.InlayHints [LanguageServer.Handler.Hover changed]
[ 8 of 17] Compiling LanguageServer.Handler.Folding [LanguageServer.Monad changed]
[ 9 of 17] Compiling LanguageServer.Handler.DocumentSymbol [LanguageServer.Monad changed]
[10 of 17] Compiling LanguageServer.Handler.Definition [LanguageServer.Monad changed]
[11 of 17] Compiling LanguageServer.Handler.Completion [Compile.BuildContext changed]
[12 of 17] Compiling LanguageServer.Handler.Commands [LanguageServer.Handler.TextDocument changed]
[13 of 17] Compiling LanguageServer.Handler.CodeAction [LanguageServer.Monad changed]
[14 of 17] Compiling LanguageServer.Handlers [LanguageServer.Handler.CodeAction changed]
[15 of 17] Compiling LanguageServer.Run [LanguageServer.Handlers changed]
[16 of 17] Compiling Main [Main.Run changed]
[18 of 18] Linking .stack-work/dist/x86_64-linux/ghc-9.6.6/build/koka/koka [Objects changed]
koka> copy/register
Installing library in /home/tim/koka/.stack-work/install/x86_64-linux/b0990f9ce7f176afb926501e29e9595b91936665080ae0b1590539787cff559a/9.6.6/lib/x86_64-linux-ghc-9.6.6/koka-3.2.2-8GBEfjISoFBMgz1sr3wgW
Installing executable koka in /home/tim/koka/.stack-work/install/x86_64-linux/b0990f9ce7f176afb926501e29e9595b91936665080ae0b1590539787cff559a/9.6.6/bin
Registering library for koka-3.2.2..
d=2,m=6
Result 34 / 34
Result 100.0%, time: 3.692903728s
d=2,m=5
Result 34 / 34
Result 100.0%, time: 3.240831893s
d=2,m=4
Result 34 / 34
Result 100.0%, time: 2.854819524s
d=2,m=3
Result 34 / 34
Result 100.0%, time: 1.087407716s
d=2,m=2
Result 34 / 34
Result 100.0%, time: 0.58850684s
d=2,m=1
Result 27 / 34
Result 79.41%, time: 7.480572508s
Failed to compile analysis/aac/benchmarks.kk
