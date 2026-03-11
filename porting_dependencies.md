# Porting Dependencies

This document outlines the dependency-ordered list of the remaining 108 Koka compiler modules to be ported from Haskell to Lean 4. 

Modules within the same group do not depend on each other (with respect to unported modules) and can be ported **simultaneously**. You must complete or mock the dependencies of a lower group before proceeding to higher groups.

## Group 1 (Ready to Port)
- `Common.NamePrim`
- `Common.QNameMap`
- `Common.Range`
- `Common.ResumeKind`
- `Interpreter.Command`
- `Lib.Scc`
- `Platform.Config`
- `Platform.GetOptions`
- `Platform.Runtime`
- `Platform.Var`

## Group 2
- `Common.Message`
- `Kind.Kind`
- `Lib.JSON`
- `Lib.Trace`
- `Platform.Console`
- `Platform.Filetime`
- `Syntax.Lexeme`

## Group 3
- `Common.Error`
- `Compile.Package`
- `Kind.ImportMap`
- `Kind.Pretty`
- `Syntax.Layout`
- `Syntax.Syntax`
- `Type.Type`

## Group 4
- `Kind.InferKind`
- `Kind.Repr`
- `Static.BindingGroups`
- `Static.FixityResolve`
- `Syntax.Highlight`
- `Syntax.Promote`
- `Type.Kind`

## Group 5
- `Platform.ReadLine`
- `Type.TypeVar`

## Group 6
- `Type.Pretty`

## Group 7
- `Core.Core`
- `Syntax.RangeMap`

## Group 8
- `Core.Borrowed`
- `Kind.Assumption`
- `Kind.Constructors`
- `Kind.Newtypes`
- `Kind.Synonym`
- `LanguageServer.Conversions`

## Group 9
- `Core.Pretty`
- `Kind.InferMonad`

## Group 10
- `Backend.C.ParcReuseSpec`
- `Core.AnalysisCCtx`
- `Core.CoreVar`
- `Kind.Unify`
- `Syntax.Pretty`

## Group 11
- `Backend.C.Parc`
- `Backend.C.ParcReuse`
- `Backend.JavaScript.FromCore`
- `Compile.Options`
- `Core.AnalysisResume`
- `Core.BindingGroups`
- `Core.Inlines`
- `Core.UnReturn`
- `Core.Uniquefy`
- `Syntax.Parse`
- `Type.Assumption`

## Group 12
- `Backend.CSharp.FromCore`
- `Compile.Module`
- `Core.CTail`
- `Core.CheckFBIP`
- `Core.Divergent`
- `Core.FunLift`
- `Core.MonadicLift`
- `Core.Parse`
- `Core.Simplify`
- `Core.Unroll`
- `Kind.Infer`
- `Syntax.Colorize`
- `Type.InfGamma`
- `Type.Operations`

## Group 13
- `Backend.C.Box`
- `Core.Inline`
- `Core.Monadic`
- `Core.Specialize`
- `LanguageServer.Handler.Pretty`
- `Syntax.GenDoc`
- `Type.Unify`

## Group 14
- `Backend.C.FromCore`
- `Core.AnalysisMatch`
- `Core.Check`
- `Core.OpenResolve`
- `Type.InferMonad`

## Group 15
- `Compile.Optimize`
- `Type.Infer`

## Group 16
- `Compile.TypeCheck`

## Group 17
- `Compile.CodeGen`

## Group 18
- `Compile.Build`

## Group 19
- `Compile.BuildContext`

## Group 20
- `Interpreter.Interpret`
- `LanguageServer.Monad`

## Group 21
- `LanguageServer.Handler.CodeAction`
- `LanguageServer.Handler.Definition`
- `LanguageServer.Handler.DocumentSymbol`
- `LanguageServer.Handler.Folding`
- `LanguageServer.Handler.Hover`
- `LanguageServer.Handler.SignatureHelp`
- `LanguageServer.Handler.TextDocument`
- `Main.Run`

## Group 22
- `LanguageServer.Handler.Commands`
- `LanguageServer.Handler.Completion`
- `LanguageServer.Handler.InlayHints`

## Group 23
- `LanguageServer.Handlers`

## Group 24
- `LanguageServer.Run`

## Group 25
- `Main`
