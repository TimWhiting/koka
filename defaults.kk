[6ncompile: samples/handlers/typeclass_show_generic.kk
loading: std/core
loading: std/core/types
loading: std/core/hnd
check  : samples/handlers/typeclass/show/generic

infer single .select-eshow
Def {defBinder = ValueBinder {binderName = .select-eshow, binderType = (), binderExpr = Ann (Lam [ValueBinder {binderName = hnd, binderType = Nothing, binderExpr = Nothing, binderNameRange = (1, 0), binderRange = (1, 0)}] (Case (Var hnd False (1, 0)) [Branch {branchPattern = PatCon .Hnd-effshow [(Nothing,PatVar (ValueBinder {binderName = fun-eshow, binderType = Nothing, binderExpr = PatWild (1, 0), binderNameRange = (1, 0), binderRange = (1, 0)}))] (1, 0) (1, 0), branchGuards = [Guard {guardTest = Var std/core/types/True False (1, 0), guardExpr = Var fun-eshow False (1, 0)}]}] (1, 0)) (1, 0)) (TForall [TypeVar {typevarId = 32, typevarKind = KCon V, typevarFlavour = Bound},TypeVar {typevarId = 33, typevarKind = KCon E, typevarFlavour = Bound},TypeVar {typevarId = 34, typevarKind = KCon V, typevarFlavour = Bound}] [] (TFun [(hnd,TApp (TCon (TypeCon {typeconName = samples/handlers/typeclass/show/generic/.hnd-effshow, typeconKind = KApp (KApp (KCon (->)) (KCon V)) (KApp (KApp (KCon (->)) (KCon E)) (KApp (KApp (KCon (->)) (KCon V)) (KCon V)))})) [TVar (TypeVar {typevarId = 32, typevarKind = KCon V, typevarFlavour = Bound}),TVar (TypeVar {typevarId = 33, typevarKind = KCon E, typevarFlavour = Bound}),TVar (TypeVar {typevarId = 34, typevarKind = KCon V, typevarFlavour = Bound})])] (TCon (TypeCon {typeconName = std/core/types/(<>), typeconKind = KCon E})) (TApp (TCon (TypeCon {typeconName = std/core/hnd/clause1, typeconKind = KApp (KApp (KCon (->)) (KCon V)) (KApp (KApp (KCon (->)) (KCon V)) (KApp (KApp (KCon (->)) (KApp (KApp (KCon (->)) (KCon E)) (KApp (KApp (KCon (->)) (KCon V)) (KCon V)))) (KApp (KApp (KCon (->)) (KCon E)) (KApp (KApp (KCon (->)) (KCon V)) (KCon V)))))})) [TVar (TypeVar {typevarId = 32, typevarKind = KCon V, typevarFlavour = Bound}),TCon (TypeCon {typeconName = std/core/types/string, typeconKind = KCon V}),TApp (TCon (TypeCon {typeconName = samples/handlers/typeclass/show/generic/.hnd-effshow, typeconKind = KApp (KApp (KCon (->)) (KCon V)) (KApp (KApp (KCon (->)) (KCon E)) (KApp (KApp (KCon (->)) (KCon V)) (KCon V)))})) [TVar (TypeVar {typevarId = 32, typevarKind = KCon V, typevarFlavour = Bound})],TVar (TypeVar {typevarId = 33, typevarKind = KCon E, typevarFlavour = Bound}),TVar (TypeVar {typevarId = 34, typevarKind = KCon V, typevarFlavour = Bound})]))) (1, 0), binderNameRange = (1, 0), binderRange = (1, 0)}, defRange = (1, 0), defVis = Public, defSort = fun, defInline = inline, defDoc = "// select `eshow` operation out of the `:effshow` effect handler"}
inferVar; hnd
Doing unify of  _81  and  (<>)
Doing unify of  .hnd-effshow<_78,_79,_80>  and  .hnd-effshow<$74,$75,$76>
Doing unify of  (<>)  and  _82
Doing unify of  bool  and  bool
inferVar; fun-eshow
Doing unify of  _77  and  _84
Doing unify of  _83  and  _84
Doing unify of  std/core/hnd/clause1<$74,string,.hnd-effshow<$74>,$75,$76>  and  std/core/hnd/clause1<$74,string,.hnd-effshow<$74>,$75,$76>
Doing unify of  (<>)  and  _77
Doing unify of  (<>)  and  (<>)
Doing unify of  (<>)  and  _85

infer single .tag-effshow
Def {defBinder = ValueBinder {binderName = .tag-effshow, binderType = (), binderExpr = Ann (App (Var std/core/hnd/.new-htag False (1, 0)) [(Nothing,Lit (LitString "effshow.typeclass_show_generic" (1, 0)))] (1, 0)) (TForall [TypeVar {typevarId = 38, typevarKind = KCon V, typevarFlavour = Bound}] [] (TApp (TCon (TypeCon {typeconName = std/core/hnd/htag, typeconKind = KApp (KApp (KCon (->)) (KApp (KApp (KCon (->)) (KCon E)) (KApp (KApp (KCon (->)) (KCon V)) (KCon V)))) (KCon V)})) [TApp (TCon (TypeCon {typeconName = samples/handlers/typeclass/show/generic/.hnd-effshow, typeconKind = KApp (KApp (KCon (->)) (KCon V)) (KApp (KApp (KCon (->)) (KCon E)) (KApp (KApp (KCon (->)) (KCon V)) (KCon V)))})) [TVar (TypeVar {typevarId = 38, typevarKind = KCon V, typevarFlavour = Bound})]])) (1, 0), binderNameRange = (1, 0), binderRange = (1, 0)}, defRange = (1, 0), defVis = Public, defSort = val, defInline = noinline, defDoc = "// runtime tag for the `:effshow` effect"}
inferVar; std/core/hnd/.new-htag
inferAppFunFirst:: eff1 _98  funEff _97
Doing unify of  _98  and  _99
Doing unify of  _97  and  _98
Defaults: []
AddDefaults: []
New Defaults: [] in Var std/core/hnd/.new-htag False (1, 0)
Propagated:  (<>)
Checking subsume Var std/core/hnd/.new-htag False (1, 0)
Doing unify of  _97  and  _98
Doing unify of  (<>)  and  _97

infer single .handle-effshow
Def {defBinder = ValueBinder {binderName = .handle-effshow, binderType = (), binderExpr = Ann (Lam [ValueBinder {binderName = cfc, binderType = Nothing, binderExpr = Nothing, binderNameRange = (1, 0), binderRange = (1, 0)},ValueBinder {binderName = hnd, binderType = Nothing, binderExpr = Nothing, binderNameRange = (1, 0), binderRange = (1, 0)},ValueBinder {binderName = ret, binderType = Nothing, binderExpr = Nothing, binderNameRange = (1, 0), binderRange = (1, 0)},ValueBinder {binderName = action, binderType = Nothing, binderExpr = Nothing, binderNameRange = (1, 0), binderRange = (1, 0)}] (App (Var std/core/hnd/.hhandle False (1, 0)) [(Nothing,Var .tag-effshow False (1, 0)),(Nothing,Var cfc False (1, 0)),(Nothing,Var hnd False (1, 0)),(Nothing,Var ret False (1, 0)),(Nothing,Var action False (1, 0))] (1, 0)) (1, 0)) (TForall [TypeVar {typevarId = 49, typevarKind = KCon V, typevarFlavour = Bound},TypeVar {typevarId = 50, typevarKind = KCon V, typevarFlavour = Bound},TypeVar {typevarId = 51, typevarKind = KCon E, typevarFlavour = Bound},TypeVar {typevarId = 52, typevarKind = KCon V, typevarFlavour = Bound}] [] (TFun [(cfc,TCon (TypeCon {typeconName = std/core/types/int32, typeconKind = KCon V})),(hnd,TApp (TCon (TypeCon {typeconName = samples/handlers/typeclass/show/generic/.hnd-effshow, typeconKind = KApp (KApp (KCon (->)) (KCon V)) (KApp (KApp (KCon (->)) (KCon E)) (KApp (KApp (KCon (->)) (KCon V)) (KCon V)))})) [TVar (TypeVar {typevarId = 49, typevarKind = KCon V, typevarFlavour = Bound}),TVar (TypeVar {typevarId = 51, typevarKind = KCon E, typevarFlavour = Bound}),TVar (TypeVar {typevarId = 52, typevarKind = KCon V, typevarFlavour = Bound})]),(ret,TFun [(res,TVar (TypeVar {typevarId = 50, typevarKind = KCon V, typevarFlavour = Bound}))] (TVar (TypeVar {typevarId = 51, typevarKind = KCon E, typevarFlavour = Bound})) (TVar (TypeVar {typevarId = 52, typevarKind = KCon V, typevarFlavour = Bound}))),(action,TFun [] (TApp (TCon (TypeCon {typeconName = std/core/types/(<|>), typeconKind = KApp (KApp (KCon (->)) (KCon X)) (KApp (KApp (KCon (->)) (KCon E)) (KCon E))})) [TApp (TCon (TypeCon {typeconName = std/core/types/handled, typeconKind = KApp (KApp (KCon (->)) (KCon HX)) (KCon X)})) [TApp (TCon (TypeCon {typeconName = samples/handlers/typeclass/show/generic/effshow, typeconKind = KApp (KApp (KCon (->)) (KCon V)) (KCon HX)})) [TVar (TypeVar {typevarId = 49, typevarKind = KCon V, typevarFlavour = Bound})]],TVar (TypeVar {typevarId = 51, typevarKind = KCon E, typevarFlavour = Bound})]) (TVar (TypeVar {typevarId = 50, typevarKind = KCon V, typevarFlavour = Bound})))] (TVar (TypeVar {typevarId = 51, typevarKind = KCon E, typevarFlavour = Bound})) (TVar (TypeVar {typevarId = 52, typevarKind = KCon V, typevarFlavour = Bound})))) (1, 0), binderNameRange = (4, 8), binderRange = (4, 1)}, defRange = (1, 0), defVis = Public, defSort = fun, defInline = noinline, defDoc = "// handler for the `:effshow` effect"}
inferVar; std/core/hnd/.hhandle
inferVar; .tag-effshow
inferVar; cfc
inferVar; hnd
inferVar; ret
inferVar; action
inferAppFunFirst:: eff1 _112  funEff _108
Doing unify of  _112  and  _114
Doing unify of  _112  and  _115
Doing unify of  _112  and  _116
Doing unify of  _112  and  _117
Doing unify of  _112  and  _118
Doing unify of  _108  and  _112
Defaults: []
AddDefaults: []
New Defaults: [] in Var std/core/hnd/.hhandle False (1, 0)
Propagated:  1001
Checking subsume Var std/core/hnd/.hhandle False (1, 0)
Doing unify of  _108  and  _112
Doing unify of  $106  and  $106
Doing unify of  $105  and  $105
Doing unify of  $105  and  $105
Doing unify of  (<>)  and  _120

infer single eshow
Def {defBinder = ValueBinder {binderName = eshow, binderType = (), binderExpr = Ann (Lam [ValueBinder {binderName = a, binderType = Nothing, binderExpr = Nothing, binderNameRange = (5,13), binderRange = (5,13)}] (App (Var std/core/hnd/.perform1 False (1, 0)) [(Nothing,App (Var std/core/hnd/.evv-at False (1, 0)) [(Nothing,App (Var std/core/ssize_t False (1, 0)) [(Nothing,Lit (LitInt 0 (1, 0)))] (1, 0))] (1, 0)),(Nothing,Var .select-eshow False (1, 0)),(Nothing,Var a False (5,13))] (1, 0)) (5, 7)) (TForall [TypeVar {typevarId = 58, typevarKind = KCon V, typevarFlavour = Bound}] [] (TFun [(a,TVar (TypeVar {typevarId = 58, typevarKind = KCon V, typevarFlavour = Bound}))] (TApp (TCon (TypeCon {typeconName = std/core/types/(<|>), typeconKind = KApp (KApp (KCon (->)) (KCon X)) (KApp (KApp (KCon (->)) (KCon E)) (KCon E))})) [TApp (TCon (TypeCon {typeconName = std/core/types/handled, typeconKind = KApp (KApp (KCon (->)) (KCon HX)) (KCon X)})) [TApp (TCon (TypeCon {typeconName = samples/handlers/typeclass/show/generic/effshow, typeconKind = KApp (KApp (KCon (->)) (KCon V)) (KCon HX)})) [TVar (TypeVar {typevarId = 58, typevarKind = KCon V, typevarFlavour = Bound})]],TCon (TypeCon {typeconName = std/core/types/(<>), typeconKind = KCon E})]) (TCon (TypeCon {typeconName = std/core/types/string, typeconKind = KCon V})))) (5, 7), binderNameRange = (5, 7), binderRange = (5, 7)}, defRange = (5, 7), defVis = Public, defSort = fun, defInline = inline, defDoc = "// call `eshow` operation of the `:effshow` effect"}
inferVar; std/core/hnd/.perform1
inferVar; std/core/hnd/.evv-at
inferVar; std/core/ssize_t
inferAppFunFirst:: eff1 _143  funEff _142
Doing unify of  _143  and  _144
Doing unify of  _142  and  _143
Defaults: []
AddDefaults: []
New Defaults: [] in Var std/core/ssize_t False (1, 0)
Propagated:  (<>)
Checking subsume Var std/core/ssize_t False (1, 0)
Doing unify of  _142  and  _143
inferAppFunFirst:: eff1 _141  funEff _140
Doing unify of  _141  and  _142
Doing unify of  _140  and  _141
Defaults: []
AddDefaults: []
New Defaults: [] in Var std/core/hnd/.evv-at False (1, 0)
Propagated:  (<>)
Checking subsume Var std/core/hnd/.evv-at False (1, 0)
Doing unify of  _140  and  _141
inferVar; .select-eshow
inferVar; a
inferAppFunFirst:: eff1 _138  funEff _136
Doing unify of  _138  and  _140
Doing unify of  _138  and  _145
Doing unify of  _138  and  _154
Doing unify of  _136  and  _138
Defaults: []
AddDefaults: []
New Defaults: [] in Var std/core/hnd/.perform1 False (1, 0)
Propagated:  1002
Checking subsume Var std/core/hnd/.perform1 False (1, 0)
Doing unify of  _136  and  _138
Doing unify of  string  and  string
Doing unify of  (effshow<$133>)  and  _136
Doing unify of  (effshow<$133>)  and  (effshow<$133>)
Doing unify of  (<>)  and  _156

infer single .default
Def {defBinder = ValueBinder {binderName = .default, binderType = (), binderExpr = Handler {hndlrSort = normal, hndlrScope = HandlerNoScope, hndlrOverride = HandlerNoOverride, hndlrAllowMask = Nothing, hndlrEffect = Nothing, hndlrLocalPars = [], hndlrInitially = Nothing, hndlrReturn = Nothing, hndlrFinally = Nothing, hndlrBranches = [HandlerBranch {hbranchName = eshow, hbranchPars = [ValueBinder {binderName = a, binderType = Just (TCon (TypeCon {typeconName = std/core/types/int, typeconKind = KCon V})), binderExpr = (), binderNameRange = (9,13), binderRange = (9,13)}], hbranchExpr = Parens (App (Var show False (10, 7)) [(Nothing,Var a False (10, 5))] (10, 5))  (9,19), hbranchSort = fun, hbranchNameRange = (9, 7), hbranchPatRange = (9, 7)}], hndlrDeclRange = (8, 9), hndlrRange = (8, 9)}, binderNameRange = (1, 0), binderRange = (1, 0)}, defRange = (8, 1), defVis = Public, defSort = default, defInline = autoinline, defDoc = ""}
infer handler: heff: effshow<_161> , propagated: none
inferVar; samples/handlers/typeclass/show/generic/.handle-effshow
inferVar; std/core/int32
inferAppFunFirst:: eff1 _180  funEff _179
Doing unify of  _180  and  _181
Doing unify of  _179  and  _180
Defaults: []
AddDefaults: []
New Defaults: [] in Var std/core/int32 False (1, 0)
Propagated:  (<>)
Checking subsume Var std/core/int32 False (1, 0)
Doing unify of  _179  and  _180
inferVar; std/core/hnd/clause-tail1
inferVar; a
inferVar; show
inferVar; a
inferAppFunFirst:: eff1 _208  funEff _207
Doing unify of  _208  and  _209
Doing unify of  _207  and  _208
Defaults: []
AddDefaults: []
New Defaults: [] in Var show False (10, 7)
Propagated:  (<>)
Checking subsume Var show False (10, 7)
Doing unify of  _207  and  _208
Doing unify of  _190  and  string
Doing unify of  _187  and  _208
Doing unify of  _187  and  _187
inferAppFunFirst:: eff1 _193  funEff _192
Doing unify of  _193  and  _210
Doing unify of  _192  and  _193
Defaults: []
AddDefaults: []
New Defaults: [] in Var std/core/hnd/clause-tail1 False (8, 9)
Propagated:  (<>)
Checking subsume Var std/core/hnd/clause-tail1 False (8, 9)
Doing unify of  _192  and  _193
inferAppFunFirst:: eff1 _186  funEff _185
Doing unify of  _186  and  _192
Doing unify of  _185  and  _186
Defaults: []
AddDefaults: []
New Defaults: [] in Var samples/handlers/typeclass/show/generic/.Hnd-effshow False (8, 9)
Propagated:  (<>)
Checking subsume Var samples/handlers/typeclass/show/generic/.Hnd-effshow False (8, 9)
Doing unify of  _185  and  _186
inferVar; .x
Doing unify of  _177  and  _175
Doing unify of  _176  and  _211
Doing unify of  _176  and  _176
inferVar; .action
inferAppFunFirst:: eff1 _178  funEff _176
Doing unify of  _178  and  _179
Doing unify of  _178  and  _185
Doing unify of  _178  and  _212
Doing unify of  _178  and  _213
Doing unify of  _176  and  _178
Defaults: []
AddDefaults: []
New Defaults: [] in Var samples/handlers/typeclass/show/generic/.handle-effshow False (8, 9)
Propagated:  131
Checking subsume Var samples/handlers/typeclass/show/generic/.handle-effshow False (8, 9)
Doing unify of  _176  and  _178
Doing unify of  _173  and  _169
Doing unify of  _172  and  _170
Doing unify of  (<>)  and  (<>)
Doing unify of  (<>)  and  _214

infer single .default
Def {defBinder = ValueBinder {binderName = .default, binderType = (), binderExpr = Handler {hndlrSort = normal, hndlrScope = HandlerNoScope, hndlrOverride = HandlerNoOverride, hndlrAllowMask = Nothing, hndlrEffect = Nothing, hndlrLocalPars = [], hndlrInitially = Nothing, hndlrReturn = Nothing, hndlrFinally = Nothing, hndlrBranches = [HandlerBranch {hbranchName = eshow, hbranchPars = [ValueBinder {binderName = a, binderType = Just (TApp (TCon (TypeCon {typeconName = std/core/list, typeconKind = KApp (KApp (KCon (->)) (KCon V)) (KCon V)})) [TVar (TypeVar {typevarId = 61, typevarKind = KCon V, typevarFlavour = Meta})]), binderExpr = (), binderNameRange = (14,13), binderRange = (14,13)}], hbranchExpr = Parens (App (Var join False (15,18)) [(Nothing,App (Var map False (15, 7)) [(Nothing,Var a False (15, 5)),(Nothing,Var eshow False (15,11))] (15, 5)),(Nothing,Lit (LitString ", " (15,23)))] (15, 5))  (14,31), hbranchSort = fun, hbranchNameRange = (14, 7), hbranchPatRange = (14, 7)}], hndlrDeclRange = (13, 9), hndlrRange = (13, 9)}, binderNameRange = (1, 0), binderRange = (1, 0)}, defRange = (13, 1), defVis = Public, defSort = default, defInline = autoinline, defDoc = ""}
infer handler: heff: effshow<_215> , propagated: none
inferVar; samples/handlers/typeclass/show/generic/.handle-effshow
inferVar; std/core/int32
inferAppFunFirst:: eff1 _234  funEff _233
Doing unify of  _234  and  _235
Doing unify of  _233  and  _234
Defaults: []
AddDefaults: []
New Defaults: [] in Var std/core/int32 False (1, 0)
Propagated:  (<>)
Checking subsume Var std/core/int32 False (1, 0)
Doing unify of  _233  and  _234
inferVar; std/core/hnd/clause-tail1
inferVar; a
inferVar; map
inferVar; a
inferVar; eshow
inferAppFunFirst:: eff1 _352  funEff _351
Doing unify of  _352  and  _353
Doing unify of  _352  and  _356
Doing unify of  _351  and  _352
Defaults: []
AddDefaults: []
New Defaults: [] in Var map False (15, 7)
Propagated:  1003
Checking subsume Var map False (15, 7)
Doing unify of  _351  and  _352
inferVar; join
inferVar; a
inferVar; map
inferVar; a
inferVar; eshow
inferAppFunFirst:: eff1 _467  funEff _466
Doing unify of  _467  and  _468
Doing unify of  _467  and  _471
Doing unify of  _466  and  _467
Defaults: []
AddDefaults: []
New Defaults: [] in Var map False (15, 7)
Propagated:  1003
Checking subsume Var map False (15, 7)
Doing unify of  _466  and  _467
inferAppFunFirst:: eff1 _364  funEff _363
Doing unify of  _364  and  <effshow<_469>|_470>
Doing unify of  <effshow<_61>|_470>  and  _474
Doing unify of  _363  and  <effshow<_61>|_470>
Defaults: []
AddDefaults: []
New Defaults: [] in Var join False (15,18)
Propagated:  (<>)
Checking subsume Var join False (15,18)
Doing unify of  _363  and  <effshow<_61>|_470>
Doing unify of  _244  and  string
Doing unify of  _241  and  <effshow<_61>|_470>
Doing unify of  _241  and  _241
inferAppFunFirst:: eff1 _247  funEff _246
Doing unify of  _247  and  _479
Doing unify of  _246  and  _247
Defaults: []
AddDefaults: []
New Defaults: [] in Var std/core/hnd/clause-tail1 False (13, 9)
Propagated:  (<>)
Checking subsume Var std/core/hnd/clause-tail1 False (13, 9)
Doing unify of  _246  and  _247
inferAppFunFirst:: eff1 _240  funEff _239
Doing unify of  _240  and  _246
Doing unify of  _239  and  _240
Defaults: []
AddDefaults: []
New Defaults: [] in Var samples/handlers/typeclass/show/generic/.Hnd-effshow False (13, 9)
Propagated:  (<>)
Checking subsume Var samples/handlers/typeclass/show/generic/.Hnd-effshow False (13, 9)
Doing unify of  _239  and  _240
inferVar; .x
Doing unify of  _231  and  _229
Doing unify of  <effshow<_61>|_470>  and  _482
Doing unify of  <effshow<_61>|_470>  and  <effshow<_61>|_470>
inferVar; .action
inferAppFunFirst:: eff1 _232  funEff _230
Doing unify of  _232  and  _233
Doing unify of  _232  and  _239
Doing unify of  _232  and  _484
Doing unify of  _232  and  _485
Doing unify of  _230  and  _232
Defaults: []
AddDefaults: []
New Defaults: [] in Var samples/handlers/typeclass/show/generic/.handle-effshow False (13, 9)
Propagated:  131
Checking subsume Var samples/handlers/typeclass/show/generic/.handle-effshow False (13, 9)
Doing unify of  _230  and  _232
Doing unify of  _227  and  _223
Doing unify of  _226  and  <effshow<_61>|_470>
Doing unify of  (<>)  and  (<>)
Doing unify of  (<>)  and  _490

infer single main
Def {defBinder = ValueBinder {binderName = main, binderType = (), binderExpr = Ann (Lam [] (Parens (App (Var println False (32,19)) [(Nothing,App (Var eshow False (32,13)) [(Nothing,Parens (App (Var std/core/Cons False (32, 3)) [(Nothing,Lit (LitInt 0 (32, 4))),(Nothing,App (Var std/core/Cons False (32, 3)) [(Nothing,Lit (LitInt 1 (32, 7))),(Nothing,App (Var std/core/Cons False (32, 3)) [(Nothing,Lit (LitInt 2 (32,10))),(Nothing,Var std/core/Nil False (32,11))] (32, 3))] (32, 3))] (32, 3))  (32, 3))] (32, 3))] (32, 3))  (29,24)) (29, 1)) (TFun [] (TApp (TCon (TypeCon {typeconName = std/core/types/(<|>), typeconKind = KApp (KApp (KCon (->)) (KCon X)) (KApp (KApp (KCon (->)) (KCon E)) (KCon E))})) [TCon (TypeCon {typeconName = std/core/console, typeconKind = KCon X}),TCon (TypeCon {typeconName = std/core/types/(<>), typeconKind = KCon E})]) (TCon (TypeCon {typeconName = std/core/types/(), typeconKind = KCon V}))) (29, 1), binderNameRange = (29, 5), binderRange = (29, 5)}, defRange = (29, 1), defVis = Public, defSort = fun, defInline = autoinline, defDoc = "// In koka main is special cased to be wrapped in a function which provides a handler for the console effect\n// In implementing these default handlers we could also make console / exception / async effects\n//  no longer special cased by the compiler. \n"}
inferVar; eshow
inferAppFunFirst:: eff1 _522  funEff _521
Doing unify of  _522  and  _525
Doing unify of  _522  and  _524
Doing unify of  _521  and  _522
Defaults: []
AddDefaults: []
New Defaults: [] in Var std/core/Cons False (32, 3)
Propagated:  (<>)
Checking subsume Var std/core/Cons False (32, 3)
Doing unify of  _521  and  _522
inferAppFunFirst:: eff1 _519  funEff _518
Doing unify of  _519  and  _526
Doing unify of  _519  and  _521
Doing unify of  _518  and  _519
Defaults: []
AddDefaults: []
New Defaults: [] in Var std/core/Cons False (32, 3)
Propagated:  (<>)
Checking subsume Var std/core/Cons False (32, 3)
Doing unify of  _518  and  _519
inferAppFunFirst:: eff1 _516  funEff _515
Doing unify of  _516  and  _527
Doing unify of  _516  and  _518
Doing unify of  _515  and  _516
Defaults: []
AddDefaults: []
New Defaults: [] in Var std/core/Cons False (32, 3)
Propagated:  (<>)
Checking subsume Var std/core/Cons False (32, 3)
Doing unify of  _515  and  _516
inferAppFunFirst:: eff1 _513  funEff <effshow<_511>|_512>
Doing unify of  _513  and  _515
Doing unify of  <effshow<_511>|_512>  and  _513
Defaults: []
AddDefaults: []
New Defaults: [] in Var eshow False (32,13)
Propagated:  (effshow<160>)
Checking subsume Var eshow False (32,13)
Doing unify of  <effshow<_511>|_512>  and  _513
inferVar; println
inferVar; eshow
inferAppFunFirst:: eff1 _548  funEff _547
Doing unify of  _548  and  _551
Doing unify of  _548  and  _550
Doing unify of  _547  and  _548
Defaults: []
AddDefaults: []
New Defaults: [] in Var std/core/Cons False (32, 3)
Propagated:  (<>)
Checking subsume Var std/core/Cons False (32, 3)
Doing unify of  _547  and  _548
inferAppFunFirst:: eff1 _545  funEff _544
Doing unify of  _545  and  _552
Doing unify of  _545  and  _547
Doing unify of  _544  and  _545
Defaults: []
AddDefaults: []
New Defaults: [] in Var std/core/Cons False (32, 3)
Propagated:  (<>)
Checking subsume Var std/core/Cons False (32, 3)
Doing unify of  _544  and  _545
inferAppFunFirst:: eff1 _542  funEff _541
Doing unify of  _542  and  _553
Doing unify of  _542  and  _544
Doing unify of  _541  and  _542
Defaults: []
AddDefaults: []
New Defaults: [] in Var std/core/Cons False (32, 3)
Propagated:  (<>)
Checking subsume Var std/core/Cons False (32, 3)
Doing unify of  _541  and  _542
inferAppFunFirst:: eff1 _539  funEff <effshow<_537>|_538>
Doing unify of  _539  and  _541
Doing unify of  <effshow<_537>|_538>  and  _539
Defaults: []
AddDefaults: []
New Defaults: [] in Var eshow False (32,13)
Propagated:  (effshow<160>)
Checking subsume Var eshow False (32,13)
Doing unify of  <effshow<_537>|_538>  and  _539
inferAppFunFirst:: eff1 _536  funEff <console|_535>
Doing unify of  _536  and  <effshow<list<int>>|_538>
Doing unify of  <console|_535>  and  <effshow<list<int>>|_538>
Match With Substitution samples/handlers/typeclass/show/generic/.default.1
Defaults: [samples/handlers/typeclass/show/generic/.default.1]
AddDefaults: []
New Defaults: [samples/handlers/typeclass/show/generic/.default.1] in Var println False (32,19)
Propagated:  console
Wrapped Expr App (Var samples/handlers/typeclass/show/generic/.default False (1, 0)) [(Nothing,Parens (Lam [] (App (Var println False (32,19)) [(Nothing,App (Var eshow False (32,13)) [(Nothing,Parens (App (Var std/core/Cons False (32, 3)) [(Nothing,Lit (LitInt 0 (32, 4))),(Nothing,App (Var std/core/Cons False (32, 3)) [(Nothing,Lit (LitInt 1 (32, 7))),(Nothing,App (Var std/core/Cons False (32, 3)) [(Nothing,Lit (LitInt 2 (32,10))),(Nothing,Var std/core/Nil False (32,11))] (32, 3))] (32, 3))] (32, 3))  (32, 3))] (32, 3))] (32, 3)) (32, 3))  (1, 0))] (32, 3)
inferVar; eshow
inferAppFunFirst:: eff1 _578  funEff _577
Doing unify of  _578  and  _581
Doing unify of  _578  and  _580
Doing unify of  _577  and  _578
Defaults: []
AddDefaults: [samples/handlers/typeclass/show/generic/.default.1]
New Defaults: [] in Var std/core/Cons False (32, 3)
Propagated:  (<>)
Checking subsume Var std/core/Cons False (32, 3)
Doing unify of  _577  and  _578
inferAppFunFirst:: eff1 _575  funEff _574
Doing unify of  _575  and  _582
Doing unify of  _575  and  _577
Doing unify of  _574  and  _575
Defaults: []
AddDefaults: [samples/handlers/typeclass/show/generic/.default.1]
New Defaults: [] in Var std/core/Cons False (32, 3)
Propagated:  (<>)
Checking subsume Var std/core/Cons False (32, 3)
Doing unify of  _574  and  _575
inferAppFunFirst:: eff1 _572  funEff _571
Doing unify of  _572  and  _583
Doing unify of  _572  and  _574
Doing unify of  _571  and  _572
Defaults: []
AddDefaults: [samples/handlers/typeclass/show/generic/.default.1]
New Defaults: [] in Var std/core/Cons False (32, 3)
Propagated:  (<>)
Checking subsume Var std/core/Cons False (32, 3)
Doing unify of  _571  and  _572
inferAppFunFirst:: eff1 _569  funEff <effshow<_567>|_568>
Doing unify of  _569  and  _571
Doing unify of  <effshow<_567>|_568>  and  _569
Defaults: []
AddDefaults: [samples/handlers/typeclass/show/generic/.default.1]
New Defaults: [] in Var eshow False (32,13)
Propagated:  (effshow<160>)
Checking subsume Var eshow False (32,13)
Doing unify of  <effshow<_567>|_568>  and  _569
inferVar; println
inferVar; eshow
inferAppFunFirst:: eff1 _604  funEff _603
Doing unify of  _604  and  _607
Doing unify of  _604  and  _606
Doing unify of  _603  and  _604
Defaults: []
AddDefaults: [samples/handlers/typeclass/show/generic/.default.1]
New Defaults: [] in Var std/core/Cons False (32, 3)
Propagated:  (<>)
Checking subsume Var std/core/Cons False (32, 3)
Doing unify of  _603  and  _604
inferAppFunFirst:: eff1 _601  funEff _600
Doing unify of  _601  and  _608
Doing unify of  _601  and  _603
Doing unify of  _600  and  _601
Defaults: []
AddDefaults: [samples/handlers/typeclass/show/generic/.default.1]
New Defaults: [] in Var std/core/Cons False (32, 3)
Propagated:  (<>)
Checking subsume Var std/core/Cons False (32, 3)
Doing unify of  _600  and  _601
inferAppFunFirst:: eff1 _598  funEff _597
Doing unify of  _598  and  _609
Doing unify of  _598  and  _600
Doing unify of  _597  and  _598
Defaults: []
AddDefaults: [samples/handlers/typeclass/show/generic/.default.1]
New Defaults: [] in Var std/core/Cons False (32, 3)
Propagated:  (<>)
Checking subsume Var std/core/Cons False (32, 3)
Doing unify of  _597  and  _598
inferAppFunFirst:: eff1 _595  funEff <effshow<_593>|_594>
Doing unify of  _595  and  _597
Doing unify of  <effshow<_593>|_594>  and  _595
Defaults: []
AddDefaults: [samples/handlers/typeclass/show/generic/.default.1]
New Defaults: [] in Var eshow False (32,13)
Propagated:  (effshow<160>)
Checking subsume Var eshow False (32,13)
Doing unify of  <effshow<_593>|_594>  and  _595
inferAppFunFirst:: eff1 _592  funEff <console|_591>
Doing unify of  _592  and  <effshow<list<int>>|_594>
Doing unify of  <console|_591>  and  <effshow<list<int>>|_594>
Match With Substitution samples/handlers/typeclass/show/generic/.default.1
Defaults: [samples/handlers/typeclass/show/generic/.default.1]
AddDefaults: [samples/handlers/typeclass/show/generic/.default.1]
New Defaults: [] in Var println False (32,19)
Propagated:  console
Checking subsume Var println False (32,19)
Doing unify of  <console|_591>  and  <effshow<list<int>>|_594>
Match With Substitution samples/handlers/typeclass/show/generic/.default.1
Doing unify of  _565  and  ()
Doing unify of  _564  and  <effshow<list<int>>|_594>
inferVar; samples/handlers/typeclass/show/generic/.default
inferVar; eshow
inferAppFunFirst:: eff1 _655  funEff _654
Doing unify of  _655  and  _658
Doing unify of  _655  and  _657
Doing unify of  _654  and  _655
Defaults: []
AddDefaults: [samples/handlers/typeclass/show/generic/.default.1]
New Defaults: [] in Var std/core/Cons False (32, 3)
Propagated:  (<>)
Checking subsume Var std/core/Cons False (32, 3)
Doing unify of  _654  and  _655
inferAppFunFirst:: eff1 _652  funEff _651
Doing unify of  _652  and  _659
Doing unify of  _652  and  _654
Doing unify of  _651  and  _652
Defaults: []
AddDefaults: [samples/handlers/typeclass/show/generic/.default.1]
New Defaults: [] in Var std/core/Cons False (32, 3)
Propagated:  (<>)
Checking subsume Var std/core/Cons False (32, 3)
Doing unify of  _651  and  _652
inferAppFunFirst:: eff1 _649  funEff _648
Doing unify of  _649  and  _660
Doing unify of  _649  and  _651
Doing unify of  _648  and  _649
Defaults: []
AddDefaults: [samples/handlers/typeclass/show/generic/.default.1]
New Defaults: [] in Var std/core/Cons False (32, 3)
Propagated:  (<>)
Checking subsume Var std/core/Cons False (32, 3)
Doing unify of  _648  and  _649
inferAppFunFirst:: eff1 _646  funEff <effshow<_644>|_645>
Doing unify of  _646  and  _648
Doing unify of  <effshow<_644>|_645>  and  _646
Defaults: []
AddDefaults: [samples/handlers/typeclass/show/generic/.default.1]
New Defaults: [] in Var eshow False (32,13)
Propagated:  (effshow<160>)
Checking subsume Var eshow False (32,13)
Doing unify of  <effshow<_644>|_645>  and  _646
inferVar; println
inferVar; eshow
inferAppFunFirst:: eff1 _681  funEff _680
Doing unify of  _681  and  _684
Doing unify of  _681  and  _683
Doing unify of  _680  and  _681
Defaults: []
AddDefaults: [samples/handlers/typeclass/show/generic/.default.1]
New Defaults: [] in Var std/core/Cons False (32, 3)
Propagated:  (<>)
Checking subsume Var std/core/Cons False (32, 3)
Doing unify of  _680  and  _681
inferAppFunFirst:: eff1 _678  funEff _677
Doing unify of  _678  and  _685
Doing unify of  _678  and  _680
Doing unify of  _677  and  _678
Defaults: []
AddDefaults: [samples/handlers/typeclass/show/generic/.default.1]
New Defaults: [] in Var std/core/Cons False (32, 3)
Propagated:  (<>)
Checking subsume Var std/core/Cons False (32, 3)
Doing unify of  _677  and  _678
inferAppFunFirst:: eff1 _675  funEff _674
Doing unify of  _675  and  _686
Doing unify of  _675  and  _677
Doing unify of  _674  and  _675
Defaults: []
AddDefaults: [samples/handlers/typeclass/show/generic/.default.1]
New Defaults: [] in Var std/core/Cons False (32, 3)
Propagated:  (<>)
Checking subsume Var std/core/Cons False (32, 3)
Doing unify of  _674  and  _675
inferAppFunFirst:: eff1 _672  funEff <effshow<_670>|_671>
Doing unify of  _672  and  _674
Doing unify of  <effshow<_670>|_671>  and  _672
Defaults: []
AddDefaults: [samples/handlers/typeclass/show/generic/.default.1]
New Defaults: [] in Var eshow False (32,13)
Propagated:  (effshow<160>)
Checking subsume Var eshow False (32,13)
Doing unify of  <effshow<_670>|_671>  and  _672
inferAppFunFirst:: eff1 _669  funEff <console|_668>
Doing unify of  _669  and  <effshow<list<int>>|_671>
Doing unify of  <console|_668>  and  <effshow<list<int>>|_671>
Match With Substitution samples/handlers/typeclass/show/generic/.default.1
Defaults: [samples/handlers/typeclass/show/generic/.default.1]
AddDefaults: [samples/handlers/typeclass/show/generic/.default.1]
New Defaults: [] in Var println False (32,19)
Propagated:  console
Checking subsume Var println False (32,19)
Doing unify of  <console|_668>  and  <effshow<list<int>>|_671>
Match With Substitution samples/handlers/typeclass/show/generic/.default.1
Doing unify of  _640  and  ()
Doing unify of  <effshow<list<_639>>,effshow<_639>|_641>  and  <effshow<list<int>>|_671>
Doing unify of  <effshow<list<_639>>,effshow<_639>|_641>  and  <effshow<list<_639>>,effshow<_639>|_641>
inferAppFunFirst:: eff1 _642  funEff <effshow<_639>|_641>
Doing unify of  _642  and  _695
Doing unify of  <effshow<_639>|_641>  and  _642
Defaults: []
AddDefaults: [samples/handlers/typeclass/show/generic/.default.1]
New Defaults: [] in Var samples/handlers/typeclass/show/generic/.default False (1, 0)
Propagated:  <effshow<61>|470>
Checking subsume Var samples/handlers/typeclass/show/generic/.default False (1, 0)
Doing unify of  <effshow<_639>|_641>  and  _642
Doing unify of  ()  and  ()
Doing unify of  console  and  <console,effshow<int>|_691>
Match Exact samples/handlers/typeclass/show/generic/.default.1
Doing unify of  console  and  console
Doing unify of  (<>)  and  _697
