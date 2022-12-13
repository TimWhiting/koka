[6ncompile: samples/handlers/typeclass_show_generic.kk
loading: std/core
loading: std/core/types
loading: std/core/hnd
check  : samples/handlers/typeclass/show/generic

infer single .tag-effshow
Def {defBinder = ValueBinder {binderName = .tag-effshow, binderType = (), binderExpr = Ann (App (Var std/core/hnd/.new-htag False (1, 0)) [(Nothing,Lit (LitString "effshow.typeclass_show_generic" (1, 0)))] (1, 0)) (TForall [TypeVar {typevarId = 24, typevarKind = KCon V, typevarFlavour = Bound}] [] (TApp (TCon (TypeCon {typeconName = std/core/hnd/htag, typeconKind = KApp (KApp (KCon (->)) (KApp (KApp (KCon (->)) (KCon E)) (KApp (KApp (KCon (->)) (KCon V)) (KCon V)))) (KCon V)})) [TApp (TCon (TypeCon {typeconName = samples/handlers/typeclass/show/generic/.hnd-effshow, typeconKind = KApp (KApp (KCon (->)) (KCon V)) (KApp (KApp (KCon (->)) (KCon E)) (KApp (KApp (KCon (->)) (KCon V)) (KCon V)))})) [TVar (TypeVar {typevarId = 24, typevarKind = KCon V, typevarFlavour = Bound})]])) (1, 0), binderNameRange = (1, 0), binderRange = (1, 0)}, defRange = (1, 0), defVis = Public, defSort = val, defInline = noinline, defDoc = "// runtime tag for the `:effshow` effect"}
inferVar; std/core/hnd/.new-htag
inferAppFunFirst:: eff1 _76  funEff _75
Doing unify of  _76  and  _77
Doing unify of  _75  and  _76
Defaults: []
AddDefaults: []
New Defaults: [] in Var std/core/hnd/.new-htag False (1, 0)
Propagated:  (<>)
Checking subsume Var std/core/hnd/.new-htag False (1, 0)
Doing unify of  _75  and  _76
Doing unify of  (<>)  and  _75

infer single .handle-effshow
Def {defBinder = ValueBinder {binderName = .handle-effshow, binderType = (), binderExpr = Ann (Lam [ValueBinder {binderName = cfc, binderType = Nothing, binderExpr = Nothing, binderNameRange = (1, 0), binderRange = (1, 0)},ValueBinder {binderName = hnd, binderType = Nothing, binderExpr = Nothing, binderNameRange = (1, 0), binderRange = (1, 0)},ValueBinder {binderName = ret, binderType = Nothing, binderExpr = Nothing, binderNameRange = (1, 0), binderRange = (1, 0)},ValueBinder {binderName = action, binderType = Nothing, binderExpr = Nothing, binderNameRange = (1, 0), binderRange = (1, 0)}] (App (Var std/core/hnd/.hhandle False (1, 0)) [(Nothing,Var .tag-effshow False (1, 0)),(Nothing,Var cfc False (1, 0)),(Nothing,Var hnd False (1, 0)),(Nothing,Var ret False (1, 0)),(Nothing,Var action False (1, 0))] (1, 0)) (1, 0)) (TForall [TypeVar {typevarId = 35, typevarKind = KCon V, typevarFlavour = Bound},TypeVar {typevarId = 36, typevarKind = KCon V, typevarFlavour = Bound},TypeVar {typevarId = 37, typevarKind = KCon E, typevarFlavour = Bound},TypeVar {typevarId = 38, typevarKind = KCon V, typevarFlavour = Bound}] [] (TFun [(cfc,TCon (TypeCon {typeconName = std/core/types/int32, typeconKind = KCon V})),(hnd,TApp (TCon (TypeCon {typeconName = samples/handlers/typeclass/show/generic/.hnd-effshow, typeconKind = KApp (KApp (KCon (->)) (KCon V)) (KApp (KApp (KCon (->)) (KCon E)) (KApp (KApp (KCon (->)) (KCon V)) (KCon V)))})) [TVar (TypeVar {typevarId = 35, typevarKind = KCon V, typevarFlavour = Bound}),TVar (TypeVar {typevarId = 37, typevarKind = KCon E, typevarFlavour = Bound}),TVar (TypeVar {typevarId = 38, typevarKind = KCon V, typevarFlavour = Bound})]),(ret,TFun [(res,TVar (TypeVar {typevarId = 36, typevarKind = KCon V, typevarFlavour = Bound}))] (TVar (TypeVar {typevarId = 37, typevarKind = KCon E, typevarFlavour = Bound})) (TVar (TypeVar {typevarId = 38, typevarKind = KCon V, typevarFlavour = Bound}))),(action,TFun [] (TApp (TCon (TypeCon {typeconName = std/core/types/(<|>), typeconKind = KApp (KApp (KCon (->)) (KCon X)) (KApp (KApp (KCon (->)) (KCon E)) (KCon E))})) [TApp (TCon (TypeCon {typeconName = std/core/types/handled, typeconKind = KApp (KApp (KCon (->)) (KCon HX)) (KCon X)})) [TApp (TCon (TypeCon {typeconName = samples/handlers/typeclass/show/generic/effshow, typeconKind = KApp (KApp (KCon (->)) (KCon V)) (KCon HX)})) [TVar (TypeVar {typevarId = 35, typevarKind = KCon V, typevarFlavour = Bound})]],TVar (TypeVar {typevarId = 37, typevarKind = KCon E, typevarFlavour = Bound})]) (TVar (TypeVar {typevarId = 36, typevarKind = KCon V, typevarFlavour = Bound})))] (TVar (TypeVar {typevarId = 37, typevarKind = KCon E, typevarFlavour = Bound})) (TVar (TypeVar {typevarId = 38, typevarKind = KCon V, typevarFlavour = Bound})))) (1, 0), binderNameRange = (4, 8), binderRange = (4, 1)}, defRange = (1, 0), defVis = Public, defSort = fun, defInline = noinline, defDoc = "// handler for the `:effshow` effect"}
inferVar; std/core/hnd/.hhandle
inferVar; .tag-effshow
inferVar; cfc
inferVar; hnd
inferVar; ret
inferVar; action
inferAppFunFirst:: eff1 _90  funEff _86
Doing unify of  _90  and  _92
Doing unify of  _90  and  _93
Doing unify of  _90  and  _94
Doing unify of  _90  and  _95
Doing unify of  _90  and  _96
Doing unify of  _86  and  _90
Defaults: []
AddDefaults: []
New Defaults: [] in Var std/core/hnd/.hhandle False (1, 0)
Propagated:  1001
Checking subsume Var std/core/hnd/.hhandle False (1, 0)
Doing unify of  _86  and  _90
Doing unify of  $84  and  $84
Doing unify of  $83  and  $83
Doing unify of  $83  and  $83
Doing unify of  (<>)  and  _98

infer single .select-eshow
Def {defBinder = ValueBinder {binderName = .select-eshow, binderType = (), binderExpr = Ann (Lam [ValueBinder {binderName = hnd, binderType = Nothing, binderExpr = Nothing, binderNameRange = (1, 0), binderRange = (1, 0)}] (Case (Var hnd False (1, 0)) [Branch {branchPattern = PatCon .Hnd-effshow [(Nothing,PatVar (ValueBinder {binderName = fun-eshow, binderType = Nothing, binderExpr = PatWild (1, 0), binderNameRange = (1, 0), binderRange = (1, 0)}))] (1, 0) (1, 0), branchGuards = [Guard {guardTest = Var std/core/types/True False (1, 0), guardExpr = Var fun-eshow False (1, 0)}]}] (1, 0)) (1, 0)) (TForall [TypeVar {typevarId = 50, typevarKind = KCon V, typevarFlavour = Bound},TypeVar {typevarId = 51, typevarKind = KCon E, typevarFlavour = Bound},TypeVar {typevarId = 52, typevarKind = KCon V, typevarFlavour = Bound}] [] (TFun [(hnd,TApp (TCon (TypeCon {typeconName = samples/handlers/typeclass/show/generic/.hnd-effshow, typeconKind = KApp (KApp (KCon (->)) (KCon V)) (KApp (KApp (KCon (->)) (KCon E)) (KApp (KApp (KCon (->)) (KCon V)) (KCon V)))})) [TVar (TypeVar {typevarId = 50, typevarKind = KCon V, typevarFlavour = Bound}),TVar (TypeVar {typevarId = 51, typevarKind = KCon E, typevarFlavour = Bound}),TVar (TypeVar {typevarId = 52, typevarKind = KCon V, typevarFlavour = Bound})])] (TCon (TypeCon {typeconName = std/core/types/(<>), typeconKind = KCon E})) (TApp (TCon (TypeCon {typeconName = std/core/hnd/clause1, typeconKind = KApp (KApp (KCon (->)) (KCon V)) (KApp (KApp (KCon (->)) (KCon V)) (KApp (KApp (KCon (->)) (KApp (KApp (KCon (->)) (KCon E)) (KApp (KApp (KCon (->)) (KCon V)) (KCon V)))) (KApp (KApp (KCon (->)) (KCon E)) (KApp (KApp (KCon (->)) (KCon V)) (KCon V)))))})) [TVar (TypeVar {typevarId = 50, typevarKind = KCon V, typevarFlavour = Bound}),TCon (TypeCon {typeconName = std/core/types/string, typeconKind = KCon V}),TApp (TCon (TypeCon {typeconName = samples/handlers/typeclass/show/generic/.hnd-effshow, typeconKind = KApp (KApp (KCon (->)) (KCon V)) (KApp (KApp (KCon (->)) (KCon E)) (KApp (KApp (KCon (->)) (KCon V)) (KCon V)))})) [TVar (TypeVar {typevarId = 50, typevarKind = KCon V, typevarFlavour = Bound})],TVar (TypeVar {typevarId = 51, typevarKind = KCon E, typevarFlavour = Bound}),TVar (TypeVar {typevarId = 52, typevarKind = KCon V, typevarFlavour = Bound})]))) (1, 0), binderNameRange = (1, 0), binderRange = (1, 0)}, defRange = (1, 0), defVis = Public, defSort = fun, defInline = inline, defDoc = "// select `eshow` operation out of the `:effshow` effect handler"}
inferVar; hnd
Doing unify of  _118  and  (<>)
Doing unify of  .hnd-effshow<_115,_116,_117>  and  .hnd-effshow<$111,$112,$113>
Doing unify of  (<>)  and  _119
Doing unify of  bool  and  bool
inferVar; fun-eshow
Doing unify of  _114  and  _121
Doing unify of  _120  and  _121
Doing unify of  std/core/hnd/clause1<$111,string,.hnd-effshow<$111>,$112,$113>  and  std/core/hnd/clause1<$111,string,.hnd-effshow<$111>,$112,$113>
Doing unify of  (<>)  and  _114
Doing unify of  (<>)  and  (<>)
Doing unify of  (<>)  and  _122

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

infer single default_int
Def {defBinder = ValueBinder {binderName = default_int, binderType = (), binderExpr = Handler {hndlrSort = normal, hndlrScope = HandlerNoScope, hndlrOverride = HandlerNoOverride, hndlrAllowMask = Nothing, hndlrEffect = Nothing, hndlrLocalPars = [], hndlrInitially = Nothing, hndlrReturn = Nothing, hndlrFinally = Nothing, hndlrBranches = [HandlerBranch {hbranchName = eshow, hbranchPars = [ValueBinder {binderName = a, binderType = Just (TCon (TypeCon {typeconName = std/core/types/int, typeconKind = KCon V})), binderExpr = (), binderNameRange = (18,13), binderRange = (18,13)}], hbranchExpr = Parens (App (Var show False (19, 7)) [(Nothing,Var a False (19, 5))] (19, 5))  (18,19), hbranchSort = fun, hbranchNameRange = (18, 7), hbranchPatRange = (18, 7)}], hndlrDeclRange = (17,19), hndlrRange = (17,19)}, binderNameRange = (17, 5), binderRange = (17, 1)}, defRange = (17, 1), defVis = Public, defSort = val, defInline = autoinline, defDoc = ""}
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
New Defaults: [] in Var show False (19, 7)
Propagated:  (<>)
Checking subsume Var show False (19, 7)
Doing unify of  _207  and  _208
Doing unify of  _190  and  string
Doing unify of  _187  and  _208
Doing unify of  _187  and  _187
inferAppFunFirst:: eff1 _193  funEff _192
Doing unify of  _193  and  _210
Doing unify of  _192  and  _193
Defaults: []
AddDefaults: []
New Defaults: [] in Var std/core/hnd/clause-tail1 False (17,19)
Propagated:  (<>)
Checking subsume Var std/core/hnd/clause-tail1 False (17,19)
Doing unify of  _192  and  _193
inferAppFunFirst:: eff1 _186  funEff _185
Doing unify of  _186  and  _192
Doing unify of  _185  and  _186
Defaults: []
AddDefaults: []
New Defaults: [] in Var samples/handlers/typeclass/show/generic/.Hnd-effshow False (17,19)
Propagated:  (<>)
Checking subsume Var samples/handlers/typeclass/show/generic/.Hnd-effshow False (17,19)
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
New Defaults: [] in Var samples/handlers/typeclass/show/generic/.handle-effshow False (17,19)
Propagated:  109
Checking subsume Var samples/handlers/typeclass/show/generic/.handle-effshow False (17,19)
Doing unify of  _176  and  _178
Doing unify of  _173  and  _169
Doing unify of  _172  and  _170
Doing unify of  (<>)  and  (<>)
Doing unify of  (<>)  and  _214

infer single default_list
Def {defBinder = ValueBinder {binderName = default_list, binderType = (), binderExpr = Handler {hndlrSort = normal, hndlrScope = HandlerNoScope, hndlrOverride = HandlerNoOverride, hndlrAllowMask = Nothing, hndlrEffect = Nothing, hndlrLocalPars = [], hndlrInitially = Nothing, hndlrReturn = Nothing, hndlrFinally = Nothing, hndlrBranches = [HandlerBranch {hbranchName = eshow, hbranchPars = [ValueBinder {binderName = a, binderType = Just (TApp (TCon (TypeCon {typeconName = std/core/list, typeconKind = KApp (KApp (KCon (->)) (KCon V)) (KCon V)})) [TVar (TypeVar {typevarId = 61, typevarKind = KCon V, typevarFlavour = Meta})]), binderExpr = (), binderNameRange = (23,13), binderRange = (23,13)}], hbranchExpr = Parens (App (Var join False (24,18)) [(Nothing,App (Var map False (24, 7)) [(Nothing,Var a False (24, 5)),(Nothing,Var eshow False (24,11))] (24, 5)),(Nothing,Lit (LitString ", " (24,23)))] (24, 5))  (23,31), hbranchSort = fun, hbranchNameRange = (23, 7), hbranchPatRange = (23, 7)}], hndlrDeclRange = (22,20), hndlrRange = (22,20)}, binderNameRange = (22, 5), binderRange = (22, 1)}, defRange = (22, 1), defVis = Public, defSort = val, defInline = autoinline, defDoc = "// Needs to unify with effshow<list<int>> to being handled, but with the handlers body requires effshow<a> instantiated with int\n"}
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
New Defaults: [] in Var map False (24, 7)
Propagated:  1003
Checking subsume Var map False (24, 7)
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
New Defaults: [] in Var map False (24, 7)
Propagated:  1003
Checking subsume Var map False (24, 7)
Doing unify of  _466  and  _467
inferAppFunFirst:: eff1 _364  funEff _363
Doing unify of  _364  and  <effshow<_469>|_470>
Doing unify of  <effshow<_61>|_470>  and  _474
Doing unify of  _363  and  <effshow<_61>|_470>
Defaults: []
AddDefaults: []
New Defaults: [] in Var join False (24,18)
Propagated:  (<>)
Checking subsume Var join False (24,18)
Doing unify of  _363  and  <effshow<_61>|_470>
Doing unify of  _244  and  string
Doing unify of  _241  and  <effshow<_61>|_470>
Doing unify of  _241  and  _241
inferAppFunFirst:: eff1 _247  funEff _246
Doing unify of  _247  and  _479
Doing unify of  _246  and  _247
Defaults: []
AddDefaults: []
New Defaults: [] in Var std/core/hnd/clause-tail1 False (22,20)
Propagated:  (<>)
Checking subsume Var std/core/hnd/clause-tail1 False (22,20)
Doing unify of  _246  and  _247
inferAppFunFirst:: eff1 _240  funEff _239
Doing unify of  _240  and  _246
Doing unify of  _239  and  _240
Defaults: []
AddDefaults: []
New Defaults: [] in Var samples/handlers/typeclass/show/generic/.Hnd-effshow False (22,20)
Propagated:  (<>)
Checking subsume Var samples/handlers/typeclass/show/generic/.Hnd-effshow False (22,20)
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
New Defaults: [] in Var samples/handlers/typeclass/show/generic/.handle-effshow False (22,20)
Propagated:  109
Checking subsume Var samples/handlers/typeclass/show/generic/.handle-effshow False (22,20)
Doing unify of  _230  and  _232
Doing unify of  _227  and  _223
Doing unify of  _226  and  <effshow<_61>|_470>
Doing unify of  (<>)  and  (<>)
Doing unify of  (<>)  and  _490

infer single main
Def {defBinder = ValueBinder {binderName = main, binderType = (), binderExpr = Ann (Lam [] (Parens (App (Var default_int False (30, 8)) [(Nothing,Parens (Lam [] (App (Var default_list False (31, 8)) [(Nothing,Parens (Lam [] (App (Var println False (32,19)) [(Nothing,App (Var eshow False (32,13)) [(Nothing,Parens (App (Var std/core/Cons False (32, 3)) [(Nothing,Lit (LitInt 0 (32, 4))),(Nothing,App (Var std/core/Cons False (32, 3)) [(Nothing,Lit (LitInt 1 (32, 7))),(Nothing,App (Var std/core/Cons False (32, 3)) [(Nothing,Lit (LitInt 2 (32,10))),(Nothing,Var std/core/Nil False (32,11))] (32, 3))] (32, 3))] (32, 3))  (32, 3))] (32, 3))] (32, 3)) (31, 3))  (32, 3))] (31, 3)) (30, 3))  (31, 3))] (30, 3))  (29,24)) (29, 1)) (TFun [] (TApp (TCon (TypeCon {typeconName = std/core/types/(<|>), typeconKind = KApp (KApp (KCon (->)) (KCon X)) (KApp (KApp (KCon (->)) (KCon E)) (KCon E))})) [TCon (TypeCon {typeconName = std/core/console, typeconKind = KCon X}),TCon (TypeCon {typeconName = std/core/types/(<>), typeconKind = KCon E})]) (TCon (TypeCon {typeconName = std/core/types/(), typeconKind = KCon V}))) (29, 1), binderNameRange = (29, 5), binderRange = (29, 5)}, defRange = (29, 1), defVis = Public, defSort = fun, defInline = autoinline, defDoc = "// In koka main is special cased to be wrapped in a function which provides a handler for the console effect\n// In implementing these default handlers we could also make console / exception / async effects\n//  no longer special cased by the compiler. \n"}
inferVar; default_int
inferVar; default_list
inferVar; eshow
inferAppFunFirst:: eff1 _510  funEff _509
Doing unify of  _510  and  _513
Doing unify of  _510  and  _512
Doing unify of  _509  and  _510
Defaults: []
AddDefaults: []
New Defaults: [] in Var std/core/Cons False (32, 3)
Propagated:  (<>)
Checking subsume Var std/core/Cons False (32, 3)
Doing unify of  _509  and  _510
inferAppFunFirst:: eff1 _507  funEff _506
Doing unify of  _507  and  _514
Doing unify of  _507  and  _509
Doing unify of  _506  and  _507
Defaults: []
AddDefaults: []
New Defaults: [] in Var std/core/Cons False (32, 3)
Propagated:  (<>)
Checking subsume Var std/core/Cons False (32, 3)
Doing unify of  _506  and  _507
inferAppFunFirst:: eff1 _504  funEff _503
Doing unify of  _504  and  _515
Doing unify of  _504  and  _506
Doing unify of  _503  and  _504
Defaults: []
AddDefaults: []
New Defaults: [] in Var std/core/Cons False (32, 3)
Propagated:  (<>)
Checking subsume Var std/core/Cons False (32, 3)
Doing unify of  _503  and  _504
inferAppFunFirst:: eff1 _501  funEff <effshow<_499>|_500>
Doing unify of  _501  and  _503
Doing unify of  <effshow<_499>|_500>  and  _501
Defaults: []
AddDefaults: []
New Defaults: [] in Var eshow False (32,13)
Propagated:  (effshow<160>)
Checking subsume Var eshow False (32,13)
Doing unify of  <effshow<_499>|_500>  and  _501
inferVar; println
inferVar; eshow
inferAppFunFirst:: eff1 _536  funEff _535
Doing unify of  _536  and  _539
Doing unify of  _536  and  _538
Doing unify of  _535  and  _536
Defaults: []
AddDefaults: []
New Defaults: [] in Var std/core/Cons False (32, 3)
Propagated:  (<>)
Checking subsume Var std/core/Cons False (32, 3)
Doing unify of  _535  and  _536
inferAppFunFirst:: eff1 _533  funEff _532
Doing unify of  _533  and  _540
Doing unify of  _533  and  _535
Doing unify of  _532  and  _533
Defaults: []
AddDefaults: []
New Defaults: [] in Var std/core/Cons False (32, 3)
Propagated:  (<>)
Checking subsume Var std/core/Cons False (32, 3)
Doing unify of  _532  and  _533
inferAppFunFirst:: eff1 _530  funEff _529
Doing unify of  _530  and  _541
Doing unify of  _530  and  _532
Doing unify of  _529  and  _530
Defaults: []
AddDefaults: []
New Defaults: [] in Var std/core/Cons False (32, 3)
Propagated:  (<>)
Checking subsume Var std/core/Cons False (32, 3)
Doing unify of  _529  and  _530
inferAppFunFirst:: eff1 _527  funEff <effshow<_525>|_526>
Doing unify of  _527  and  _529
Doing unify of  <effshow<_525>|_526>  and  _527
Defaults: []
AddDefaults: []
New Defaults: [] in Var eshow False (32,13)
Propagated:  (effshow<160>)
Checking subsume Var eshow False (32,13)
Doing unify of  <effshow<_525>|_526>  and  _527
inferAppFunFirst:: eff1 _524  funEff <console|_523>
Doing unify of  _524  and  <effshow<list<int>>|_526>
Doing unify of  <console|_523>  and  <effshow<list<int>>|_526>
Defaults: []
AddDefaults: []
New Defaults: [] in Var println False (32,19)
Propagated:  console
Checking subsume Var println False (32,19)
Doing unify of  <console|_523>  and  <effshow<list<int>>|_526>
Doing unify of  _495  and  ()
Doing unify of  <effshow<list<_494>>,effshow<_494>|_496>  and  <effshow<list<int>>|_526>
Doing unify of  <effshow<list<_494>>,effshow<_494>|_496>  and  <effshow<list<_494>>,effshow<_494>|_496>
inferAppFunFirst:: eff1 _497  funEff <effshow<_494>|_496>
Doing unify of  _497  and  _552
Doing unify of  <effshow<_494>|_496>  and  _497
Defaults: []
AddDefaults: []
New Defaults: [] in Var default_list False (31, 8)
Propagated:  <effshow<61>|470>
Checking subsume Var default_list False (31, 8)
Doing unify of  <effshow<_494>|_496>  and  _497
Doing unify of  _491  and  ()
Doing unify of  <effshow<int>|_492>  and  _497
Doing unify of  <effshow<int>|_492>  and  <effshow<int>|_492>
inferAppFunFirst:: eff1 _493  funEff _492
Doing unify of  _493  and  _556
Doing unify of  _492  and  _493
Defaults: []
AddDefaults: []
New Defaults: [] in Var default_int False (30, 8)
Propagated:  170
Checking subsume Var default_int False (30, 8)
Doing unify of  _492  and  _493
Doing unify of  ()  and  ()
Doing unify of  console  and  <console|_548>
Doing unify of  console  and  console
Doing unify of  (<>)  and  _558
