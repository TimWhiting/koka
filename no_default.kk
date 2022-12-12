[6ncompile: samples/handlers/typeclass_show_generic.kk
loading: std/core
loading: std/core/types
loading: std/core/hnd
check  : samples/handlers/typeclass/show/generic

infer single .tag-effshow
Def {defBinder = ValueBinder {binderName = .tag-effshow, binderType = (), binderExpr = Ann (App (Var std/core/hnd/.new-htag False (1, 0)) [(Nothing,Lit (LitString "effshow.typeclass_show_generic" (1, 0)))] (1, 0)) (TForall [TypeVar {typevarId = 24, typevarKind = KCon V, typevarFlavour = Bound}] [] (TApp (TCon (TypeCon {typeconName = std/core/hnd/htag, typeconKind = KApp (KApp (KCon (->)) (KApp (KApp (KCon (->)) (KCon E)) (KApp (KApp (KCon (->)) (KCon V)) (KCon V)))) (KCon V)})) [TApp (TCon (TypeCon {typeconName = samples/handlers/typeclass/show/generic/.hnd-effshow, typeconKind = KApp (KApp (KCon (->)) (KCon V)) (KApp (KApp (KCon (->)) (KCon E)) (KApp (KApp (KCon (->)) (KCon V)) (KCon V)))})) [TVar (TypeVar {typevarId = 24, typevarKind = KCon V, typevarFlavour = Bound})]])) (1, 0), binderNameRange = (1, 0), binderRange = (1, 0)}, defRange = (1, 0), defVis = Public, defSort = val, defInline = noinline, defDoc = "// runtime tag for the `:effshow` effect"}
infer: App Var std/core/hnd/.new-htag False (1, 0)
Defaults: []

infer single .handle-effshow
Def {defBinder = ValueBinder {binderName = .handle-effshow, binderType = (), binderExpr = Ann (Lam [ValueBinder {binderName = cfc, binderType = Nothing, binderExpr = Nothing, binderNameRange = (1, 0), binderRange = (1, 0)},ValueBinder {binderName = hnd, binderType = Nothing, binderExpr = Nothing, binderNameRange = (1, 0), binderRange = (1, 0)},ValueBinder {binderName = ret, binderType = Nothing, binderExpr = Nothing, binderNameRange = (1, 0), binderRange = (1, 0)},ValueBinder {binderName = action, binderType = Nothing, binderExpr = Nothing, binderNameRange = (1, 0), binderRange = (1, 0)}] (App (Var std/core/hnd/.hhandle False (1, 0)) [(Nothing,Var .tag-effshow False (1, 0)),(Nothing,Var cfc False (1, 0)),(Nothing,Var hnd False (1, 0)),(Nothing,Var ret False (1, 0)),(Nothing,Var action False (1, 0))] (1, 0)) (1, 0)) (TForall [TypeVar {typevarId = 35, typevarKind = KCon V, typevarFlavour = Bound},TypeVar {typevarId = 36, typevarKind = KCon V, typevarFlavour = Bound},TypeVar {typevarId = 37, typevarKind = KCon E, typevarFlavour = Bound},TypeVar {typevarId = 38, typevarKind = KCon V, typevarFlavour = Bound}] [] (TFun [(cfc,TCon (TypeCon {typeconName = std/core/types/int32, typeconKind = KCon V})),(hnd,TApp (TCon (TypeCon {typeconName = samples/handlers/typeclass/show/generic/.hnd-effshow, typeconKind = KApp (KApp (KCon (->)) (KCon V)) (KApp (KApp (KCon (->)) (KCon E)) (KApp (KApp (KCon (->)) (KCon V)) (KCon V)))})) [TVar (TypeVar {typevarId = 35, typevarKind = KCon V, typevarFlavour = Bound}),TVar (TypeVar {typevarId = 37, typevarKind = KCon E, typevarFlavour = Bound}),TVar (TypeVar {typevarId = 38, typevarKind = KCon V, typevarFlavour = Bound})]),(ret,TFun [(res,TVar (TypeVar {typevarId = 36, typevarKind = KCon V, typevarFlavour = Bound}))] (TVar (TypeVar {typevarId = 37, typevarKind = KCon E, typevarFlavour = Bound})) (TVar (TypeVar {typevarId = 38, typevarKind = KCon V, typevarFlavour = Bound}))),(action,TFun [] (TApp (TCon (TypeCon {typeconName = std/core/types/(<|>), typeconKind = KApp (KApp (KCon (->)) (KCon X)) (KApp (KApp (KCon (->)) (KCon E)) (KCon E))})) [TApp (TCon (TypeCon {typeconName = std/core/types/handled, typeconKind = KApp (KApp (KCon (->)) (KCon HX)) (KCon X)})) [TApp (TCon (TypeCon {typeconName = samples/handlers/typeclass/show/generic/effshow, typeconKind = KApp (KApp (KCon (->)) (KCon V)) (KCon HX)})) [TVar (TypeVar {typevarId = 35, typevarKind = KCon V, typevarFlavour = Bound})]],TVar (TypeVar {typevarId = 37, typevarKind = KCon E, typevarFlavour = Bound})]) (TVar (TypeVar {typevarId = 36, typevarKind = KCon V, typevarFlavour = Bound})))] (TVar (TypeVar {typevarId = 37, typevarKind = KCon E, typevarFlavour = Bound})) (TVar (TypeVar {typevarId = 38, typevarKind = KCon V, typevarFlavour = Bound})))) (1, 0), binderNameRange = (4, 8), binderRange = (4, 1)}, defRange = (1, 0), defVis = Public, defSort = fun, defInline = noinline, defDoc = "// handler for the `:effshow` effect"}
infer: App Var std/core/hnd/.hhandle False (1, 0)
Defaults: []

infer single .select-eshow
Def {defBinder = ValueBinder {binderName = .select-eshow, binderType = (), binderExpr = Ann (Lam [ValueBinder {binderName = hnd, binderType = Nothing, binderExpr = Nothing, binderNameRange = (1, 0), binderRange = (1, 0)}] (Case (Var hnd False (1, 0)) [Branch {branchPattern = PatCon .Hnd-effshow [(Nothing,PatVar (ValueBinder {binderName = fun-eshow, binderType = Nothing, binderExpr = PatWild (1, 0), binderNameRange = (1, 0), binderRange = (1, 0)}))] (1, 0) (1, 0), branchGuards = [Guard {guardTest = Var std/core/types/True False (1, 0), guardExpr = Var fun-eshow False (1, 0)}]}] (1, 0)) (1, 0)) (TForall [TypeVar {typevarId = 50, typevarKind = KCon V, typevarFlavour = Bound},TypeVar {typevarId = 51, typevarKind = KCon E, typevarFlavour = Bound},TypeVar {typevarId = 52, typevarKind = KCon V, typevarFlavour = Bound}] [] (TFun [(hnd,TApp (TCon (TypeCon {typeconName = samples/handlers/typeclass/show/generic/.hnd-effshow, typeconKind = KApp (KApp (KCon (->)) (KCon V)) (KApp (KApp (KCon (->)) (KCon E)) (KApp (KApp (KCon (->)) (KCon V)) (KCon V)))})) [TVar (TypeVar {typevarId = 50, typevarKind = KCon V, typevarFlavour = Bound}),TVar (TypeVar {typevarId = 51, typevarKind = KCon E, typevarFlavour = Bound}),TVar (TypeVar {typevarId = 52, typevarKind = KCon V, typevarFlavour = Bound})])] (TCon (TypeCon {typeconName = std/core/types/(<>), typeconKind = KCon E})) (TApp (TCon (TypeCon {typeconName = std/core/hnd/clause1, typeconKind = KApp (KApp (KCon (->)) (KCon V)) (KApp (KApp (KCon (->)) (KCon V)) (KApp (KApp (KCon (->)) (KApp (KApp (KCon (->)) (KCon E)) (KApp (KApp (KCon (->)) (KCon V)) (KCon V)))) (KApp (KApp (KCon (->)) (KCon E)) (KApp (KApp (KCon (->)) (KCon V)) (KCon V)))))})) [TVar (TypeVar {typevarId = 50, typevarKind = KCon V, typevarFlavour = Bound}),TCon (TypeCon {typeconName = std/core/types/string, typeconKind = KCon V}),TApp (TCon (TypeCon {typeconName = samples/handlers/typeclass/show/generic/.hnd-effshow, typeconKind = KApp (KApp (KCon (->)) (KCon V)) (KApp (KApp (KCon (->)) (KCon E)) (KApp (KApp (KCon (->)) (KCon V)) (KCon V)))})) [TVar (TypeVar {typevarId = 50, typevarKind = KCon V, typevarFlavour = Bound})],TVar (TypeVar {typevarId = 51, typevarKind = KCon E, typevarFlavour = Bound}),TVar (TypeVar {typevarId = 52, typevarKind = KCon V, typevarFlavour = Bound})]))) (1, 0), binderNameRange = (1, 0), binderRange = (1, 0)}, defRange = (1, 0), defVis = Public, defSort = fun, defInline = inline, defDoc = "// select `eshow` operation out of the `:effshow` effect handler"}
inferVar: constructor: std/core/types/True

infer single eshow
Def {defBinder = ValueBinder {binderName = eshow, binderType = (), binderExpr = Ann (Lam [ValueBinder {binderName = a, binderType = Nothing, binderExpr = Nothing, binderNameRange = (5,13), binderRange = (5,13)}] (App (Var std/core/hnd/.perform1 False (1, 0)) [(Nothing,App (Var std/core/hnd/.evv-at False (1, 0)) [(Nothing,App (Var std/core/ssize_t False (1, 0)) [(Nothing,Lit (LitInt 0 (1, 0)))] (1, 0))] (1, 0)),(Nothing,Var .select-eshow False (1, 0)),(Nothing,Var a False (5,13))] (1, 0)) (5, 7)) (TForall [TypeVar {typevarId = 58, typevarKind = KCon V, typevarFlavour = Bound}] [] (TFun [(a,TVar (TypeVar {typevarId = 58, typevarKind = KCon V, typevarFlavour = Bound}))] (TApp (TCon (TypeCon {typeconName = std/core/types/(<|>), typeconKind = KApp (KApp (KCon (->)) (KCon X)) (KApp (KApp (KCon (->)) (KCon E)) (KCon E))})) [TApp (TCon (TypeCon {typeconName = std/core/types/handled, typeconKind = KApp (KApp (KCon (->)) (KCon HX)) (KCon X)})) [TApp (TCon (TypeCon {typeconName = samples/handlers/typeclass/show/generic/effshow, typeconKind = KApp (KApp (KCon (->)) (KCon V)) (KCon HX)})) [TVar (TypeVar {typevarId = 58, typevarKind = KCon V, typevarFlavour = Bound})]],TCon (TypeCon {typeconName = std/core/types/(<>), typeconKind = KCon E})]) (TCon (TypeCon {typeconName = std/core/types/string, typeconKind = KCon V})))) (5, 7), binderNameRange = (5, 7), binderRange = (5, 7)}, defRange = (5, 7), defVis = Public, defSort = fun, defInline = inline, defDoc = "// call `eshow` operati-------------------------
core
-------------------------
module samples/handlers/typeclass/show/generic
// handlers for the `:effshow` effect
pub recursive type samples/handlers/typeclass/show/generic/.hnd-effshow <a,(e :: E),b> :: (V, E, V) -> V {
  pub con samples/handlers/typeclass/show/generic/.Hnd-effshow(fun-eshow: (std/core/hnd/clause1 :: (V, V, (E, V) -> V, E, V) -> V)<a,string,(
   samples/handlers/typeclass/show/generic/.hnd-effshow :: (V, E, V) -> V)<a>,(e :: E),b>) : forall<a,(e :: E),b> (fun-eshow : (std/core/hnd/clause1 :: (V, V, 
   (E, V) -> V, E, V) -> V)<a,string,(samples/handlers/typeclass/show/generic/.hnd-effshow :: (V, E, V) -> V)<a>,(e :: E),b>) -> (
   samples/handlers/typeclass/show/generic/.hnd-effshow :: (V, E, V) -> V)<a,(e :: E),b>;
};
// Here is our effect type / typeclass definition
// it has only one generic parameter, and thus is associated with only a single value 
// (value polymorphism via an effect).
pub type samples/handlers/typeclass/show/generic/effshow <a> :: V -> HX {
  con samples/handlers/typeclass/show/generic/Effshow<(e :: E),b>((samples/handlers/typeclass/show/generic/.hnd-effshow :: (V, E, V) -> V)<a,(e :: E),b>) : 
   forall<a,(e :: E),b> ((samples/handlers/typeclass/show/generic/.hnd-effshow :: (V, E, V) -> V)<a,(e :: E),b>) -> (
   samples/handlers/typeclass/show/generic/effshow :: V -> HX)<a>;
};
// runtime tag for the `:effshow` effect
pub val .tag-effshow : forall<a> std/core/hnd/htag<samples/handlers/typeclass/show/generic/.hnd-effshow<a>>
  = forall<a> std/core/hnd/.new-htag("effshow.typeclass_show_generic");
// handler for the `:effshow` effect
pub fun .handle-effshow : forall<a,b,e,c> (cfc : int32, hnd : samples/handlers/typeclass/show/generic/.hnd-effshow<a,e,c>, ret : (res : b) -> e c, action : () 
   -> <samples/handlers/typeclass/show/generic/effshow<a>|e> b) -> e c
  = forall<a,b,e,c> fn<e>(cfc: int32, hnd: samples/handlers/typeclass/show/generic/.hnd-effshow<a,e,c>, ret: (res : b) -> e c, action: () -> <
   samples/handlers/typeclass/show/generic/effshow<a>|e> b){
    std/core/hnd/.hhandle(samples/handlers/typeclass/show/generic/.tag-effshow, cfc, hnd, ret, action);
  };
// select `eshow` operation out of the `:effshow` effect handler
pub fun .select-eshow : forall<a,e,b> (^ hnd : samples/handlers/typeclass/show/generic/.hnd-effshow<a,e,b>) -> std/core/hnd/clause1<a,string,
   samples/handlers/typeclass/show/generic/.hnd-effshow<a>,e,b>
  = forall<a,e,b> fn(hnd: samples/handlers/typeclass/show/generic/.hnd-effshow<a,e,b>){
    (match (hnd) {
      ((.skip samples/handlers/typeclass/show/generic/.Hnd-effshow((fun-eshow: std/core/hnd/clause1<a,string,
   samples/handlers/typeclass/show/generic/.hnd-effshow<a>,e,b>)) : samples/handlers/typeclass/show/generic/.hnd-effshow<a,e,b> ) as .pat: (
   samples/handlers/typeclass/show/generic/.hnd-effshow<a,e,b>))
         -> fun-eshow;
    });
  };
// call `eshow` operation of the `:effshow` effect
pub fun eshow : forall<a> (a : a) -> (samples/handlers/typeclass/show/generic/effshow<a>) string
  = forall<a> fn<(samples/handlers/typeclass/show/generic/effshow<a>)>(a: a){
    std/core/hnd/.perform1((std/core/types/.open(std/core/hnd/.evv-at)((std/core/types/.open(std/core/ssize_t)(0)))), (forall<e,b> 
   samples/handlers/typeclass/show/generic/.select-eshow), a);
  };
pub val default_int : forall<a,e> (() -> <samples/handlers/typeclass/show/generic/effshow<int>|e> a) -> e a
  = forall<a,e> fn<e>(.action: () -> <samples/handlers/typeclass/show/generic/effshow<int>|e> a){
    samples/handlers/typeclass/show/generic/.handle-effshow((std/core/types/.open(std/core/int32)(1)), (samples/handlers/typeclass/show/generic/.Hnd-effshow((
   std/core/types/.open(std/core/hnd/clause-tail1)((fn<e>(a: int){
        (std/core/types/.open(std/core/show)(a));
      }))))), (fn<e>(.x: a){
        .x;
      }), .action);
  };
//  // Needs to unify with effshow<list<int>> to being handled, but with the handlers body requires effshow<a> instantiated with int
pub val default_list : forall<a,b,e> (() -> <samples/handlers/typeclass/show/generic/effshow<list<a>>,samples/handlers/typeclass/show/generic/effshow<a>|e> b) 
   -> <samples/handlers/typeclass/show/generic/effshow<a>|e> b
  = forall<a,b,e> fn<<samples/handlers/typeclass/show/generic/effshow<a>|e>>(.action: () -> <samples/handlers/typeclass/show/generic/effshow<list<a>>,
   samples/handlers/typeclass/show/generic/effshow<a>|e> b){
    samples/handlers/typeclass/show/generic/.handle-effshow((std/core/types/.open(std/core/int32)(1)), (samples/handlers/typeclass/show/generic/.Hnd-effshow((
   std/core/types/.open(std/core/hnd/clause-tail1)((fn<<samples/handlers/typeclass/show/generic/effshow<a>|e>>(a: list<a>){
        (std/core/types/.open((fn(xs: list<string>, sep: string){
          (match (xs) {
            ((std/core/Nil() : list<string> ) as .pat1: (list<string>))
               -> "";
            ((.skip std/core/Cons((x: string), (xx: list<string>)) : list<string> ) as .pat2: (list<string>))
               -> std/core/.lift16998-joinsep(sep, xx, x);
          });
        }))((std/core/map.5(a, (std/core/types/.open(samples/handlers/typeclass/show/generic/eshow)))), ", "));
      }))))), (fn<<samples/handlers/typeclass/show/generic/effshow<a>|e>>(.x: b){
        .x;
      }), .action);
  };
// In koka main is special cased to be wrapped in a function which provides a handler for the console effect
// In implementing these default handlers we could also make console / exception / async effects
//  no longer special cased by the compiler. 
pub fun main : () -> console ()
  = fn<console>(){
    samples/handlers/typeclass/show/generic/default_int((fn<<samples/handlers/typeclass/show/generic/effshow<int>,console>>(){
      (samples/handlers/typeclass/show/generic/default_list((fn<<samples/handlers/typeclass/show/generic/effshow<list<int>>,
   samples/handlers/typeclass/show/generic/effshow<int>,console>>(){
        (std/core/types/.open(std/core/printsln)((std/core/types/.open((fn<(samples/handlers/typeclass/show/generic/effshow<list<int>>)>(a: list<int>){
          (std/core/hnd/.perform1((std/core/types/.open(std/core/hnd/.evv-at)((std/core/types/.open(std/core/ssize_t)(0)))), (forall<e,a> 
   samples/handlers/typeclass/show/generic/.select-eshow), a));
        }))((std/core/Cons(0, (std/core/Cons(1, (std/core/Cons(2, std/core/Nil))))))))));
      })));
    }));
  };
-------------------------
linking: samples_handlers_typeclass_show_generic
created: .koka/v2.4.1/gcc-debug/samples_handlers_typeclass_show_generic
 
0, 1, 2
on of the `:effshow` effect"}
infer: App Var std/core/hnd/.perform1 False (1, 0)
infer: App Var std/core/hnd/.evv-at False (1, 0)
infer: App Var std/core/ssize_t False (1, 0)
Defaults: []
Defaults: []
Defaults: []

infer single default_int
Def {defBinder = ValueBinder {binderName = default_int, binderType = (), binderExpr = Handler {hndlrSort = normal, hndlrScope = HandlerNoScope, hndlrOverride = HandlerNoOverride, hndlrAllowMask = Nothing, hndlrEffect = Nothing, hndlrLocalPars = [], hndlrInitially = Nothing, hndlrReturn = Nothing, hndlrFinally = Nothing, hndlrBranches = [HandlerBranch {hbranchName = eshow, hbranchPars = [ValueBinder {binderName = a, binderType = Just (TCon (TypeCon {typeconName = std/core/types/int, typeconKind = KCon V})), binderExpr = (), binderNameRange = (18,13), binderRange = (18,13)}], hbranchExpr = Parens (App (Var show False (19, 7)) [(Nothing,Var a False (19, 5))] (19, 5))  (18,19), hbranchSort = fun, hbranchNameRange = (18, 7), hbranchPatRange = (18, 7)}], hndlrDeclRange = (17,19), hndlrRange = (17,19)}, binderNameRange = (17, 5), binderRange = (17, 1)}, defRange = (17, 1), defVis = Public, defSort = val, defInline = autoinline, defDoc = ""}
infer: App Var samples/handlers/typeclass/show/generic/.handle-effshow False (17,19)
infer: App Var std/core/int32 False (1, 0)
Defaults: []
infer: App Var samples/handlers/typeclass/show/generic/.Hnd-effshow False (17,19)
inferVar: constructor: samples/handlers/typeclass/show/generic/.Hnd-effshow
infer: App Var std/core/hnd/clause-tail1 False (17,19)
infer: App Var show False (19, 7)
InferApp from ArgsX
inferAppArgsFirst: function
Fixed show CtxFunTypes True [TCon (TypeCon {typeconName = std/core/types/int, typeconKind = KCon V})] []
Got Here
Left []
Got Here
Left []
Got Here
Left []
Got Here
Left []
Got Here
Left []
Got Here
Left []
Got Here
Left []
Got Here
Left []
Got Here
Left []
Got Here
Left []
Got Here
Right []
Expect
Defaults: []
Defaults: []
Defaults: []
Defaults: []

infer single default_list
Def {defBinder = ValueBinder {binderName = default_list, binderType = (), binderExpr = Handler {hndlrSort = normal, hndlrScope = HandlerNoScope, hndlrOverride = HandlerNoOverride, hndlrAllowMask = Nothing, hndlrEffect = Nothing, hndlrLocalPars = [], hndlrInitially = Nothing, hndlrReturn = Nothing, hndlrFinally = Nothing, hndlrBranches = [HandlerBranch {hbranchName = eshow, hbranchPars = [ValueBinder {binderName = a, binderType = Just (TApp (TCon (TypeCon {typeconName = std/core/list, typeconKind = KApp (KApp (KCon (->)) (KCon V)) (KCon V)})) [TVar (TypeVar {typevarId = 61, typevarKind = KCon V, typevarFlavour = Meta})]), binderExpr = (), binderNameRange = (23,13), binderRange = (23,13)}], hbranchExpr = Parens (App (Var join False (24,18)) [(Nothing,App (Var map False (24, 7)) [(Nothing,Var a False (24, 5)),(Nothing,Var eshow False (24,11))] (24, 5)),(Nothing,Lit (LitString ", " (24,23)))] (24, 5))  (23,31), hbranchSort = fun, hbranchNameRange = (23, 7), hbranchPatRange = (23, 7)}], hndlrDeclRange = (22,20), hndlrRange = (22,20)}, binderNameRange = (22, 5), binderRange = (22, 1)}, defRange = (22, 1), defVis = Public, defSort = val, defInline = autoinline, defDoc = "//  // Needs to unify with effshow<list<int>> to being handled, but with the handlers body requires effshow<a> instantiated with int\n"}
infer: App Var samples/handlers/typeclass/show/generic/.handle-effshow False (22,20)
infer: App Var std/core/int32 False (1, 0)
Defaults: []
infer: App Var samples/handlers/typeclass/show/generic/.Hnd-effshow False (22,20)
inferVar: constructor: samples/handlers/typeclass/show/generic/.Hnd-effshow
infer: App Var std/core/hnd/clause-tail1 False (22,20)
infer: App Var join False (24,18)
InferApp from ArgsX
infer: App Var map False (24, 7)
InferApp from ArgsX
inferAppArgsFirst: function
Fixed map CtxFunTypes True [TApp (TCon (TypeCon {typeconName = std/core/list, typeconKind = KApp (KApp (KCon (->)) (KCon V)) (KCon V)})) [TVar (TypeVar {typevarId = 61, typevarKind = KCon V, typevarFlavour = Meta})],TVar (TypeVar {typevarId = 274, typevarKind = KCon V, typevarFlavour = Meta})] []
Got Here
Left []
Got Here
Left []
Got Here
Left []
Got Here
Left []
Got Here
Left []
Got Here
Left []
Got Here
Left []
Got Here
Right []
Expect
Defaults: []
inferAppArgsFirst: function
Fixed join CtxFunTypes True [TApp (TCon (TypeCon {typeconName = std/core/list, typeconKind = KApp (KApp (KCon (->)) (KCon V)) (KCon V)})) [TCon (TypeCon {typeconName = std/core/types/string, typeconKind = KCon V})],TVar (TypeVar {typevarId = 249, typevarKind = KCon V, typevarFlavour = Meta})] []
Got Here
Left []
Left []
Got Here
Right []
Left []
Expect
infer: App Var map False (24, 7)
InferApp from ArgsX
inferAppArgsFirst: function
Fixed map CtxFunTypes True [TApp (TCon (TypeCon {typeconName = std/core/list, typeconKind = KApp (KApp (KCon (->)) (KCon V)) (KCon V)})) [TVar (TypeVar {typevarId = 61, typevarKind = KCon V, typevarFlavour = Meta})],TVar (TypeVar {typevarId = 389, typevarKind = KCon V, typevarFlavour = Meta})] []
Got Here
Left []
Got Here
Left []
Got Here
Left []
Got Here
Left []
Got Here
Left []
Got Here
Left []
Got Here
Left []
Got Here
Right []
Expect
Defaults: []
Defaults: []
Defaults: []
Defaults: []
Defaults: []

infer single main
Def {defBinder = ValueBinder {binderName = main, binderType = (), 
binderExpr = Ann (Lam [] (Parens 
(App (Var default_int False (30, 8)) 
      [(Nothing,
      Parens (Lam [] 
        (App (Var default_list False (31, 8)) 
          [(Nothing,Parens (Lam [] 
            (App (Var println False (32,19)) 
              [(Nothing,App (Var eshow False (32,13)) 
                [(Nothing,Parens (App (Var std/core/Cons False (32, 3)) 
                  [(Nothing,Lit (LitInt 0 (32, 4))),(Nothing,App (Var std/core/Cons False (32, 3)) 
                    [(Nothing,Lit (LitInt 1 (32, 7))),(Nothing,App (Var std/core/Cons False (32, 3)) 
                      [(Nothing,Lit (LitInt 2 (32,10))),(Nothing,Var std/core/Nil False (32,11))] (32, 3))] 
                      (32, 3))] (32, 3))  (32, 3))] (32, 3))] (32, 3)) (31, 3))  (32, 3))] 
                      (31, 3)) (30, 3))  (31, 3))] (30, 3))  (29,24)) (29, 1)) 
          (TFun [] (TApp (TCon (TypeCon {typeconName = std/core/types/(<|>), 
          typeconKind = KApp (KApp (KCon (->)) (KCon X)) (KApp (KApp (KCon (->)) (KCon E)) (KCon E))}))
           [TCon (TypeCon {typeconName = std/core/console, typeconKind = KCon X}),
           TCon (TypeCon {typeconName = std/core/types/(<>), typeconKind = KCon E})]) 
           (TCon (TypeCon {typeconName = std/core/types/(), typeconKind = KCon V}))) 
           (29, 1), binderNameRange = (29, 5), binderRange = (29, 5)}, defRange = (29, 1),
            defVis = Public, defSort = fun, defInline = autoinline, 
           defDoc = "// In koka main is special cased to be wrapped in a function which provides a handler for the console effect\n// In implementing these default handlers we could also make console / exception / async effects\n//  no longer special cased by the compiler. \n"}
infer: App Var default_int False (30, 8)
infer: App Var default_list False (31, 8)
infer: App Var println False (32,19)
InferApp from ArgsX
infer: App Var eshow False (32,13)
infer: App Var std/core/Cons False (32, 3)
inferVar: constructor: std/core/Cons
infer: App Var std/core/Cons False (32, 3)
inferVar: constructor: std/core/Cons
infer: App Var std/core/Cons False (32, 3)
inferVar: constructor: std/core/Cons
inferVar: constructor: std/core/Nil
Defaults: []
Defaults: []
Defaults: []
Defaults: []
inferAppArgsFirst: function
Fixed println CtxFunTypes True [TCon (TypeCon {typeconName = std/core/types/string, typeconKind = KCon V})] []
Got Here
Left []
Got Here
Left []
Got Here
Left []
Got Here
Left []
Got Here
Left []
Got Here
Right []
Expect
infer: App Var eshow False (32,13)
infer: App Var std/core/Cons False (32, 3)
inferVar: constructor: std/core/Cons
infer: App Var std/core/Cons False (32, 3)
inferVar: constructor: std/core/Cons
infer: App Var std/core/Cons False (32, 3)
inferVar: constructor: std/core/Cons
inferVar: constructor: std/core/Nil
Defaults: []
Defaults: []
Defaults: []
Defaults: []
Defaults: []
Defaults: []
Defaults: []
