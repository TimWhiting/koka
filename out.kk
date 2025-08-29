koka-3.2.2: unregistering (local file changes: src/Core/FlowAnalysis/Full/DMCFAR/DMCFA.hs)
koka> build (lib + exe) with ghc-9.6.6
Preprocessing library for koka-3.2.2..
Building library for koka-3.2.2..
[125 of 143] Compiling Core.FlowAnalysis.Full.DMCFAR.DMCFA [Source file changed]
Warning: The following header files listed in the main library's c-sources
will not be used: src/Platform/cpp/Platform/cconsole.h.
Header files should be in the 'include' or 'install-include' stanza.
See https://cabal.readthedocs.io/en/3.10/cabal-package.html#pkg-field-includes
Preprocessing executable 'koka' for koka-3.2.2..
Building executable 'koka' for koka-3.2.2..
[18 of 18] Linking .stack-work/dist/aarch64-osx/ghc-9.6.6/build/koka/koka [Library changed]
koka> copy/register
Installing library in /Users/timwhiting/koka/.stack-work/install/aarch64-osx/50e7567ab93459510bfd412b9898f4e9df3111e36f9d2dfd4eb8cba51d1770ee/9.6.6/lib/aarch64-osx-ghc-9.6.6/koka-3.2.2-8GBEfjISoFBMgz1sr3wgW
Installing executable koka in /Users/timwhiting/koka/.stack-work/install/aarch64-osx/50e7567ab93459510bfd412b9898f4e9df3111e36f9d2dfd4eb8cba51d1770ee/9.6.6/bin
Registering library for koka-3.2.2..
Evaluating: val _ : ()
      = @open(trace)("Example 22 - nondeterminism twice");
(fn(@action){
  ex2/@handle((@Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
      }))))), (fn(x){
      x;
    }), @action);
})((fn(){
  (@open((+))((@open(ex2)((Tuple2(1, 2)))), (@open(ex2)((Tuple2(1, 2))))));
})) basic-bench:138:[top]@[]
Evaluating: @open(trace)("Example 22 - nondeterminism twice") basic-bench:140:[top]@[]
Evaluating: trace basic-bench:227:[top]@[]
Extending store: BI@(227:[top]@[]) with std/core/debug/trace
Applying FApp {totalArgs = 1, leftArgs = [AppParam basic-bench:225 0 "Example 22 - nondeterminism twice"], resolvedArgs = [], parent = LetDef val _ : ();}
Evaluating: "Example 22 - nondeterminism twice" basic-bench:225:[top]@[]
Extending store: BI@(225:[top]@[]) with string -> "Example 22 - nondeterminism twice"
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(227:[top]@[])], parent = LetDef val _ : ();}
Applying: [] [BI@(227:[top]@[]),BI@(225:[top]@[])]
Applying function: BI@(227:[top]@[]) std/core/debug/trace
Applying primitive std/core/debug/trace
Extending store: BI@(140:[top]@[]) with Unit
Applying FLet {groupIdx = 0, numGroups = 1, bindingIdx = 0, numBindings = 1, name = _, resolved = [], parent = LamBody [] val _ : ()
      = @open(trace)("Example 22 - nondeterminism twice");
(fn(@action){
  ex2/@handle((@Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
      }))))), (fn(x){
      x;
    }), @action);
})((fn(){
  (@open((+))((@open(ex2)((Tuple2(1, 2)))), (@open(ex2)((Tuple2(1, 2))))));
}))}
Extending store: B@(_:[top]@[]) with Unit
Evaluating: (fn(@action){
  ex2/@handle((@Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
      }))))), (fn(x){
      x;
    }), @action);
})((fn(){
  (@open((+))((@open(ex2)((Tuple2(1, 2)))), (@open(ex2)((Tuple2(1, 2))))));
})) basic-bench:141:[top]@[]
Evaluating: fn(@action){
  ex2/@handle((@Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
      }))))), (fn(x){
      x;
    }), @action);
} basic-bench:142:[top]@[]
Extending store: BI@(142:[top]@[]) with AppLambda(fn(@action){
  ex2/@handle((@Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
      }))))), (fn(x){
      x;
    }), @action);
})
Applying FApp {totalArgs = 1, leftArgs = [AppParam basic-bench:143 0 fn(){
  @open((+))((@open(ex2)((Tuple2(1, 2)))), (@open(ex2)((Tuple2(1, 2)))));
}], resolvedArgs = [], parent = LetBody (fn(@action){
  ex2/@handle((@Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
      }))))), (fn(x){
      x;
    }), @action);
})((fn(){
  (@open((+))((@open(ex2)((Tuple2(1, 2)))), (@open(ex2)((Tuple2(1, 2))))));
}))}
Evaluating: fn(){
  @open((+))((@open(ex2)((Tuple2(1, 2)))), (@open(ex2)((Tuple2(1, 2)))));
} basic-bench:143:[top]@[]
Extending store: BI@(143:[top]@[]) with AppParam(fn(){
  @open((+))((@open(ex2)((Tuple2(1, 2)))), (@open(ex2)((Tuple2(1, 2)))));
})
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(142:[top]@[])], parent = LetBody (fn(@action){
  ex2/@handle((@Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
      }))))), (fn(x){
      x;
    }), @action);
})((fn(){
  (@open((+))((@open(ex2)((Tuple2(1, 2)))), (@open(ex2)((Tuple2(1, 2))))));
}))}
Applying: [] [BI@(142:[top]@[]),BI@(143:[top]@[])]
Applying function: BI@(142:[top]@[]) AppLambda(fn(@action){
  ex2/@handle((@Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
      }))))), (fn(x){
      x;
    }), @action);
})
Applying closure: AppLambda fn(@action){
  ex2/@handle((@Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
      }))))), (fn(x){
      x;
    }), @action);
}:[a141,top]@[] fvvs: fromList [] args [@action]
Extending store: B@(@action:[a141,top]@[]) with AppParam(fn(){
  @open((+))((@open(ex2)((Tuple2(1, 2)))), (@open(ex2)((Tuple2(1, 2)))));
})
Evaluating: ex2/@handle((@Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
      (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
    }))))), (fn(x){
    x;
  }), @action) basic-bench:144:[a141,top]@[]
Evaluating: ex2/@handle basic-bench:145:[a141,top]@[]
Evaluating: ex2/@handle basic-bench:149:[a141,top]@[]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex2/@tag, hnd, ret, action);
} basic-bench:19:[top]@[]
Extending store: BI@(19:[top]@[]) with DefNonRec(ex2/@handle)
Extending store: T@analysis/aac/basic-bench/#ex2/@handle with DefNonRec(ex2/@handle)
New result at Step (CEval ExprBasic ex2/@handle AI@(145:[a141,top]@[]) EndMKAddr [a141,top]@[])
N (CApply AI@(145:[a141,top]@[]) EndMKAddr T@analysis/aac/basic-bench/#ex2/@handle [])
Not in:
Next (fromList [CEval DefNonRec // handler for the effect `:ex2`
pub fun ex2/@handle : forall<a,e,b> (hnd : analysis/aac/basic-bench/ex2<e,b>, ret : (res : a) -> e b, action : () -> <analysis/aac/basic-bench/ex2|e> a) -> e b; EndKAddr T@analysis/aac/basic-bench/#ex2/@handle [top]@[]])
New:
N (CApply AI@(145:[a141,top]@[]) EndMKAddr T@analysis/aac/basic-bench/#ex2/@handle [])
Applying FApp {totalArgs = 3, leftArgs = [AppParam basic-bench:146 0 @Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
    (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
  })))),AppParam basic-bench:147 1 fn(x){
  x;
},AppParam basic-bench:148 2 @action], resolvedArgs = [], parent = LamBody [@action] ex2/@handle((@Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
      (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
    }))))), (fn(x){
    x;
  }), @action)}
Evaluating: @Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
    (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
  })))) basic-bench:146:[a141,top]@[]
Evaluating: @Hnd-ex2 basic-bench:150:[a141,top]@[]
Evaluating: @Hnd-ex2 basic-bench:153:[a141,top]@[]
Extending store: BI@(153:[a141,top]@[]) with @Hnd-ex2
Applying FApp {totalArgs = 2, leftArgs = [AppParam basic-bench:151 0 3,AppParam basic-bench:152 1 @open(clause-control1)((fn(a, resume){
  (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
}))], resolvedArgs = [], parent = AppParam basic-bench:146 0 @Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
    (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
  }))))}
Evaluating: 3 basic-bench:151:[a141,top]@[]
Extending store: BI@(151:[a141,top]@[]) with int -> 3
Applying FApp {totalArgs = 2, leftArgs = [AppParam basic-bench:152 1 @open(clause-control1)((fn(a, resume){
  (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
}))], resolvedArgs = [BI@(153:[a141,top]@[])], parent = AppParam basic-bench:146 0 @Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
    (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
  }))))}
Evaluating: @open(clause-control1)((fn(a, resume){
  (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
})) basic-bench:152:[a141,top]@[]
Evaluating: clause-control1 basic-bench:158:[a141,top]@[]
Evaluating: clause-control1 basic-bench:160:[a141,top]@[]
Extending store: BI@(160:[a141,top]@[]) with std/core/hnd/clause-control1
Applying FApp {totalArgs = 1, leftArgs = [AppParam basic-bench:156 0 fn(a, resume){
  @open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a)))));
}], resolvedArgs = [], parent = AppParam basic-bench:152 1 @open(clause-control1)((fn(a, resume){
  (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
}))}
Evaluating: fn(a, resume){
  @open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a)))));
} basic-bench:156:[a141,top]@[]
Extending store: BI@(156:[a141,top]@[]) with AppParam(fn(a, resume){
  @open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a)))));
})
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(160:[a141,top]@[])], parent = AppParam basic-bench:152 1 @open(clause-control1)((fn(a, resume){
  (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
}))}
Applying: [] [BI@(160:[a141,top]@[]),BI@(156:[a141,top]@[])]
Applying function: BI@(160:[a141,top]@[]) std/core/hnd/clause-control1
Applying primitive std/core/hnd/clause-control1
Extending store: CI@(@field-x1 152:[a141,top]@[]) with AppParam(fn(a, resume){
  @open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a)))));
})
Extending store: BI@(152:[a141,top]@[]) with std/core/hnd/clause-control1([(,CI@(@field-x1 152:[a141,top]@[]))])
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(153:[a141,top]@[]),BI@(151:[a141,top]@[])], parent = AppParam basic-bench:146 0 @Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
    (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
  }))))}
Applying: [] [BI@(153:[a141,top]@[]),BI@(151:[a141,top]@[]),BI@(152:[a141,top]@[])]
Applying function: BI@(153:[a141,top]@[]) @Hnd-ex2
Extending store: CI@(@cfc 146:[a141,top]@[]) with int -> 3
Extending store: CI@(@ctl-ex2 146:[a141,top]@[]) with std/core/hnd/clause-control1([(,CI@(@field-x1 152:[a141,top]@[]))])
Extending store: BI@(146:[a141,top]@[]) with analysis/aac/basic-bench/@Hnd-ex2([(@cfc,CI@(@cfc 146:[a141,top]@[])),(@ctl-ex2,CI@(@ctl-ex2 146:[a141,top]@[]))])
Applying FApp {totalArgs = 3, leftArgs = [AppParam basic-bench:147 1 fn(x){
  x;
},AppParam basic-bench:148 2 @action], resolvedArgs = [T@analysis/aac/basic-bench/#ex2/@handle], parent = LamBody [@action] ex2/@handle((@Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
      (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
    }))))), (fn(x){
    x;
  }), @action)}
Evaluating: fn(x){
  x;
} basic-bench:147:[a141,top]@[]
Extending store: BI@(147:[a141,top]@[]) with AppParam(fn(x){
  x;
})
Applying FApp {totalArgs = 3, leftArgs = [AppParam basic-bench:148 2 @action], resolvedArgs = [T@analysis/aac/basic-bench/#ex2/@handle,BI@(146:[a141,top]@[])], parent = LamBody [@action] ex2/@handle((@Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
      (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
    }))))), (fn(x){
    x;
  }), @action)}
Evaluating: @action basic-bench:148:[a141,top]@[]
Applying FApp {totalArgs = 3, leftArgs = [], resolvedArgs = [T@analysis/aac/basic-bench/#ex2/@handle,BI@(146:[a141,top]@[]),BI@(147:[a141,top]@[])], parent = LamBody [@action] ex2/@handle((@Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
      (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
    }))))), (fn(x){
    x;
  }), @action)}
Applying: [] [T@analysis/aac/basic-bench/#ex2/@handle,BI@(146:[a141,top]@[]),BI@(147:[a141,top]@[]),B@(@action:[a141,top]@[])]
Applying function: T@analysis/aac/basic-bench/#ex2/@handle DefNonRec(ex2/@handle)
Applying closure: DefNonRec // handler for the effect `:ex2`
pub fun ex2/@handle : forall<a,e,b> (hnd : analysis/aac/basic-bench/ex2<e,b>, ret : (res : a) -> e b, action : () -> <analysis/aac/basic-bench/ex2|e> a) -> e b;:[a144,a141,top]@[] fvvs: fromList [] args [hnd,ret,action]
Extending store: B@(hnd:[a144,a141,top]@[]) with analysis/aac/basic-bench/@Hnd-ex2([(@cfc,CI@(@cfc 146:[a141,top]@[])),(@ctl-ex2,CI@(@ctl-ex2 146:[a141,top]@[]))])
Extending store: B@(ret:[a144,a141,top]@[]) with AppParam(fn(x){
  x;
})
Extending store: B@(action:[a144,a141,top]@[]) with AppParam(fn(){
  @open((+))((@open(ex2)((Tuple2(1, 2)))), (@open(ex2)((Tuple2(1, 2)))));
})
Evaluating: @hhandle(ex2/@tag, hnd, ret, action) basic-bench:96:[a144,a141,top]@[]
Evaluating: @hhandle basic-bench:97:[a144,a141,top]@[]
Evaluating: @hhandle basic-bench:102:[a144,a141,top]@[]
Extending store: BI@(102:[a144,a141,top]@[]) with std/core/hnd/@hhandle
Applying FApp {totalArgs = 4, leftArgs = [AppParam basic-bench:98 0 ex2/@tag,AppParam basic-bench:99 1 hnd,AppParam basic-bench:100 2 ret,AppParam basic-bench:101 3 action], resolvedArgs = [], parent = LamBody [hnd,ret,action] @hhandle(ex2/@tag, hnd, ret, action)}
Evaluating: ex2/@tag basic-bench:98:[a144,a141,top]@[]
Evaluating: @open(@new-htag)("ex2@basic-bench") basic-bench:17:[top]@[]
Evaluating: @new-htag basic-bench:92:[top]@[]
Evaluating: @new-htag basic-bench:94:[top]@[]
Extending store: BI@(94:[top]@[]) with std/core/hnd/@new-htag
Applying FApp {totalArgs = 1, leftArgs = [AppParam basic-bench:90 0 "ex2@basic-bench"], resolvedArgs = [], parent = DefNonRec // runtime tag for the effect `:ex2`
pub val ex2/@tag : hnd/htag<analysis/aac/basic-bench/ex2>;}
Evaluating: "ex2@basic-bench" basic-bench:90:[top]@[]
Extending store: BI@(90:[top]@[]) with string -> "ex2@basic-bench"
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(94:[top]@[])], parent = DefNonRec // runtime tag for the effect `:ex2`
pub val ex2/@tag : hnd/htag<analysis/aac/basic-bench/ex2>;}
Applying: [] [BI@(94:[top]@[]),BI@(90:[top]@[])]
Applying function: BI@(94:[top]@[]) std/core/hnd/@new-htag
Applying primitive std/core/hnd/@new-htag
Extending store: CI@(@field-x1 17:[top]@[]) with string -> "ex2@basic-bench"
Extending store: BI@(17:[top]@[]) with std/core/hnd/@new-htag([(,CI@(@field-x1 17:[top]@[]))])
Extending store: T@analysis/aac/basic-bench/#ex2/@tag with std/core/hnd/@new-htag([(,CI@(@field-x1 17:[top]@[]))])
New result at Step (CEval AppParam basic-bench:98 0 ex2/@tag AI@(98:[a144,a141,top]@[]) EndMKAddr [a144,a141,top]@[])
N (CApply AI@(98:[a144,a141,top]@[]) EndMKAddr T@analysis/aac/basic-bench/#ex2/@tag [])
Not in:
Next (fromList [CEval DefNonRec // runtime tag for the effect `:ex2`
pub val ex2/@tag : hnd/htag<analysis/aac/basic-bench/ex2>; EndKAddr T@analysis/aac/basic-bench/#ex2/@tag [top]@[]])
New:
N (CApply AI@(98:[a144,a141,top]@[]) EndMKAddr T@analysis/aac/basic-bench/#ex2/@tag [])
Applying FApp {totalArgs = 4, leftArgs = [AppParam basic-bench:99 1 hnd,AppParam basic-bench:100 2 ret,AppParam basic-bench:101 3 action], resolvedArgs = [BI@(102:[a144,a141,top]@[])], parent = LamBody [hnd,ret,action] @hhandle(ex2/@tag, hnd, ret, action)}
Evaluating: hnd basic-bench:99:[a144,a141,top]@[]
Applying FApp {totalArgs = 4, leftArgs = [AppParam basic-bench:100 2 ret,AppParam basic-bench:101 3 action], resolvedArgs = [BI@(102:[a144,a141,top]@[]),T@analysis/aac/basic-bench/#ex2/@tag], parent = LamBody [hnd,ret,action] @hhandle(ex2/@tag, hnd, ret, action)}
Evaluating: ret basic-bench:100:[a144,a141,top]@[]
Applying FApp {totalArgs = 4, leftArgs = [AppParam basic-bench:101 3 action], resolvedArgs = [BI@(102:[a144,a141,top]@[]),T@analysis/aac/basic-bench/#ex2/@tag,B@(hnd:[a144,a141,top]@[])], parent = LamBody [hnd,ret,action] @hhandle(ex2/@tag, hnd, ret, action)}
Evaluating: action basic-bench:101:[a144,a141,top]@[]
Applying FApp {totalArgs = 4, leftArgs = [], resolvedArgs = [BI@(102:[a144,a141,top]@[]),T@analysis/aac/basic-bench/#ex2/@tag,B@(hnd:[a144,a141,top]@[]),B@(ret:[a144,a141,top]@[])], parent = LamBody [hnd,ret,action] @hhandle(ex2/@tag, hnd, ret, action)}
Applying: [] [BI@(102:[a144,a141,top]@[]),T@analysis/aac/basic-bench/#ex2/@tag,B@(hnd:[a144,a141,top]@[]),B@(ret:[a144,a141,top]@[]),B@(action:[a144,a141,top]@[])]
Applying function: BI@(102:[a144,a141,top]@[]) std/core/hnd/@hhandle
Applying primitive std/core/hnd/@hhandle
Evaluating: @open((+))((@open(ex2)((Tuple2(1, 2)))), (@open(ex2)((Tuple2(1, 2))))) basic-bench:192:[delim]@[(basic-bench:96,[a144,a141,top])]
Evaluating: (+) basic-bench:197:[delim]@[(basic-bench:96,[a144,a141,top])]
Evaluating: fn(x, y){
  @open(int-add)(x, y);
} int:241:[top]@[]
Extending store: BI@(241:[top]@[]) with DefNonRec((+))
Extending store: T@std/core/int/(+) with DefNonRec((+))
New result at Step (CEval AppParam basic-bench:197 0 (+) AI@(193:[delim]@[(basic-bench:96,[a144,a141,top])]) AI@(192:[a144,a141,top]@[]) [delim]@[(basic-bench:96,[a144,a141,top])])
N (CApply AI@(193:[delim]@[(basic-bench:96,[a144,a141,top])]) AI@(192:[a144,a141,top]@[]) T@std/core/int/(+) [(basic-bench:96,[a144,a141,top])])
Not in:
Next (fromList [CEval DefNonRec // Add two integers.
pub fip fun (+) : (x : int, y : int) -> int; EndKAddr T@std/core/int/(+) [top]@[]])
New:
N (CApply AI@(193:[delim]@[(basic-bench:96,[a144,a141,top])]) AI@(192:[a144,a141,top]@[]) T@std/core/int/(+) [(basic-bench:96,[a144,a141,top])])
Applying FApp {totalArgs = 2, leftArgs = [AppParam basic-bench:194 0 @open(ex2)((Tuple2(1, 2))),AppParam basic-bench:195 1 @open(ex2)((Tuple2(1, 2)))], resolvedArgs = [], parent = LamBody [] @open((+))((@open(ex2)((Tuple2(1, 2)))), (@open(ex2)((Tuple2(1, 2)))))}
Evaluating: @open(ex2)((Tuple2(1, 2))) basic-bench:194:[delim]@[(basic-bench:96,[a144,a141,top])]
Evaluating: ex2 basic-bench:203:[delim]@[(basic-bench:96,[a144,a141,top])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex2/@select), a);
} basic-bench:25:[top]@[]
Extending store: BI@(25:[top]@[]) with DefNonRec(ex2)
Extending store: T@analysis/aac/basic-bench/ex2 with DefNonRec(ex2)
New result at Step (CEval AppParam basic-bench:203 0 ex2 AI@(200:[delim]@[(basic-bench:96,[a144,a141,top])]) AI@(192:[a144,a141,top]@[]) [delim]@[(basic-bench:96,[a144,a141,top])])
N (CApply AI@(200:[delim]@[(basic-bench:96,[a144,a141,top])]) AI@(192:[a144,a141,top]@[]) T@analysis/aac/basic-bench/ex2 [(basic-bench:96,[a144,a141,top])])
Not in:
Next (fromList [CEval DefNonRec // Call the `ctl ex2` operation of the effect `:ex2`
pub fun ex2 : (a : (int, int)) -> analysis/aac/basic-bench/ex2 int; EndKAddr T@analysis/aac/basic-bench/ex2 [top]@[]])
New:
N (CApply AI@(200:[delim]@[(basic-bench:96,[a144,a141,top])]) AI@(192:[a144,a141,top]@[]) T@analysis/aac/basic-bench/ex2 [(basic-bench:96,[a144,a141,top])])
Applying FApp {totalArgs = 1, leftArgs = [AppParam basic-bench:201 0 Tuple2(1, 2)], resolvedArgs = [], parent = AppParam basic-bench:194 0 @open(ex2)((Tuple2(1, 2)))}
Evaluating: Tuple2(1, 2) basic-bench:201:[delim]@[(basic-bench:96,[a144,a141,top])]
Evaluating: Tuple2 basic-bench:206:[delim]@[(basic-bench:96,[a144,a141,top])]
Evaluating: Tuple2 basic-bench:209:[delim]@[(basic-bench:96,[a144,a141,top])]
Extending store: BI@(209:[delim]@[(basic-bench:96,[a144,a141,top])]) with Tuple2
Applying FApp {totalArgs = 2, leftArgs = [AppParam basic-bench:207 0 1,AppParam basic-bench:208 1 2], resolvedArgs = [], parent = AppParam basic-bench:201 0 Tuple2(1, 2)}
Evaluating: 1 basic-bench:207:[delim]@[(basic-bench:96,[a144,a141,top])]
Extending store: BI@(207:[delim]@[(basic-bench:96,[a144,a141,top])]) with int -> 1
Applying FApp {totalArgs = 2, leftArgs = [AppParam basic-bench:208 1 2], resolvedArgs = [BI@(209:[delim]@[(basic-bench:96,[a144,a141,top])])], parent = AppParam basic-bench:201 0 Tuple2(1, 2)}
Evaluating: 2 basic-bench:208:[delim]@[(basic-bench:96,[a144,a141,top])]
Extending store: BI@(208:[delim]@[(basic-bench:96,[a144,a141,top])]) with int -> 2
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(209:[delim]@[(basic-bench:96,[a144,a141,top])]),BI@(207:[delim]@[(basic-bench:96,[a144,a141,top])])], parent = AppParam basic-bench:201 0 Tuple2(1, 2)}
Applying: [] [BI@(209:[delim]@[(basic-bench:96,[a144,a141,top])]),BI@(207:[delim]@[(basic-bench:96,[a144,a141,top])]),BI@(208:[delim]@[(basic-bench:96,[a144,a141,top])])]
Applying function: BI@(209:[delim]@[(basic-bench:96,[a144,a141,top])]) Tuple2
Extending store: CI@(fst 201:[delim]@[(basic-bench:96,[a144,a141,top])]) with int -> 1
Extending store: CI@(snd 201:[delim]@[(basic-bench:96,[a144,a141,top])]) with int -> 2
Extending store: BI@(201:[delim]@[(basic-bench:96,[a144,a141,top])]) with std/core/types/Tuple2([(fst,CI@(fst 201:[delim]@[(basic-bench:96,[a144,a141,top])])),(snd,CI@(snd 201:[delim]@[(basic-bench:96,[a144,a141,top])]))])
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/aac/basic-bench/ex2], parent = AppParam basic-bench:194 0 @open(ex2)((Tuple2(1, 2)))}
Applying: [] [T@analysis/aac/basic-bench/ex2,BI@(201:[delim]@[(basic-bench:96,[a144,a141,top])])]
Applying function: T@analysis/aac/basic-bench/ex2 DefNonRec(ex2)
Applying closure: DefNonRec // Call the `ctl ex2` operation of the effect `:ex2`
pub fun ex2 : (a : (int, int)) -> analysis/aac/basic-bench/ex2 int;:[a194,delim]@[(basic-bench:96,[a144,a141,top])] fvvs: fromList [] args [a]
Extending store: B@(a:[a194,delim]@[(basic-bench:96,[a144,a141,top])]) with std/core/types/Tuple2([(fst,CI@(fst 201:[delim]@[(basic-bench:96,[a144,a141,top])])),(snd,CI@(snd 201:[delim]@[(basic-bench:96,[a144,a141,top])]))])
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex2/@select), a) basic-bench:117:[a194,delim]@[(basic-bench:96,[a144,a141,top])]
Evaluating: @perform1 basic-bench:118:[a194,delim]@[(basic-bench:96,[a144,a141,top])]
Evaluating: @perform1 basic-bench:122:[a194,delim]@[(basic-bench:96,[a144,a141,top])]
Extending store: BI@(122:[a194,delim]@[(basic-bench:96,[a144,a141,top])]) with std/core/hnd/@perform1
Applying FApp {totalArgs = 3, leftArgs = [AppParam basic-bench:119 0 @open(@evv-at)((@open(@make-ssize_t)(0))),AppParam basic-bench:120 1 forall<e,a> ex2/@select,AppParam basic-bench:121 2 a], resolvedArgs = [], parent = LamBody [a] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex2/@select), a)}
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) basic-bench:119:[a194,delim]@[(basic-bench:96,[a144,a141,top])]
Evaluating: @evv-at basic-bench:126:[a194,delim]@[(basic-bench:96,[a144,a141,top])]
Evaluating: @evv-at basic-bench:128:[a194,delim]@[(basic-bench:96,[a144,a141,top])]
Extending store: BI@(128:[a194,delim]@[(basic-bench:96,[a144,a141,top])]) with std/core/hnd/@evv-at
Applying FApp {totalArgs = 1, leftArgs = [AppParam basic-bench:124 0 @open(@make-ssize_t)(0)], resolvedArgs = [], parent = AppParam basic-bench:119 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Evaluating: @open(@make-ssize_t)(0) basic-bench:124:[a194,delim]@[(basic-bench:96,[a144,a141,top])]
Evaluating: @make-ssize_t basic-bench:132:[a194,delim]@[(basic-bench:96,[a144,a141,top])]
Extending store: BI@(132:[a194,delim]@[(basic-bench:96,[a144,a141,top])]) with std/core/types/@make-ssize_t
Applying FApp {totalArgs = 1, leftArgs = [AppParam basic-bench:130 0 0], resolvedArgs = [], parent = AppParam basic-bench:124 0 @open(@make-ssize_t)(0)}
Evaluating: 0 basic-bench:130:[a194,delim]@[(basic-bench:96,[a144,a141,top])]
Extending store: BI@(130:[a194,delim]@[(basic-bench:96,[a144,a141,top])]) with int -> 0
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(132:[a194,delim]@[(basic-bench:96,[a144,a141,top])])], parent = AppParam basic-bench:124 0 @open(@make-ssize_t)(0)}
Applying: [] [BI@(132:[a194,delim]@[(basic-bench:96,[a144,a141,top])]),BI@(130:[a194,delim]@[(basic-bench:96,[a144,a141,top])])]
Applying function: BI@(132:[a194,delim]@[(basic-bench:96,[a144,a141,top])]) std/core/types/@make-ssize_t
Applying primitive std/core/types/@make-ssize_t
Extending store: BI@(124:[a194,delim]@[(basic-bench:96,[a144,a141,top])]) with int -> 0
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(128:[a194,delim]@[(basic-bench:96,[a144,a141,top])])], parent = AppParam basic-bench:119 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Applying: [] [BI@(128:[a194,delim]@[(basic-bench:96,[a144,a141,top])]),BI@(124:[a194,delim]@[(basic-bench:96,[a144,a141,top])])]
Applying function: BI@(128:[a194,delim]@[(basic-bench:96,[a144,a141,top])]) std/core/hnd/@evv-at
Applying primitive std/core/hnd/@evv-at
Extending store: CI@(@field-x1 119:[a194,delim]@[(basic-bench:96,[a144,a141,top])]) with int -> 0
Extending store: BI@(119:[a194,delim]@[(basic-bench:96,[a144,a141,top])]) with std/core/hnd/@evv-at([(,CI@(@field-x1 119:[a194,delim]@[(basic-bench:96,[a144,a141,top])]))])
Applying FApp {totalArgs = 3, leftArgs = [AppParam basic-bench:120 1 forall<e,a> ex2/@select,AppParam basic-bench:121 2 a], resolvedArgs = [BI@(122:[a194,delim]@[(basic-bench:96,[a144,a141,top])])], parent = LamBody [a] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex2/@select), a)}
Evaluating: forall<e,a> ex2/@select basic-bench:120:[a194,delim]@[(basic-bench:96,[a144,a141,top])]
Evaluating: ex2/@select basic-bench:136:[a194,delim]@[(basic-bench:96,[a144,a141,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex2(_, (@ctl-ex2)) : analysis/aac/basic-bench/ex2<e,a> )
       -> @ctl-ex2;
  });
} basic-bench:23:[top]@[]
Extending store: BI@(23:[top]@[]) with DefNonRec(ex2/@select)
Extending store: T@analysis/aac/basic-bench/#ex2/@select with DefNonRec(ex2/@select)
New result at Step (CEval ExprBasic ex2/@select AI@(120:[a194,delim]@[(basic-bench:96,[a144,a141,top])]) AI@(192:[a144,a141,top]@[]) [a194,delim]@[(basic-bench:96,[a144,a141,top])])
N (CApply AI@(120:[a194,delim]@[(basic-bench:96,[a144,a141,top])]) AI@(192:[a144,a141,top]@[]) T@analysis/aac/basic-bench/#ex2/@select [(basic-bench:96,[a144,a141,top])])
Not in:
Next (fromList [CEval DefNonRec // select `ex2` operation out of effect `:ex2`
pub fun ex2/@select : forall<e,a> (^ hnd : analysis/aac/basic-bench/ex2<e,a>) -> hnd/clause1<(int, int),int,analysis/aac/basic-bench/ex2,e,a>; EndKAddr T@analysis/aac/basic-bench/#ex2/@select [top]@[]])
New:
N (CApply AI@(120:[a194,delim]@[(basic-bench:96,[a144,a141,top])]) AI@(192:[a144,a141,top]@[]) T@analysis/aac/basic-bench/#ex2/@select [(basic-bench:96,[a144,a141,top])])
Applying FApp {totalArgs = 3, leftArgs = [AppParam basic-bench:121 2 a], resolvedArgs = [BI@(122:[a194,delim]@[(basic-bench:96,[a144,a141,top])]),BI@(119:[a194,delim]@[(basic-bench:96,[a144,a141,top])])], parent = LamBody [a] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex2/@select), a)}
Evaluating: a basic-bench:121:[a194,delim]@[(basic-bench:96,[a144,a141,top])]
Applying FApp {totalArgs = 3, leftArgs = [], resolvedArgs = [BI@(122:[a194,delim]@[(basic-bench:96,[a144,a141,top])]),BI@(119:[a194,delim]@[(basic-bench:96,[a144,a141,top])]),T@analysis/aac/basic-bench/#ex2/@select], parent = LamBody [a] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex2/@select), a)}
Applying: [] [BI@(122:[a194,delim]@[(basic-bench:96,[a144,a141,top])]),BI@(119:[a194,delim]@[(basic-bench:96,[a144,a141,top])]),T@analysis/aac/basic-bench/#ex2/@select,B@(a:[a194,delim]@[(basic-bench:96,[a144,a141,top])])]
Applying function: BI@(122:[a194,delim]@[(basic-bench:96,[a144,a141,top])]) std/core/hnd/@perform1
Applying primitive std/core/hnd/@perform1
Matched [a144,a141,top]@[]
Extending store: B@(a:[a117,a144,a141]@[]) with std/core/types/Tuple2([(fst,CI@(fst 201:[delim]@[(basic-bench:96,[a144,a141,top])])),(snd,CI@(snd 201:[delim]@[(basic-bench:96,[a144,a141,top])]))])
Extending store: B@(resume:[a117,a144,a141]@[]) with Kont(analysis/aac/basic-bench/ex2,AI@(117:[a194,delim]@[(basic-bench:96,[a144,a141,top])]),[a117,a144,a141]@[],Handler {ops = B@(hnd:[a144,a141,top]@[]), ret = Just AppParam basic-bench:147 1 fn(x){
  x;
}, henv = BEnv (fromList [])})
Evaluating: @open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))) basic-bench:161:[a117,a144,a141]@[]
Evaluating: (+) basic-bench:166:[a117,a144,a141]@[]
New result at Step (CEval AppParam basic-bench:166 0 (+) AI@(162:[a117,a144,a141]@[]) EndMKAddr [a117,a144,a141]@[])
N (CApply AI@(162:[a117,a144,a141]@[]) EndMKAddr T@std/core/int/(+) [])
Not in:
Next (fromList [CEval DefNonRec // Add two integers.
pub fip fun (+) : (x : int, y : int) -> int; EndKAddr T@std/core/int/(+) [top]@[]])
New:
N (CApply AI@(162:[a117,a144,a141]@[]) EndMKAddr T@std/core/int/(+) [])
Applying FApp {totalArgs = 2, leftArgs = [AppParam basic-bench:163 0 resume((@open(tuple2/fst)(a))),AppParam basic-bench:164 1 resume((@open(tuple2/snd)(a)))], resolvedArgs = [], parent = LamBody [a,resume] @open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a)))))}
Evaluating: resume((@open(tuple2/fst)(a))) basic-bench:163:[a117,a144,a141]@[]
Evaluating: resume basic-bench:169:[a117,a144,a141]@[]
Applying FApp {totalArgs = 1, leftArgs = [AppParam basic-bench:170 0 @open(tuple2/fst)(a)], resolvedArgs = [], parent = AppParam basic-bench:163 0 resume((@open(tuple2/fst)(a)))}
Evaluating: @open(tuple2/fst)(a) basic-bench:170:[a117,a144,a141]@[]
Evaluating: tuple2/fst basic-bench:175:[a117,a144,a141]@[]
Evaluating: tuple2/fst basic-bench:177:[a117,a144,a141]@[]
Evaluating: forall<a,b> fn(tuple2){
  (match (tuple2) {
    (@skip Tuple2((@x), _) : (a, b) )
       -> @x;
  });
} types:316:[top]@[]
Extending store: BI@(316:[top]@[]) with DefNonRec(tuple2/fst)
Extending store: T@std/core/types/#tuple2/fst with DefNonRec(tuple2/fst)
New result at Step (CEval ExprBasic tuple2/fst AI@(172:[a117,a144,a141]@[]) EndMKAddr [a117,a144,a141]@[])
N (CApply AI@(172:[a117,a144,a141]@[]) EndMKAddr T@std/core/types/#tuple2/fst [])
Not in:
Next (fromList [CEval DefNonRec // Automatically generated. Retrieves the `fst` constructor field of the `:tuple2` type.
pub fun tuple2/fst : forall<a,b> (^ tuple2 : (a, b)) -> a; EndKAddr T@std/core/types/#tuple2/fst [top]@[]])
New:
N (CApply AI@(172:[a117,a144,a141]@[]) EndMKAddr T@std/core/types/#tuple2/fst [])
Applying FApp {totalArgs = 1, leftArgs = [AppParam basic-bench:173 0 a], resolvedArgs = [], parent = AppParam basic-bench:170 0 @open(tuple2/fst)(a)}
Evaluating: a basic-bench:173:[a117,a144,a141]@[]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@std/core/types/#tuple2/fst], parent = AppParam basic-bench:170 0 @open(tuple2/fst)(a)}
Applying: [] [T@std/core/types/#tuple2/fst,B@(a:[a117,a144,a141]@[])]
Applying function: T@std/core/types/#tuple2/fst DefNonRec(tuple2/fst)
Applying closure: DefNonRec // Automatically generated. Retrieves the `fst` constructor field of the `:tuple2` type.
pub fun tuple2/fst : forall<a,b> (^ tuple2 : (a, b)) -> a;:[a170,a117,a144]@[] fvvs: fromList [] args [tuple2]
Extending store: B@(tuple2:[a170,a117,a144]@[]) with std/core/types/Tuple2([(fst,CI@(fst 201:[delim]@[(basic-bench:96,[a144,a141,top])])),(snd,CI@(snd 201:[delim]@[(basic-bench:96,[a144,a141,top])]))])
Evaluating: match (tuple2) {
  (@skip Tuple2((@x), _) : (a, b) )
     -> @x;
} types:413:[a170,a117,a144]@[]
Evaluating: tuple2 types:414:[a170,a117,a144]@[]
Applying FScrut {parent = LamBody [tuple2] match (tuple2) {
  (@skip Tuple2((@x), _) : (a, b) )
     -> @x;
}, branches = [CaseBranch 0 (@skip std/core/types/Tuple2((@x), _) : (a, b) )
   -> @x;]}
Extending store: B@(@x:[a170,a117,a144]@[]) with int -> 1
Evaluating: @x types:415:[a170,a117,a144]@[]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(resume:[a117,a144,a141]@[])], parent = AppParam basic-bench:163 0 resume((@open(tuple2/fst)(a)))}
Applying: [] [B@(resume:[a117,a144,a141]@[]),B@(@x:[a170,a117,a144]@[])]
Applying function: B@(resume:[a117,a144,a141]@[]) Kont(analysis/aac/basic-bench/ex2,AI@(117:[a194,delim]@[(basic-bench:96,[a144,a141,top])]),[a117,a144,a141]@[],Handler {ops = B@(hnd:[a144,a141,top]@[]), ret = Just AppParam basic-bench:147 1 fn(x){
  x;
}, henv = BEnv (fromList [])})
Applying continuation basic-bench:163 rebinding fromList [a,resume]
Rebinding: fromList [a,resume] from [a117,a144,a141]@[] to [a163,a117,a144]@[]
Extending store: B@(a:[a163,a117,a144]@[]) with std/core/types/Tuple2([(fst,CI@(fst 201:[delim]@[(basic-bench:96,[a144,a141,top])])),(snd,CI@(snd 201:[delim]@[(basic-bench:96,[a144,a141,top])]))])
Extending store: B@(resume:[a163,a117,a144]@[]) with Kont(analysis/aac/basic-bench/ex2,AI@(117:[a194,delim]@[(basic-bench:96,[a144,a141,top])]),[a117,a144,a141]@[],Handler {ops = B@(hnd:[a144,a141,top]@[]), ret = Just AppParam basic-bench:147 1 fn(x){
  x;
}, henv = BEnv (fromList [])})
Applying FApp {totalArgs = 2, leftArgs = [AppParam basic-bench:195 1 @open(ex2)((Tuple2(1, 2)))], resolvedArgs = [T@std/core/int/(+)], parent = LamBody [] @open((+))((@open(ex2)((Tuple2(1, 2)))), (@open(ex2)((Tuple2(1, 2)))))}
Evaluating: @open(ex2)((Tuple2(1, 2))) basic-bench:195:[delim]@[(basic-bench:163,[a163,a117,a144])]
Evaluating: ex2 basic-bench:215:[delim]@[(basic-bench:163,[a163,a117,a144])]
New result at Step (CEval AppParam basic-bench:215 0 ex2 AI@(212:[delim]@[(basic-bench:163,[a163,a117,a144])]) AI@(163:[a163,a117,a144]@[]) [delim]@[(basic-bench:163,[a163,a117,a144])])
N (CApply AI@(212:[delim]@[(basic-bench:163,[a163,a117,a144])]) AI@(163:[a163,a117,a144]@[]) T@analysis/aac/basic-bench/ex2 [(basic-bench:163,[a163,a117,a144])])
Not in:
Next (fromList [CEval DefNonRec // Call the `ctl ex2` operation of the effect `:ex2`
pub fun ex2 : (a : (int, int)) -> analysis/aac/basic-bench/ex2 int; EndKAddr T@analysis/aac/basic-bench/ex2 [top]@[]])
New:
N (CApply AI@(212:[delim]@[(basic-bench:163,[a163,a117,a144])]) AI@(163:[a163,a117,a144]@[]) T@analysis/aac/basic-bench/ex2 [(basic-bench:163,[a163,a117,a144])])
Applying FApp {totalArgs = 1, leftArgs = [AppParam basic-bench:213 0 Tuple2(1, 2)], resolvedArgs = [], parent = AppParam basic-bench:195 1 @open(ex2)((Tuple2(1, 2)))}
Evaluating: Tuple2(1, 2) basic-bench:213:[delim]@[(basic-bench:163,[a163,a117,a144])]
Evaluating: Tuple2 basic-bench:218:[delim]@[(basic-bench:163,[a163,a117,a144])]
Evaluating: Tuple2 basic-bench:221:[delim]@[(basic-bench:163,[a163,a117,a144])]
Extending store: BI@(221:[delim]@[(basic-bench:163,[a163,a117,a144])]) with Tuple2
Applying FApp {totalArgs = 2, leftArgs = [AppParam basic-bench:219 0 1,AppParam basic-bench:220 1 2], resolvedArgs = [], parent = AppParam basic-bench:213 0 Tuple2(1, 2)}
Evaluating: 1 basic-bench:219:[delim]@[(basic-bench:163,[a163,a117,a144])]
Extending store: BI@(219:[delim]@[(basic-bench:163,[a163,a117,a144])]) with int -> 1
Applying FApp {totalArgs = 2, leftArgs = [AppParam basic-bench:220 1 2], resolvedArgs = [BI@(221:[delim]@[(basic-bench:163,[a163,a117,a144])])], parent = AppParam basic-bench:213 0 Tuple2(1, 2)}
Evaluating: 2 basic-bench:220:[delim]@[(basic-bench:163,[a163,a117,a144])]
Extending store: BI@(220:[delim]@[(basic-bench:163,[a163,a117,a144])]) with int -> 2
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(221:[delim]@[(basic-bench:163,[a163,a117,a144])]),BI@(219:[delim]@[(basic-bench:163,[a163,a117,a144])])], parent = AppParam basic-bench:213 0 Tuple2(1, 2)}
Applying: [] [BI@(221:[delim]@[(basic-bench:163,[a163,a117,a144])]),BI@(219:[delim]@[(basic-bench:163,[a163,a117,a144])]),BI@(220:[delim]@[(basic-bench:163,[a163,a117,a144])])]
Applying function: BI@(221:[delim]@[(basic-bench:163,[a163,a117,a144])]) Tuple2
Extending store: CI@(fst 213:[delim]@[(basic-bench:163,[a163,a117,a144])]) with int -> 1
Extending store: CI@(snd 213:[delim]@[(basic-bench:163,[a163,a117,a144])]) with int -> 2
Extending store: BI@(213:[delim]@[(basic-bench:163,[a163,a117,a144])]) with std/core/types/Tuple2([(fst,CI@(fst 213:[delim]@[(basic-bench:163,[a163,a117,a144])])),(snd,CI@(snd 213:[delim]@[(basic-bench:163,[a163,a117,a144])]))])
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/aac/basic-bench/ex2], parent = AppParam basic-bench:195 1 @open(ex2)((Tuple2(1, 2)))}
Applying: [] [T@analysis/aac/basic-bench/ex2,BI@(213:[delim]@[(basic-bench:163,[a163,a117,a144])])]
Applying function: T@analysis/aac/basic-bench/ex2 DefNonRec(ex2)
Applying closure: DefNonRec // Call the `ctl ex2` operation of the effect `:ex2`
pub fun ex2 : (a : (int, int)) -> analysis/aac/basic-bench/ex2 int;:[a195,delim]@[(basic-bench:163,[a163,a117,a144])] fvvs: fromList [] args [a]
Extending store: B@(a:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]) with std/core/types/Tuple2([(fst,CI@(fst 213:[delim]@[(basic-bench:163,[a163,a117,a144])])),(snd,CI@(snd 213:[delim]@[(basic-bench:163,[a163,a117,a144])]))])
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex2/@select), a) basic-bench:117:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]
Evaluating: @perform1 basic-bench:118:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]
Evaluating: @perform1 basic-bench:122:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]
Extending store: BI@(122:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]) with std/core/hnd/@perform1
Applying FApp {totalArgs = 3, leftArgs = [AppParam basic-bench:119 0 @open(@evv-at)((@open(@make-ssize_t)(0))),AppParam basic-bench:120 1 forall<e,a> ex2/@select,AppParam basic-bench:121 2 a], resolvedArgs = [], parent = LamBody [a] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex2/@select), a)}
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) basic-bench:119:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]
Evaluating: @evv-at basic-bench:126:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]
Evaluating: @evv-at basic-bench:128:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]
Extending store: BI@(128:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]) with std/core/hnd/@evv-at
Applying FApp {totalArgs = 1, leftArgs = [AppParam basic-bench:124 0 @open(@make-ssize_t)(0)], resolvedArgs = [], parent = AppParam basic-bench:119 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Evaluating: @open(@make-ssize_t)(0) basic-bench:124:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]
Evaluating: @make-ssize_t basic-bench:132:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]
Extending store: BI@(132:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]) with std/core/types/@make-ssize_t
Applying FApp {totalArgs = 1, leftArgs = [AppParam basic-bench:130 0 0], resolvedArgs = [], parent = AppParam basic-bench:124 0 @open(@make-ssize_t)(0)}
Evaluating: 0 basic-bench:130:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]
Extending store: BI@(130:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]) with int -> 0
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(132:[a195,delim]@[(basic-bench:163,[a163,a117,a144])])], parent = AppParam basic-bench:124 0 @open(@make-ssize_t)(0)}
Applying: [] [BI@(132:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]),BI@(130:[a195,delim]@[(basic-bench:163,[a163,a117,a144])])]
Applying function: BI@(132:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]) std/core/types/@make-ssize_t
Applying primitive std/core/types/@make-ssize_t
Extending store: BI@(124:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]) with int -> 0
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(128:[a195,delim]@[(basic-bench:163,[a163,a117,a144])])], parent = AppParam basic-bench:119 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Applying: [] [BI@(128:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]),BI@(124:[a195,delim]@[(basic-bench:163,[a163,a117,a144])])]
Applying function: BI@(128:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]) std/core/hnd/@evv-at
Applying primitive std/core/hnd/@evv-at
Extending store: CI@(@field-x1 119:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]) with int -> 0
Extending store: BI@(119:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]) with std/core/hnd/@evv-at([(,CI@(@field-x1 119:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]))])
Applying FApp {totalArgs = 3, leftArgs = [AppParam basic-bench:120 1 forall<e,a> ex2/@select,AppParam basic-bench:121 2 a], resolvedArgs = [BI@(122:[a195,delim]@[(basic-bench:163,[a163,a117,a144])])], parent = LamBody [a] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex2/@select), a)}
Evaluating: forall<e,a> ex2/@select basic-bench:120:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]
Evaluating: ex2/@select basic-bench:136:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]
New result at Step (CEval ExprBasic ex2/@select AI@(120:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]) AI@(163:[a163,a117,a144]@[]) [a195,delim]@[(basic-bench:163,[a163,a117,a144])])
N (CApply AI@(120:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]) AI@(163:[a163,a117,a144]@[]) T@analysis/aac/basic-bench/#ex2/@select [(basic-bench:163,[a163,a117,a144])])
Not in:
Next (fromList [CEval DefNonRec // select `ex2` operation out of effect `:ex2`
pub fun ex2/@select : forall<e,a> (^ hnd : analysis/aac/basic-bench/ex2<e,a>) -> hnd/clause1<(int, int),int,analysis/aac/basic-bench/ex2,e,a>; EndKAddr T@analysis/aac/basic-bench/#ex2/@select [top]@[]])
New:
N (CApply AI@(120:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]) AI@(163:[a163,a117,a144]@[]) T@analysis/aac/basic-bench/#ex2/@select [(basic-bench:163,[a163,a117,a144])])
Applying FApp {totalArgs = 3, leftArgs = [AppParam basic-bench:121 2 a], resolvedArgs = [BI@(122:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]),BI@(119:[a195,delim]@[(basic-bench:163,[a163,a117,a144])])], parent = LamBody [a] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex2/@select), a)}
Evaluating: a basic-bench:121:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]
Applying FApp {totalArgs = 3, leftArgs = [], resolvedArgs = [BI@(122:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]),BI@(119:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]),T@analysis/aac/basic-bench/#ex2/@select], parent = LamBody [a] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex2/@select), a)}
Applying: [] [BI@(122:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]),BI@(119:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]),T@analysis/aac/basic-bench/#ex2/@select,B@(a:[a195,delim]@[(basic-bench:163,[a163,a117,a144])])]
Applying function: BI@(122:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]) std/core/hnd/@perform1
Applying primitive std/core/hnd/@perform1
Matched [a163,a117,a144]@[]
Extending store: B@(a:[a117,a163,a117]@[]) with std/core/types/Tuple2([(fst,CI@(fst 213:[delim]@[(basic-bench:163,[a163,a117,a144])])),(snd,CI@(snd 213:[delim]@[(basic-bench:163,[a163,a117,a144])]))])
Extending store: B@(resume:[a117,a163,a117]@[]) with Kont(analysis/aac/basic-bench/ex2,AI@(117:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]),[a117,a163,a117]@[],Handler {ops = B@(hnd:[a144,a141,top]@[]), ret = Just AppParam basic-bench:147 1 fn(x){
  x;
}, henv = BEnv (fromList [a,resume])})
Evaluating: @open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))) basic-bench:161:[a117,a163,a117]@[]
Evaluating: (+) basic-bench:166:[a117,a163,a117]@[]
New result at Step (CEval AppParam basic-bench:166 0 (+) AI@(162:[a117,a163,a117]@[]) EndMKAddr [a117,a163,a117]@[])
N (CApply AI@(162:[a117,a163,a117]@[]) EndMKAddr T@std/core/int/(+) [])
Not in:
Next (fromList [CEval DefNonRec // Add two integers.
pub fip fun (+) : (x : int, y : int) -> int; EndKAddr T@std/core/int/(+) [top]@[]])
New:
N (CApply AI@(162:[a117,a163,a117]@[]) EndMKAddr T@std/core/int/(+) [])
Applying FApp {totalArgs = 2, leftArgs = [AppParam basic-bench:163 0 resume((@open(tuple2/fst)(a))),AppParam basic-bench:164 1 resume((@open(tuple2/snd)(a)))], resolvedArgs = [], parent = LamBody [a,resume] @open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a)))))}
Evaluating: resume((@open(tuple2/fst)(a))) basic-bench:163:[a117,a163,a117]@[]
Evaluating: resume basic-bench:169:[a117,a163,a117]@[]
Applying FApp {totalArgs = 1, leftArgs = [AppParam basic-bench:170 0 @open(tuple2/fst)(a)], resolvedArgs = [], parent = AppParam basic-bench:163 0 resume((@open(tuple2/fst)(a)))}
Evaluating: @open(tuple2/fst)(a) basic-bench:170:[a117,a163,a117]@[]
Evaluating: tuple2/fst basic-bench:175:[a117,a163,a117]@[]
Evaluating: tuple2/fst basic-bench:177:[a117,a163,a117]@[]
New result at Step (CEval ExprBasic tuple2/fst AI@(172:[a117,a163,a117]@[]) EndMKAddr [a117,a163,a117]@[])
N (CApply AI@(172:[a117,a163,a117]@[]) EndMKAddr T@std/core/types/#tuple2/fst [])
Not in:
Next (fromList [CEval DefNonRec // Automatically generated. Retrieves the `fst` constructor field of the `:tuple2` type.
pub fun tuple2/fst : forall<a,b> (^ tuple2 : (a, b)) -> a; EndKAddr T@std/core/types/#tuple2/fst [top]@[]])
New:
N (CApply AI@(172:[a117,a163,a117]@[]) EndMKAddr T@std/core/types/#tuple2/fst [])
Applying FApp {totalArgs = 1, leftArgs = [AppParam basic-bench:173 0 a], resolvedArgs = [], parent = AppParam basic-bench:170 0 @open(tuple2/fst)(a)}
Evaluating: a basic-bench:173:[a117,a163,a117]@[]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@std/core/types/#tuple2/fst], parent = AppParam basic-bench:170 0 @open(tuple2/fst)(a)}
Applying: [] [T@std/core/types/#tuple2/fst,B@(a:[a117,a163,a117]@[])]
Applying function: T@std/core/types/#tuple2/fst DefNonRec(tuple2/fst)
Applying closure: DefNonRec // Automatically generated. Retrieves the `fst` constructor field of the `:tuple2` type.
pub fun tuple2/fst : forall<a,b> (^ tuple2 : (a, b)) -> a;:[a170,a117,a163]@[] fvvs: fromList [] args [tuple2]
Extending store: B@(tuple2:[a170,a117,a163]@[]) with std/core/types/Tuple2([(fst,CI@(fst 213:[delim]@[(basic-bench:163,[a163,a117,a144])])),(snd,CI@(snd 213:[delim]@[(basic-bench:163,[a163,a117,a144])]))])
Evaluating: match (tuple2) {
  (@skip Tuple2((@x), _) : (a, b) )
     -> @x;
} types:413:[a170,a117,a163]@[]
Evaluating: tuple2 types:414:[a170,a117,a163]@[]
Applying FScrut {parent = LamBody [tuple2] match (tuple2) {
  (@skip Tuple2((@x), _) : (a, b) )
     -> @x;
}, branches = [CaseBranch 0 (@skip std/core/types/Tuple2((@x), _) : (a, b) )
   -> @x;]}
Extending store: B@(@x:[a170,a117,a163]@[]) with int -> 1
Evaluating: @x types:415:[a170,a117,a163]@[]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(resume:[a117,a163,a117]@[])], parent = AppParam basic-bench:163 0 resume((@open(tuple2/fst)(a)))}
Applying: [] [B@(resume:[a117,a163,a117]@[]),B@(@x:[a170,a117,a163]@[])]
Applying function: B@(resume:[a117,a163,a117]@[]) Kont(analysis/aac/basic-bench/ex2,AI@(117:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]),[a117,a163,a117]@[],Handler {ops = B@(hnd:[a144,a141,top]@[]), ret = Just AppParam basic-bench:147 1 fn(x){
  x;
}, henv = BEnv (fromList [a,resume])})
Applying continuation basic-bench:163 rebinding fromList [a,resume]
Rebinding: fromList [a,resume] from [a117,a163,a117]@[] to [a163,a117,a163]@[]
Extending store: B@(a:[a163,a117,a163]@[]) with std/core/types/Tuple2([(fst,CI@(fst 213:[delim]@[(basic-bench:163,[a163,a117,a144])])),(snd,CI@(snd 213:[delim]@[(basic-bench:163,[a163,a117,a144])]))])
Extending store: B@(resume:[a163,a117,a163]@[]) with Kont(analysis/aac/basic-bench/ex2,AI@(117:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]),[a117,a163,a117]@[],Handler {ops = B@(hnd:[a144,a141,top]@[]), ret = Just AppParam basic-bench:147 1 fn(x){
  x;
}, henv = BEnv (fromList [a,resume])})
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/int/(+),B@(@x:[a170,a117,a144]@[])], parent = LamBody [] @open((+))((@open(ex2)((Tuple2(1, 2)))), (@open(ex2)((Tuple2(1, 2)))))}
Applying: [] [T@std/core/int/(+),B@(@x:[a170,a117,a144]@[]),B@(@x:[a170,a117,a163]@[])]
Applying function: T@std/core/int/(+) DefNonRec((+))
Applying closure: DefNonRec // Add two integers.
pub fip fun (+) : (x : int, y : int) -> int;:[a192,delim]@[(basic-bench:163,[a163,a117,a163])] fvvs: fromList [] args [x,y]
Extending store: B@(x:[a192,delim]@[(basic-bench:163,[a163,a117,a163])]) with int -> 1
Extending store: B@(y:[a192,delim]@[(basic-bench:163,[a163,a117,a163])]) with int -> 1
Evaluating: @open(int-add)(x, y) int:416:[a192,delim]@[(basic-bench:163,[a163,a117,a163])]
Evaluating: int-add int:421:[a192,delim]@[(basic-bench:163,[a163,a117,a163])]
Extending store: BI@(421:[a192,delim]@[(basic-bench:163,[a163,a117,a163])]) with std/core/int/int-add
Applying FApp {totalArgs = 2, leftArgs = [AppParam int:418 0 x,AppParam int:419 1 y], resolvedArgs = [], parent = LamBody [x,y] @open(int-add)(x, y)}
Evaluating: x int:418:[a192,delim]@[(basic-bench:163,[a163,a117,a163])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam int:419 1 y], resolvedArgs = [BI@(421:[a192,delim]@[(basic-bench:163,[a163,a117,a163])])], parent = LamBody [x,y] @open(int-add)(x, y)}
Evaluating: y int:419:[a192,delim]@[(basic-bench:163,[a163,a117,a163])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(421:[a192,delim]@[(basic-bench:163,[a163,a117,a163])]),B@(x:[a192,delim]@[(basic-bench:163,[a163,a117,a163])])], parent = LamBody [x,y] @open(int-add)(x, y)}
Applying: [] [BI@(421:[a192,delim]@[(basic-bench:163,[a163,a117,a163])]),B@(x:[a192,delim]@[(basic-bench:163,[a163,a117,a163])]),B@(y:[a192,delim]@[(basic-bench:163,[a163,a117,a163])])]
Applying function: BI@(421:[a192,delim]@[(basic-bench:163,[a163,a117,a163])]) std/core/int/int-add
Applying primitive std/core/int/int-add
Extending store: BI@(416:[a192,delim]@[(basic-bench:163,[a163,a117,a163])]) with int -> 2
Applying FDollar {vaddr = B@(ret:[a144,a141,top]@[])}
Extending store: B@(x:[a163,a117,a163]@[]) with int -> 2
Evaluating: x basic-bench:189:[a163,a117,a163]@[]
Applying FApp {totalArgs = 2, leftArgs = [AppParam basic-bench:164 1 resume((@open(tuple2/snd)(a)))], resolvedArgs = [T@std/core/int/(+)], parent = LamBody [a,resume] @open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a)))))}
Evaluating: resume((@open(tuple2/snd)(a))) basic-bench:164:[a117,a163,a117]@[]
Evaluating: resume basic-bench:179:[a117,a163,a117]@[]
Applying FApp {totalArgs = 1, leftArgs = [AppParam basic-bench:180 0 @open(tuple2/snd)(a)], resolvedArgs = [], parent = AppParam basic-bench:164 1 resume((@open(tuple2/snd)(a)))}
Evaluating: @open(tuple2/snd)(a) basic-bench:180:[a117,a163,a117]@[]
Evaluating: tuple2/snd basic-bench:185:[a117,a163,a117]@[]
Evaluating: tuple2/snd basic-bench:187:[a117,a163,a117]@[]
Evaluating: forall<a,b> fn(tuple2){
  (match (tuple2) {
    (@skip Tuple2(_, (@x)) : (a, b) )
       -> @x;
  });
} types:318:[top]@[]
Extending store: BI@(318:[top]@[]) with DefNonRec(tuple2/snd)
Extending store: T@std/core/types/#tuple2/snd with DefNonRec(tuple2/snd)
New result at Step (CEval ExprBasic tuple2/snd AI@(182:[a117,a163,a117]@[]) EndMKAddr [a117,a163,a117]@[])
N (CApply AI@(182:[a117,a163,a117]@[]) EndMKAddr T@std/core/types/#tuple2/snd [])
Not in:
Next (fromList [CEval DefNonRec // Automatically generated. Retrieves the `snd` constructor field of the `:tuple2` type.
pub fun tuple2/snd : forall<a,b> (^ tuple2 : (a, b)) -> b; EndKAddr T@std/core/types/#tuple2/snd [top]@[]])
New:
N (CApply AI@(182:[a117,a163,a117]@[]) EndMKAddr T@std/core/types/#tuple2/snd [])
Applying FApp {totalArgs = 1, leftArgs = [AppParam basic-bench:183 0 a], resolvedArgs = [], parent = AppParam basic-bench:180 0 @open(tuple2/snd)(a)}
Evaluating: a basic-bench:183:[a117,a163,a117]@[]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@std/core/types/#tuple2/snd], parent = AppParam basic-bench:180 0 @open(tuple2/snd)(a)}
Applying: [] [T@std/core/types/#tuple2/snd,B@(a:[a117,a163,a117]@[])]
Applying function: T@std/core/types/#tuple2/snd DefNonRec(tuple2/snd)
Applying closure: DefNonRec // Automatically generated. Retrieves the `snd` constructor field of the `:tuple2` type.
pub fun tuple2/snd : forall<a,b> (^ tuple2 : (a, b)) -> b;:[a180,a117,a163]@[] fvvs: fromList [] args [tuple2]
Extending store: B@(tuple2:[a180,a117,a163]@[]) with std/core/types/Tuple2([(fst,CI@(fst 213:[delim]@[(basic-bench:163,[a163,a117,a144])])),(snd,CI@(snd 213:[delim]@[(basic-bench:163,[a163,a117,a144])]))])
Evaluating: match (tuple2) {
  (@skip Tuple2(_, (@x)) : (a, b) )
     -> @x;
} types:422:[a180,a117,a163]@[]
Evaluating: tuple2 types:423:[a180,a117,a163]@[]
Applying FScrut {parent = LamBody [tuple2] match (tuple2) {
  (@skip Tuple2(_, (@x)) : (a, b) )
     -> @x;
}, branches = [CaseBranch 0 (@skip std/core/types/Tuple2(_, (@x)) : (a, b) )
   -> @x;]}
Extending store: B@(@x:[a180,a117,a163]@[]) with int -> 2
Evaluating: @x types:424:[a180,a117,a163]@[]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(resume:[a117,a163,a117]@[])], parent = AppParam basic-bench:164 1 resume((@open(tuple2/snd)(a)))}
Applying: [] [B@(resume:[a117,a163,a117]@[]),B@(@x:[a180,a117,a163]@[])]
Applying function: B@(resume:[a117,a163,a117]@[]) Kont(analysis/aac/basic-bench/ex2,AI@(117:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]),[a117,a163,a117]@[],Handler {ops = B@(hnd:[a144,a141,top]@[]), ret = Just AppParam basic-bench:147 1 fn(x){
  x;
}, henv = BEnv (fromList [a,resume])})
Applying continuation basic-bench:164 rebinding fromList [a,resume]
Rebinding: fromList [a,resume] from [a117,a163,a117]@[] to [a164,a117,a163]@[]
Extending store: B@(a:[a164,a117,a163]@[]) with std/core/types/Tuple2([(fst,CI@(fst 213:[delim]@[(basic-bench:163,[a163,a117,a144])])),(snd,CI@(snd 213:[delim]@[(basic-bench:163,[a163,a117,a144])]))])
Extending store: B@(resume:[a164,a117,a163]@[]) with Kont(analysis/aac/basic-bench/ex2,AI@(117:[a195,delim]@[(basic-bench:163,[a163,a117,a144])]),[a117,a163,a117]@[],Handler {ops = B@(hnd:[a144,a141,top]@[]), ret = Just AppParam basic-bench:147 1 fn(x){
  x;
}, henv = BEnv (fromList [a,resume])})
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/int/(+),B@(@x:[a170,a117,a144]@[])], parent = LamBody [] @open((+))((@open(ex2)((Tuple2(1, 2)))), (@open(ex2)((Tuple2(1, 2)))))}
Applying: [] [T@std/core/int/(+),B@(@x:[a170,a117,a144]@[]),B@(@x:[a180,a117,a163]@[])]
Applying function: T@std/core/int/(+) DefNonRec((+))
Applying closure: DefNonRec // Add two integers.
pub fip fun (+) : (x : int, y : int) -> int;:[a192,delim]@[(basic-bench:164,[a164,a117,a163])] fvvs: fromList [] args [x,y]
Extending store: B@(x:[a192,delim]@[(basic-bench:164,[a164,a117,a163])]) with int -> 1
Extending store: B@(y:[a192,delim]@[(basic-bench:164,[a164,a117,a163])]) with int -> 2
Evaluating: @open(int-add)(x, y) int:416:[a192,delim]@[(basic-bench:164,[a164,a117,a163])]
Evaluating: int-add int:421:[a192,delim]@[(basic-bench:164,[a164,a117,a163])]
Extending store: BI@(421:[a192,delim]@[(basic-bench:164,[a164,a117,a163])]) with std/core/int/int-add
Applying FApp {totalArgs = 2, leftArgs = [AppParam int:418 0 x,AppParam int:419 1 y], resolvedArgs = [], parent = LamBody [x,y] @open(int-add)(x, y)}
Evaluating: x int:418:[a192,delim]@[(basic-bench:164,[a164,a117,a163])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam int:419 1 y], resolvedArgs = [BI@(421:[a192,delim]@[(basic-bench:164,[a164,a117,a163])])], parent = LamBody [x,y] @open(int-add)(x, y)}
Evaluating: y int:419:[a192,delim]@[(basic-bench:164,[a164,a117,a163])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(421:[a192,delim]@[(basic-bench:164,[a164,a117,a163])]),B@(x:[a192,delim]@[(basic-bench:164,[a164,a117,a163])])], parent = LamBody [x,y] @open(int-add)(x, y)}
Applying: [] [BI@(421:[a192,delim]@[(basic-bench:164,[a164,a117,a163])]),B@(x:[a192,delim]@[(basic-bench:164,[a164,a117,a163])]),B@(y:[a192,delim]@[(basic-bench:164,[a164,a117,a163])])]
Applying function: BI@(421:[a192,delim]@[(basic-bench:164,[a164,a117,a163])]) std/core/int/int-add
Applying primitive std/core/int/int-add
Extending store: BI@(416:[a192,delim]@[(basic-bench:164,[a164,a117,a163])]) with int -> 3
Applying FDollar {vaddr = B@(ret:[a144,a141,top]@[])}
Extending store: B@(x:[a164,a117,a163]@[]) with int -> 3
Evaluating: x basic-bench:189:[a164,a117,a163]@[]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/int/(+),B@(x:[a163,a117,a163]@[])], parent = LamBody [a,resume] @open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a)))))}
Applying: [] [T@std/core/int/(+),B@(x:[a163,a117,a163]@[]),B@(x:[a164,a117,a163]@[])]
Applying function: T@std/core/int/(+) DefNonRec((+))
Applying closure: DefNonRec // Add two integers.
pub fip fun (+) : (x : int, y : int) -> int;:[a161,a117,a163]@[] fvvs: fromList [] args [x,y]
Extending store: B@(x:[a161,a117,a163]@[]) with int -> 2
Extending store: B@(y:[a161,a117,a163]@[]) with int -> 3
Evaluating: @open(int-add)(x, y) int:416:[a161,a117,a163]@[]
Evaluating: int-add int:421:[a161,a117,a163]@[]
Extending store: BI@(421:[a161,a117,a163]@[]) with std/core/int/int-add
Applying FApp {totalArgs = 2, leftArgs = [AppParam int:418 0 x,AppParam int:419 1 y], resolvedArgs = [], parent = LamBody [x,y] @open(int-add)(x, y)}
Evaluating: x int:418:[a161,a117,a163]@[]
Applying FApp {totalArgs = 2, leftArgs = [AppParam int:419 1 y], resolvedArgs = [BI@(421:[a161,a117,a163]@[])], parent = LamBody [x,y] @open(int-add)(x, y)}
Evaluating: y int:419:[a161,a117,a163]@[]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(421:[a161,a117,a163]@[]),B@(x:[a161,a117,a163]@[])], parent = LamBody [x,y] @open(int-add)(x, y)}
Applying: [] [BI@(421:[a161,a117,a163]@[]),B@(x:[a161,a117,a163]@[]),B@(y:[a161,a117,a163]@[])]
Applying function: BI@(421:[a161,a117,a163]@[]) std/core/int/int-add
Applying primitive std/core/int/int-add
Extending store: BI@(416:[a161,a117,a163]@[]) with int -> 5
Applying FApp {totalArgs = 2, leftArgs = [AppParam basic-bench:164 1 resume((@open(tuple2/snd)(a)))], resolvedArgs = [T@std/core/int/(+)], parent = LamBody [a,resume] @open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a)))))}
Evaluating: resume((@open(tuple2/snd)(a))) basic-bench:164:[a117,a144,a141]@[]
Evaluating: resume basic-bench:179:[a117,a144,a141]@[]
Applying FApp {totalArgs = 1, leftArgs = [AppParam basic-bench:180 0 @open(tuple2/snd)(a)], resolvedArgs = [], parent = AppParam basic-bench:164 1 resume((@open(tuple2/snd)(a)))}
Evaluating: @open(tuple2/snd)(a) basic-bench:180:[a117,a144,a141]@[]
Evaluating: tuple2/snd basic-bench:185:[a117,a144,a141]@[]
Evaluating: tuple2/snd basic-bench:187:[a117,a144,a141]@[]
New result at Step (CEval ExprBasic tuple2/snd AI@(182:[a117,a144,a141]@[]) EndMKAddr [a117,a144,a141]@[])
N (CApply AI@(182:[a117,a144,a141]@[]) EndMKAddr T@std/core/types/#tuple2/snd [])
Not in:
Next (fromList [CEval DefNonRec // Automatically generated. Retrieves the `snd` constructor field of the `:tuple2` type.
pub fun tuple2/snd : forall<a,b> (^ tuple2 : (a, b)) -> b; EndKAddr T@std/core/types/#tuple2/snd [top]@[]])
New:
N (CApply AI@(182:[a117,a144,a141]@[]) EndMKAddr T@std/core/types/#tuple2/snd [])
Applying FApp {totalArgs = 1, leftArgs = [AppParam basic-bench:183 0 a], resolvedArgs = [], parent = AppParam basic-bench:180 0 @open(tuple2/snd)(a)}
Evaluating: a basic-bench:183:[a117,a144,a141]@[]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@std/core/types/#tuple2/snd], parent = AppParam basic-bench:180 0 @open(tuple2/snd)(a)}
Applying: [] [T@std/core/types/#tuple2/snd,B@(a:[a117,a144,a141]@[])]
Applying function: T@std/core/types/#tuple2/snd DefNonRec(tuple2/snd)
Applying closure: DefNonRec // Automatically generated. Retrieves the `snd` constructor field of the `:tuple2` type.
pub fun tuple2/snd : forall<a,b> (^ tuple2 : (a, b)) -> b;:[a180,a117,a144]@[] fvvs: fromList [] args [tuple2]
Extending store: B@(tuple2:[a180,a117,a144]@[]) with std/core/types/Tuple2([(fst,CI@(fst 201:[delim]@[(basic-bench:96,[a144,a141,top])])),(snd,CI@(snd 201:[delim]@[(basic-bench:96,[a144,a141,top])]))])
Evaluating: match (tuple2) {
  (@skip Tuple2(_, (@x)) : (a, b) )
     -> @x;
} types:422:[a180,a117,a144]@[]
Evaluating: tuple2 types:423:[a180,a117,a144]@[]
Applying FScrut {parent = LamBody [tuple2] match (tuple2) {
  (@skip Tuple2(_, (@x)) : (a, b) )
     -> @x;
}, branches = [CaseBranch 0 (@skip std/core/types/Tuple2(_, (@x)) : (a, b) )
   -> @x;]}
Extending store: B@(@x:[a180,a117,a144]@[]) with int -> 2
Evaluating: @x types:424:[a180,a117,a144]@[]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(resume:[a117,a144,a141]@[])], parent = AppParam basic-bench:164 1 resume((@open(tuple2/snd)(a)))}
Applying: [] [B@(resume:[a117,a144,a141]@[]),B@(@x:[a180,a117,a144]@[])]
Applying function: B@(resume:[a117,a144,a141]@[]) Kont(analysis/aac/basic-bench/ex2,AI@(117:[a194,delim]@[(basic-bench:96,[a144,a141,top])]),[a117,a144,a141]@[],Handler {ops = B@(hnd:[a144,a141,top]@[]), ret = Just AppParam basic-bench:147 1 fn(x){
  x;
}, henv = BEnv (fromList [])})
Applying continuation basic-bench:164 rebinding fromList [a,resume]
Rebinding: fromList [a,resume] from [a117,a144,a141]@[] to [a164,a117,a144]@[]
Extending store: B@(a:[a164,a117,a144]@[]) with std/core/types/Tuple2([(fst,CI@(fst 201:[delim]@[(basic-bench:96,[a144,a141,top])])),(snd,CI@(snd 201:[delim]@[(basic-bench:96,[a144,a141,top])]))])
Extending store: B@(resume:[a164,a117,a144]@[]) with Kont(analysis/aac/basic-bench/ex2,AI@(117:[a194,delim]@[(basic-bench:96,[a144,a141,top])]),[a117,a144,a141]@[],Handler {ops = B@(hnd:[a144,a141,top]@[]), ret = Just AppParam basic-bench:147 1 fn(x){
  x;
}, henv = BEnv (fromList [])})
Applying FApp {totalArgs = 2, leftArgs = [AppParam basic-bench:195 1 @open(ex2)((Tuple2(1, 2)))], resolvedArgs = [T@std/core/int/(+)], parent = LamBody [] @open((+))((@open(ex2)((Tuple2(1, 2)))), (@open(ex2)((Tuple2(1, 2)))))}
Evaluating: @open(ex2)((Tuple2(1, 2))) basic-bench:195:[delim]@[(basic-bench:164,[a164,a117,a144])]
Evaluating: ex2 basic-bench:215:[delim]@[(basic-bench:164,[a164,a117,a144])]
New result at Step (CEval AppParam basic-bench:215 0 ex2 AI@(212:[delim]@[(basic-bench:164,[a164,a117,a144])]) AI@(164:[a164,a117,a144]@[]) [delim]@[(basic-bench:164,[a164,a117,a144])])
N (CApply AI@(212:[delim]@[(basic-bench:164,[a164,a117,a144])]) AI@(164:[a164,a117,a144]@[]) T@analysis/aac/basic-bench/ex2 [(basic-bench:164,[a164,a117,a144])])
Not in:
Next (fromList [CEval DefNonRec // Call the `ctl ex2` operation of the effect `:ex2`
pub fun ex2 : (a : (int, int)) -> analysis/aac/basic-bench/ex2 int; EndKAddr T@analysis/aac/basic-bench/ex2 [top]@[]])
New:
N (CApply AI@(212:[delim]@[(basic-bench:164,[a164,a117,a144])]) AI@(164:[a164,a117,a144]@[]) T@analysis/aac/basic-bench/ex2 [(basic-bench:164,[a164,a117,a144])])
Applying FApp {totalArgs = 1, leftArgs = [AppParam basic-bench:213 0 Tuple2(1, 2)], resolvedArgs = [], parent = AppParam basic-bench:195 1 @open(ex2)((Tuple2(1, 2)))}
Evaluating: Tuple2(1, 2) basic-bench:213:[delim]@[(basic-bench:164,[a164,a117,a144])]
Evaluating: Tuple2 basic-bench:218:[delim]@[(basic-bench:164,[a164,a117,a144])]
Evaluating: Tuple2 basic-bench:221:[delim]@[(basic-bench:164,[a164,a117,a144])]
Extending store: BI@(221:[delim]@[(basic-bench:164,[a164,a117,a144])]) with Tuple2
Applying FApp {totalArgs = 2, leftArgs = [AppParam basic-bench:219 0 1,AppParam basic-bench:220 1 2], resolvedArgs = [], parent = AppParam basic-bench:213 0 Tuple2(1, 2)}
Evaluating: 1 basic-bench:219:[delim]@[(basic-bench:164,[a164,a117,a144])]
Extending store: BI@(219:[delim]@[(basic-bench:164,[a164,a117,a144])]) with int -> 1
Applying FApp {totalArgs = 2, leftArgs = [AppParam basic-bench:220 1 2], resolvedArgs = [BI@(221:[delim]@[(basic-bench:164,[a164,a117,a144])])], parent = AppParam basic-bench:213 0 Tuple2(1, 2)}
Evaluating: 2 basic-bench:220:[delim]@[(basic-bench:164,[a164,a117,a144])]
Extending store: BI@(220:[delim]@[(basic-bench:164,[a164,a117,a144])]) with int -> 2
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(221:[delim]@[(basic-bench:164,[a164,a117,a144])]),BI@(219:[delim]@[(basic-bench:164,[a164,a117,a144])])], parent = AppParam basic-bench:213 0 Tuple2(1, 2)}
Applying: [] [BI@(221:[delim]@[(basic-bench:164,[a164,a117,a144])]),BI@(219:[delim]@[(basic-bench:164,[a164,a117,a144])]),BI@(220:[delim]@[(basic-bench:164,[a164,a117,a144])])]
Applying function: BI@(221:[delim]@[(basic-bench:164,[a164,a117,a144])]) Tuple2
Extending store: CI@(fst 213:[delim]@[(basic-bench:164,[a164,a117,a144])]) with int -> 1
Extending store: CI@(snd 213:[delim]@[(basic-bench:164,[a164,a117,a144])]) with int -> 2
Extending store: BI@(213:[delim]@[(basic-bench:164,[a164,a117,a144])]) with std/core/types/Tuple2([(fst,CI@(fst 213:[delim]@[(basic-bench:164,[a164,a117,a144])])),(snd,CI@(snd 213:[delim]@[(basic-bench:164,[a164,a117,a144])]))])
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/aac/basic-bench/ex2], parent = AppParam basic-bench:195 1 @open(ex2)((Tuple2(1, 2)))}
Applying: [] [T@analysis/aac/basic-bench/ex2,BI@(213:[delim]@[(basic-bench:164,[a164,a117,a144])])]
Applying function: T@analysis/aac/basic-bench/ex2 DefNonRec(ex2)
Applying closure: DefNonRec // Call the `ctl ex2` operation of the effect `:ex2`
pub fun ex2 : (a : (int, int)) -> analysis/aac/basic-bench/ex2 int;:[a195,delim]@[(basic-bench:164,[a164,a117,a144])] fvvs: fromList [] args [a]
Extending store: B@(a:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]) with std/core/types/Tuple2([(fst,CI@(fst 213:[delim]@[(basic-bench:164,[a164,a117,a144])])),(snd,CI@(snd 213:[delim]@[(basic-bench:164,[a164,a117,a144])]))])
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex2/@select), a) basic-bench:117:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]
Evaluating: @perform1 basic-bench:118:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]
Evaluating: @perform1 basic-bench:122:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]
Extending store: BI@(122:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]) with std/core/hnd/@perform1
Applying FApp {totalArgs = 3, leftArgs = [AppParam basic-bench:119 0 @open(@evv-at)((@open(@make-ssize_t)(0))),AppParam basic-bench:120 1 forall<e,a> ex2/@select,AppParam basic-bench:121 2 a], resolvedArgs = [], parent = LamBody [a] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex2/@select), a)}
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) basic-bench:119:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]
Evaluating: @evv-at basic-bench:126:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]
Evaluating: @evv-at basic-bench:128:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]
Extending store: BI@(128:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]) with std/core/hnd/@evv-at
Applying FApp {totalArgs = 1, leftArgs = [AppParam basic-bench:124 0 @open(@make-ssize_t)(0)], resolvedArgs = [], parent = AppParam basic-bench:119 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Evaluating: @open(@make-ssize_t)(0) basic-bench:124:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]
Evaluating: @make-ssize_t basic-bench:132:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]
Extending store: BI@(132:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]) with std/core/types/@make-ssize_t
Applying FApp {totalArgs = 1, leftArgs = [AppParam basic-bench:130 0 0], resolvedArgs = [], parent = AppParam basic-bench:124 0 @open(@make-ssize_t)(0)}
Evaluating: 0 basic-bench:130:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]
Extending store: BI@(130:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]) with int -> 0
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(132:[a195,delim]@[(basic-bench:164,[a164,a117,a144])])], parent = AppParam basic-bench:124 0 @open(@make-ssize_t)(0)}
Applying: [] [BI@(132:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]),BI@(130:[a195,delim]@[(basic-bench:164,[a164,a117,a144])])]
Applying function: BI@(132:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]) std/core/types/@make-ssize_t
Applying primitive std/core/types/@make-ssize_t
Extending store: BI@(124:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]) with int -> 0
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(128:[a195,delim]@[(basic-bench:164,[a164,a117,a144])])], parent = AppParam basic-bench:119 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Applying: [] [BI@(128:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]),BI@(124:[a195,delim]@[(basic-bench:164,[a164,a117,a144])])]
Applying function: BI@(128:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]) std/core/hnd/@evv-at
Applying primitive std/core/hnd/@evv-at
Extending store: CI@(@field-x1 119:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]) with int -> 0
Extending store: BI@(119:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]) with std/core/hnd/@evv-at([(,CI@(@field-x1 119:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]))])
Applying FApp {totalArgs = 3, leftArgs = [AppParam basic-bench:120 1 forall<e,a> ex2/@select,AppParam basic-bench:121 2 a], resolvedArgs = [BI@(122:[a195,delim]@[(basic-bench:164,[a164,a117,a144])])], parent = LamBody [a] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex2/@select), a)}
Evaluating: forall<e,a> ex2/@select basic-bench:120:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]
Evaluating: ex2/@select basic-bench:136:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]
New result at Step (CEval ExprBasic ex2/@select AI@(120:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]) AI@(164:[a164,a117,a144]@[]) [a195,delim]@[(basic-bench:164,[a164,a117,a144])])
N (CApply AI@(120:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]) AI@(164:[a164,a117,a144]@[]) T@analysis/aac/basic-bench/#ex2/@select [(basic-bench:164,[a164,a117,a144])])
Not in:
Next (fromList [CEval DefNonRec // select `ex2` operation out of effect `:ex2`
pub fun ex2/@select : forall<e,a> (^ hnd : analysis/aac/basic-bench/ex2<e,a>) -> hnd/clause1<(int, int),int,analysis/aac/basic-bench/ex2,e,a>; EndKAddr T@analysis/aac/basic-bench/#ex2/@select [top]@[]])
New:
N (CApply AI@(120:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]) AI@(164:[a164,a117,a144]@[]) T@analysis/aac/basic-bench/#ex2/@select [(basic-bench:164,[a164,a117,a144])])
Applying FApp {totalArgs = 3, leftArgs = [AppParam basic-bench:121 2 a], resolvedArgs = [BI@(122:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]),BI@(119:[a195,delim]@[(basic-bench:164,[a164,a117,a144])])], parent = LamBody [a] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex2/@select), a)}
Evaluating: a basic-bench:121:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]
Applying FApp {totalArgs = 3, leftArgs = [], resolvedArgs = [BI@(122:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]),BI@(119:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]),T@analysis/aac/basic-bench/#ex2/@select], parent = LamBody [a] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex2/@select), a)}
Applying: [] [BI@(122:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]),BI@(119:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]),T@analysis/aac/basic-bench/#ex2/@select,B@(a:[a195,delim]@[(basic-bench:164,[a164,a117,a144])])]
Applying function: BI@(122:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]) std/core/hnd/@perform1
Applying primitive std/core/hnd/@perform1
Matched [a164,a117,a144]@[]
Extending store: B@(a:[a117,a164,a117]@[]) with std/core/types/Tuple2([(fst,CI@(fst 213:[delim]@[(basic-bench:164,[a164,a117,a144])])),(snd,CI@(snd 213:[delim]@[(basic-bench:164,[a164,a117,a144])]))])
Extending store: B@(resume:[a117,a164,a117]@[]) with Kont(analysis/aac/basic-bench/ex2,AI@(117:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]),[a117,a164,a117]@[],Handler {ops = B@(hnd:[a144,a141,top]@[]), ret = Just AppParam basic-bench:147 1 fn(x){
  x;
}, henv = BEnv (fromList [a,resume])})
Evaluating: @open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))) basic-bench:161:[a117,a164,a117]@[]
Evaluating: (+) basic-bench:166:[a117,a164,a117]@[]
New result at Step (CEval AppParam basic-bench:166 0 (+) AI@(162:[a117,a164,a117]@[]) EndMKAddr [a117,a164,a117]@[])
N (CApply AI@(162:[a117,a164,a117]@[]) EndMKAddr T@std/core/int/(+) [])
Not in:
Next (fromList [CEval DefNonRec // Add two integers.
pub fip fun (+) : (x : int, y : int) -> int; EndKAddr T@std/core/int/(+) [top]@[]])
New:
N (CApply AI@(162:[a117,a164,a117]@[]) EndMKAddr T@std/core/int/(+) [])
Applying FApp {totalArgs = 2, leftArgs = [AppParam basic-bench:163 0 resume((@open(tuple2/fst)(a))),AppParam basic-bench:164 1 resume((@open(tuple2/snd)(a)))], resolvedArgs = [], parent = LamBody [a,resume] @open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a)))))}
Evaluating: resume((@open(tuple2/fst)(a))) basic-bench:163:[a117,a164,a117]@[]
Evaluating: resume basic-bench:169:[a117,a164,a117]@[]
Applying FApp {totalArgs = 1, leftArgs = [AppParam basic-bench:170 0 @open(tuple2/fst)(a)], resolvedArgs = [], parent = AppParam basic-bench:163 0 resume((@open(tuple2/fst)(a)))}
Evaluating: @open(tuple2/fst)(a) basic-bench:170:[a117,a164,a117]@[]
Evaluating: tuple2/fst basic-bench:175:[a117,a164,a117]@[]
Evaluating: tuple2/fst basic-bench:177:[a117,a164,a117]@[]
New result at Step (CEval ExprBasic tuple2/fst AI@(172:[a117,a164,a117]@[]) EndMKAddr [a117,a164,a117]@[])
N (CApply AI@(172:[a117,a164,a117]@[]) EndMKAddr T@std/core/types/#tuple2/fst [])
Not in:
Next (fromList [CEval DefNonRec // Automatically generated. Retrieves the `fst` constructor field of the `:tuple2` type.
pub fun tuple2/fst : forall<a,b> (^ tuple2 : (a, b)) -> a; EndKAddr T@std/core/types/#tuple2/fst [top]@[]])
New:
N (CApply AI@(172:[a117,a164,a117]@[]) EndMKAddr T@std/core/types/#tuple2/fst [])
Applying FApp {totalArgs = 1, leftArgs = [AppParam basic-bench:173 0 a], resolvedArgs = [], parent = AppParam basic-bench:170 0 @open(tuple2/fst)(a)}
Evaluating: a basic-bench:173:[a117,a164,a117]@[]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@std/core/types/#tuple2/fst], parent = AppParam basic-bench:170 0 @open(tuple2/fst)(a)}
Applying: [] [T@std/core/types/#tuple2/fst,B@(a:[a117,a164,a117]@[])]
Applying function: T@std/core/types/#tuple2/fst DefNonRec(tuple2/fst)
Applying closure: DefNonRec // Automatically generated. Retrieves the `fst` constructor field of the `:tuple2` type.
pub fun tuple2/fst : forall<a,b> (^ tuple2 : (a, b)) -> a;:[a170,a117,a164]@[] fvvs: fromList [] args [tuple2]
Extending store: B@(tuple2:[a170,a117,a164]@[]) with std/core/types/Tuple2([(fst,CI@(fst 213:[delim]@[(basic-bench:164,[a164,a117,a144])])),(snd,CI@(snd 213:[delim]@[(basic-bench:164,[a164,a117,a144])]))])
Evaluating: match (tuple2) {
  (@skip Tuple2((@x), _) : (a, b) )
     -> @x;
} types:413:[a170,a117,a164]@[]
Evaluating: tuple2 types:414:[a170,a117,a164]@[]
Applying FScrut {parent = LamBody [tuple2] match (tuple2) {
  (@skip Tuple2((@x), _) : (a, b) )
     -> @x;
}, branches = [CaseBranch 0 (@skip std/core/types/Tuple2((@x), _) : (a, b) )
   -> @x;]}
Extending store: B@(@x:[a170,a117,a164]@[]) with int -> 1
Evaluating: @x types:415:[a170,a117,a164]@[]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(resume:[a117,a164,a117]@[])], parent = AppParam basic-bench:163 0 resume((@open(tuple2/fst)(a)))}
Applying: [] [B@(resume:[a117,a164,a117]@[]),B@(@x:[a170,a117,a164]@[])]
Applying function: B@(resume:[a117,a164,a117]@[]) Kont(analysis/aac/basic-bench/ex2,AI@(117:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]),[a117,a164,a117]@[],Handler {ops = B@(hnd:[a144,a141,top]@[]), ret = Just AppParam basic-bench:147 1 fn(x){
  x;
}, henv = BEnv (fromList [a,resume])})
Applying continuation basic-bench:163 rebinding fromList [a,resume]
Rebinding: fromList [a,resume] from [a117,a164,a117]@[] to [a163,a117,a164]@[]
Extending store: B@(a:[a163,a117,a164]@[]) with std/core/types/Tuple2([(fst,CI@(fst 213:[delim]@[(basic-bench:164,[a164,a117,a144])])),(snd,CI@(snd 213:[delim]@[(basic-bench:164,[a164,a117,a144])]))])
Extending store: B@(resume:[a163,a117,a164]@[]) with Kont(analysis/aac/basic-bench/ex2,AI@(117:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]),[a117,a164,a117]@[],Handler {ops = B@(hnd:[a144,a141,top]@[]), ret = Just AppParam basic-bench:147 1 fn(x){
  x;
}, henv = BEnv (fromList [a,resume])})
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/int/(+),B@(@x:[a180,a117,a144]@[])], parent = LamBody [] @open((+))((@open(ex2)((Tuple2(1, 2)))), (@open(ex2)((Tuple2(1, 2)))))}
Applying: [] [T@std/core/int/(+),B@(@x:[a180,a117,a144]@[]),B@(@x:[a170,a117,a164]@[])]
Applying function: T@std/core/int/(+) DefNonRec((+))
Applying closure: DefNonRec // Add two integers.
pub fip fun (+) : (x : int, y : int) -> int;:[a192,delim]@[(basic-bench:163,[a163,a117,a164])] fvvs: fromList [] args [x,y]
Extending store: B@(x:[a192,delim]@[(basic-bench:163,[a163,a117,a164])]) with int -> 2
Extending store: B@(y:[a192,delim]@[(basic-bench:163,[a163,a117,a164])]) with int -> 1
Evaluating: @open(int-add)(x, y) int:416:[a192,delim]@[(basic-bench:163,[a163,a117,a164])]
Evaluating: int-add int:421:[a192,delim]@[(basic-bench:163,[a163,a117,a164])]
Extending store: BI@(421:[a192,delim]@[(basic-bench:163,[a163,a117,a164])]) with std/core/int/int-add
Applying FApp {totalArgs = 2, leftArgs = [AppParam int:418 0 x,AppParam int:419 1 y], resolvedArgs = [], parent = LamBody [x,y] @open(int-add)(x, y)}
Evaluating: x int:418:[a192,delim]@[(basic-bench:163,[a163,a117,a164])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam int:419 1 y], resolvedArgs = [BI@(421:[a192,delim]@[(basic-bench:163,[a163,a117,a164])])], parent = LamBody [x,y] @open(int-add)(x, y)}
Evaluating: y int:419:[a192,delim]@[(basic-bench:163,[a163,a117,a164])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(421:[a192,delim]@[(basic-bench:163,[a163,a117,a164])]),B@(x:[a192,delim]@[(basic-bench:163,[a163,a117,a164])])], parent = LamBody [x,y] @open(int-add)(x, y)}
Applying: [] [BI@(421:[a192,delim]@[(basic-bench:163,[a163,a117,a164])]),B@(x:[a192,delim]@[(basic-bench:163,[a163,a117,a164])]),B@(y:[a192,delim]@[(basic-bench:163,[a163,a117,a164])])]
Applying function: BI@(421:[a192,delim]@[(basic-bench:163,[a163,a117,a164])]) std/core/int/int-add
Applying primitive std/core/int/int-add
Extending store: BI@(416:[a192,delim]@[(basic-bench:163,[a163,a117,a164])]) with int -> 3
Applying FDollar {vaddr = B@(ret:[a144,a141,top]@[])}
Extending store: B@(x:[a163,a117,a164]@[]) with int -> 3
Evaluating: x basic-bench:189:[a163,a117,a164]@[]
Applying FApp {totalArgs = 2, leftArgs = [AppParam basic-bench:164 1 resume((@open(tuple2/snd)(a)))], resolvedArgs = [T@std/core/int/(+)], parent = LamBody [a,resume] @open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a)))))}
Evaluating: resume((@open(tuple2/snd)(a))) basic-bench:164:[a117,a164,a117]@[]
Evaluating: resume basic-bench:179:[a117,a164,a117]@[]
Applying FApp {totalArgs = 1, leftArgs = [AppParam basic-bench:180 0 @open(tuple2/snd)(a)], resolvedArgs = [], parent = AppParam basic-bench:164 1 resume((@open(tuple2/snd)(a)))}
Evaluating: @open(tuple2/snd)(a) basic-bench:180:[a117,a164,a117]@[]
Evaluating: tuple2/snd basic-bench:185:[a117,a164,a117]@[]
Evaluating: tuple2/snd basic-bench:187:[a117,a164,a117]@[]
New result at Step (CEval ExprBasic tuple2/snd AI@(182:[a117,a164,a117]@[]) EndMKAddr [a117,a164,a117]@[])
N (CApply AI@(182:[a117,a164,a117]@[]) EndMKAddr T@std/core/types/#tuple2/snd [])
Not in:
Next (fromList [CEval DefNonRec // Automatically generated. Retrieves the `snd` constructor field of the `:tuple2` type.
pub fun tuple2/snd : forall<a,b> (^ tuple2 : (a, b)) -> b; EndKAddr T@std/core/types/#tuple2/snd [top]@[]])
New:
N (CApply AI@(182:[a117,a164,a117]@[]) EndMKAddr T@std/core/types/#tuple2/snd [])
Applying FApp {totalArgs = 1, leftArgs = [AppParam basic-bench:183 0 a], resolvedArgs = [], parent = AppParam basic-bench:180 0 @open(tuple2/snd)(a)}
Evaluating: a basic-bench:183:[a117,a164,a117]@[]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@std/core/types/#tuple2/snd], parent = AppParam basic-bench:180 0 @open(tuple2/snd)(a)}
Applying: [] [T@std/core/types/#tuple2/snd,B@(a:[a117,a164,a117]@[])]
Applying function: T@std/core/types/#tuple2/snd DefNonRec(tuple2/snd)
Applying closure: DefNonRec // Automatically generated. Retrieves the `snd` constructor field of the `:tuple2` type.
pub fun tuple2/snd : forall<a,b> (^ tuple2 : (a, b)) -> b;:[a180,a117,a164]@[] fvvs: fromList [] args [tuple2]
Extending store: B@(tuple2:[a180,a117,a164]@[]) with std/core/types/Tuple2([(fst,CI@(fst 213:[delim]@[(basic-bench:164,[a164,a117,a144])])),(snd,CI@(snd 213:[delim]@[(basic-bench:164,[a164,a117,a144])]))])
Evaluating: match (tuple2) {
  (@skip Tuple2(_, (@x)) : (a, b) )
     -> @x;
} types:422:[a180,a117,a164]@[]
Evaluating: tuple2 types:423:[a180,a117,a164]@[]
Applying FScrut {parent = LamBody [tuple2] match (tuple2) {
  (@skip Tuple2(_, (@x)) : (a, b) )
     -> @x;
}, branches = [CaseBranch 0 (@skip std/core/types/Tuple2(_, (@x)) : (a, b) )
   -> @x;]}
Extending store: B@(@x:[a180,a117,a164]@[]) with int -> 2
Evaluating: @x types:424:[a180,a117,a164]@[]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(resume:[a117,a164,a117]@[])], parent = AppParam basic-bench:164 1 resume((@open(tuple2/snd)(a)))}
Applying: [] [B@(resume:[a117,a164,a117]@[]),B@(@x:[a180,a117,a164]@[])]
Applying function: B@(resume:[a117,a164,a117]@[]) Kont(analysis/aac/basic-bench/ex2,AI@(117:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]),[a117,a164,a117]@[],Handler {ops = B@(hnd:[a144,a141,top]@[]), ret = Just AppParam basic-bench:147 1 fn(x){
  x;
}, henv = BEnv (fromList [a,resume])})
Applying continuation basic-bench:164 rebinding fromList [a,resume]
Rebinding: fromList [a,resume] from [a117,a164,a117]@[] to [a164,a117,a164]@[]
Extending store: B@(a:[a164,a117,a164]@[]) with std/core/types/Tuple2([(fst,CI@(fst 213:[delim]@[(basic-bench:164,[a164,a117,a144])])),(snd,CI@(snd 213:[delim]@[(basic-bench:164,[a164,a117,a144])]))])
Extending store: B@(resume:[a164,a117,a164]@[]) with Kont(analysis/aac/basic-bench/ex2,AI@(117:[a195,delim]@[(basic-bench:164,[a164,a117,a144])]),[a117,a164,a117]@[],Handler {ops = B@(hnd:[a144,a141,top]@[]), ret = Just AppParam basic-bench:147 1 fn(x){
  x;
}, henv = BEnv (fromList [a,resume])})
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/int/(+),B@(@x:[a180,a117,a144]@[])], parent = LamBody [] @open((+))((@open(ex2)((Tuple2(1, 2)))), (@open(ex2)((Tuple2(1, 2)))))}
Applying: [] [T@std/core/int/(+),B@(@x:[a180,a117,a144]@[]),B@(@x:[a180,a117,a164]@[])]
Applying function: T@std/core/int/(+) DefNonRec((+))
Applying closure: DefNonRec // Add two integers.
pub fip fun (+) : (x : int, y : int) -> int;:[a192,delim]@[(basic-bench:164,[a164,a117,a164])] fvvs: fromList [] args [x,y]
Extending store: B@(x:[a192,delim]@[(basic-bench:164,[a164,a117,a164])]) with int -> 2
Extending store: B@(y:[a192,delim]@[(basic-bench:164,[a164,a117,a164])]) with int -> 2
Evaluating: @open(int-add)(x, y) int:416:[a192,delim]@[(basic-bench:164,[a164,a117,a164])]
Evaluating: int-add int:421:[a192,delim]@[(basic-bench:164,[a164,a117,a164])]
Extending store: BI@(421:[a192,delim]@[(basic-bench:164,[a164,a117,a164])]) with std/core/int/int-add
Applying FApp {totalArgs = 2, leftArgs = [AppParam int:418 0 x,AppParam int:419 1 y], resolvedArgs = [], parent = LamBody [x,y] @open(int-add)(x, y)}
Evaluating: x int:418:[a192,delim]@[(basic-bench:164,[a164,a117,a164])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam int:419 1 y], resolvedArgs = [BI@(421:[a192,delim]@[(basic-bench:164,[a164,a117,a164])])], parent = LamBody [x,y] @open(int-add)(x, y)}
Evaluating: y int:419:[a192,delim]@[(basic-bench:164,[a164,a117,a164])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(421:[a192,delim]@[(basic-bench:164,[a164,a117,a164])]),B@(x:[a192,delim]@[(basic-bench:164,[a164,a117,a164])])], parent = LamBody [x,y] @open(int-add)(x, y)}
Applying: [] [BI@(421:[a192,delim]@[(basic-bench:164,[a164,a117,a164])]),B@(x:[a192,delim]@[(basic-bench:164,[a164,a117,a164])]),B@(y:[a192,delim]@[(basic-bench:164,[a164,a117,a164])])]
Applying function: BI@(421:[a192,delim]@[(basic-bench:164,[a164,a117,a164])]) std/core/int/int-add
Applying primitive std/core/int/int-add
Extending store: BI@(416:[a192,delim]@[(basic-bench:164,[a164,a117,a164])]) with int -> 4
Applying FDollar {vaddr = B@(ret:[a144,a141,top]@[])}
Extending store: B@(x:[a164,a117,a164]@[]) with int -> 4
Evaluating: x basic-bench:189:[a164,a117,a164]@[]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/int/(+),B@(x:[a163,a117,a164]@[])], parent = LamBody [a,resume] @open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a)))))}
Applying: [] [T@std/core/int/(+),B@(x:[a163,a117,a164]@[]),B@(x:[a164,a117,a164]@[])]
Applying function: T@std/core/int/(+) DefNonRec((+))
Applying closure: DefNonRec // Add two integers.
pub fip fun (+) : (x : int, y : int) -> int;:[a161,a117,a164]@[] fvvs: fromList [] args [x,y]
Extending store: B@(x:[a161,a117,a164]@[]) with int -> 3
Extending store: B@(y:[a161,a117,a164]@[]) with int -> 4
Evaluating: @open(int-add)(x, y) int:416:[a161,a117,a164]@[]
Evaluating: int-add int:421:[a161,a117,a164]@[]
Extending store: BI@(421:[a161,a117,a164]@[]) with std/core/int/int-add
Applying FApp {totalArgs = 2, leftArgs = [AppParam int:418 0 x,AppParam int:419 1 y], resolvedArgs = [], parent = LamBody [x,y] @open(int-add)(x, y)}
Evaluating: x int:418:[a161,a117,a164]@[]
Applying FApp {totalArgs = 2, leftArgs = [AppParam int:419 1 y], resolvedArgs = [BI@(421:[a161,a117,a164]@[])], parent = LamBody [x,y] @open(int-add)(x, y)}
Evaluating: y int:419:[a161,a117,a164]@[]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(421:[a161,a117,a164]@[]),B@(x:[a161,a117,a164]@[])], parent = LamBody [x,y] @open(int-add)(x, y)}
Applying: [] [BI@(421:[a161,a117,a164]@[]),B@(x:[a161,a117,a164]@[]),B@(y:[a161,a117,a164]@[])]
Applying function: BI@(421:[a161,a117,a164]@[]) std/core/int/int-add
Applying primitive std/core/int/int-add
Extending store: BI@(416:[a161,a117,a164]@[]) with int -> 7
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/int/(+),BI@(416:[a161,a117,a163]@[])], parent = LamBody [a,resume] @open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a)))))}
Applying: [] [T@std/core/int/(+),BI@(416:[a161,a117,a163]@[]),BI@(416:[a161,a117,a164]@[])]
Applying function: T@std/core/int/(+) DefNonRec((+))
Applying closure: DefNonRec // Add two integers.
pub fip fun (+) : (x : int, y : int) -> int;:[a161,a117,a144]@[] fvvs: fromList [] args [x,y]
Extending store: B@(x:[a161,a117,a144]@[]) with int -> 5
Extending store: B@(y:[a161,a117,a144]@[]) with int -> 7
Evaluating: @open(int-add)(x, y) int:416:[a161,a117,a144]@[]
Evaluating: int-add int:421:[a161,a117,a144]@[]
Extending store: BI@(421:[a161,a117,a144]@[]) with std/core/int/int-add
Applying FApp {totalArgs = 2, leftArgs = [AppParam int:418 0 x,AppParam int:419 1 y], resolvedArgs = [], parent = LamBody [x,y] @open(int-add)(x, y)}
Evaluating: x int:418:[a161,a117,a144]@[]
Applying FApp {totalArgs = 2, leftArgs = [AppParam int:419 1 y], resolvedArgs = [BI@(421:[a161,a117,a144]@[])], parent = LamBody [x,y] @open(int-add)(x, y)}
Evaluating: y int:419:[a161,a117,a144]@[]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(421:[a161,a117,a144]@[]),B@(x:[a161,a117,a144]@[])], parent = LamBody [x,y] @open(int-add)(x, y)}
Applying: [] [BI@(421:[a161,a117,a144]@[]),B@(x:[a161,a117,a144]@[]),B@(y:[a161,a117,a144]@[])]
Applying function: BI@(421:[a161,a117,a144]@[]) std/core/int/int-add
Applying primitive std/core/int/int-add
Extending store: BI@(416:[a161,a117,a144]@[]) with int -> 12
Extending store: EndVAddr with int -> 12
Evaluating: 12 basic-bench:231:[top]@[]
Extending store: BI@(231:[top]@[]) with int -> 12
Extending store: EndVAddr with int -> 12
d=2,m=3
Result 1 / 1
Result 100.0%, time: 0.022613s
