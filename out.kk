koka-3.2.3: unregistering (local file changes: src/Compile/TypeCheck.hs src/Core/FlowAnalysis/Full/DMCFA/DMCFA.hs)
koka> build (lib + exe) with ghc-9.6.6
Preprocessing library for koka-3.2.3..
Building library for koka-3.2.3..
[126 of 141] Compiling Core.FlowAnalysis.Full.DMCFA.DMCFA [Source file changed]
[127 of 141] Compiling Core.FlowAnalysis.Full.DMCFA.Syntax [Core.FlowAnalysis.Full.DMCFA.DMCFA changed]
[136 of 141] Compiling Compile.TypeCheck [Source file changed]
[138 of 141] Compiling Compile.Build [Core.FlowAnalysis.Full.DMCFA.Syntax changed]
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
Module // Automatically generated. Retrieves the `index` constructor field of the `:ix` type.
fun ix/index : forall<s> (^ ix : analysis/benchmarks/handlers/vec/ix<s>) -> int
  = forall<s> fn(ix){
    (match (ix) {
      ((@skip Ix((@x)) : analysis/benchmarks/handlers/vec/ix<s> ) as @pat)
         -> @x;
    });
  };
pub fun ix/@copy : forall<s> (@this : analysis/benchmarks/handlers/vec/ix<s>, index : ? int) -> analysis/benchmarks/handlers/vec/ix<s>
  = forall<s> fn(@this, index){
    val @uniq-index@127 : int
          = (match (index) {
            ((@Optional((@uniq-index@128)) : ? int ) as @pat)
               -> @uniq-index@128;
            ((@skip @None() : ? int ) as @pat@0)
               -> ix/index(@this);
          });
    Ix(@uniq-index@127);
  };
// Automatically generated. Retrieves the `@cfc` constructor field of the `:vec` type.
fun vec/@cfc : forall<s,e,a> (^ vec : analysis/benchmarks/handlers/vec/vec<s,e,a>) -> int
  = forall<s,e,a> fn(vec@0){
    (match (vec@0) {
      ((@skip @Hnd-vec((@x), (@pat@0), (@pat@1)) : analysis/benchmarks/handlers/vec/vec<s,e,a> ) as @pat)
         -> @x;
    });
  };
// runtime tag for the effect `:vec`
val vec/@tag : forall<s> hnd/htag<analysis/benchmarks/handlers/vec/vec<s>>
  = forall<s> @new-htag("vec@vec");
// handler for the effect `:vec`
fun vec/@handle : forall<s,a,e,b> (hnd : analysis/benchmarks/handlers/vec/vec<s,e,b>, ret : (res : a) -> e b, action : () -> <analysis/benchmarks/handlers/vec/vec<s>|e> a) -> e b
  = forall<s,a,e,b> fn(hnd, ret, action){
    @hhandle(vec/@tag, hnd, ret, action);
  };
// Automatically generated. Retrieves the `@fun-push` constructor field of the `:vec` type.
fun vec/@fun-push : forall<s,e,a> (^ vec : analysis/benchmarks/handlers/vec/vec<s,e,a>) -> hnd/clause1<string,analysis/benchmarks/handlers/vec/ix<s>,analysis/benchmarks/handlers/vec/vec<s>,e,a>
  = forall<s,e,a> fn(vec@0){
    (match (vec@0) {
      ((@skip @Hnd-vec((@pat@0), (@pat@1), (@x)) : analysis/benchmarks/handlers/vec/vec<s,e,a> ) as @pat)
         -> @x;
    });
  };
// select `push` operation out of effect `:vec`
fun push/@select : forall<s,e,a> (^ hnd : analysis/benchmarks/handlers/vec/vec<s,e,a>) -> hnd/clause1<string,analysis/benchmarks/handlers/vec/ix<s>,analysis/benchmarks/handlers/vec/vec<s>,e,a>
  = forall<s,e,a> fn(hnd){
    (match (hnd) {
      ((@skip @Hnd-vec((@pat@0), (@pat@1), (@fun-push)) : analysis/benchmarks/handlers/vec/vec<s,e,a> ) as @pat)
         -> @fun-push;
    });
  };
// Call the `fun push` operation of the effect `:vec`
fun push : forall<s> (s : string) -> (analysis/benchmarks/handlers/vec/vec<s>) analysis/benchmarks/handlers/vec/ix<s>
  = forall<s> fn(s){
    @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> push/@select), s);
  };
// Automatically generated. Retrieves the `@fun-lookup` constructor field of the `:vec` type.
fun vec/@fun-lookup : forall<s,e,a> (^ vec : analysis/benchmarks/handlers/vec/vec<s,e,a>) -> hnd/clause1<analysis/benchmarks/handlers/vec/ix<s>,string,analysis/benchmarks/handlers/vec/vec<s>,e,a>
  = forall<s,e,a> fn(vec@0){
    (match (vec@0) {
      ((@skip @Hnd-vec((@pat@0), (@x), (@pat@1)) : analysis/benchmarks/handlers/vec/vec<s,e,a> ) as @pat)
         -> @x;
    });
  };
// select `lookup` operation out of effect `:vec`
fun lookup/@select : forall<s,e,a> (^ hnd : analysis/benchmarks/handlers/vec/vec<s,e,a>) -> hnd/clause1<analysis/benchmarks/handlers/vec/ix<s>,string,analysis/benchmarks/handlers/vec/vec<s>,e,a>
  = forall<s,e,a> fn(hnd){
    (match (hnd) {
      ((@skip @Hnd-vec((@pat@0), (@fun-lookup), (@pat@1)) : analysis/benchmarks/handlers/vec/vec<s,e,a> ) as @pat)
         -> @fun-lookup;
    });
  };
// Call the `fun lookup` operation of the effect `:vec`
fun lookup : forall<s> (ix : analysis/benchmarks/handlers/vec/ix<s>) -> (analysis/benchmarks/handlers/vec/vec<s>) string
  = forall<s> fn(ix){
    @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> lookup/@select), ix);
  };
// Create a `vec` handler that safely only handles its own indices (parameterized by `:s`)
fun vec : forall<a,e> (action1 : forall<s> () -> <analysis/benchmarks/handlers/vec/vec<s>|e> a) -> e a
  = forall<a,e> fn(action1){
    local-scope((forall<h> fn(){
      local-var(Nil, (fn(xs){
          (vec/@handle((@Hnd-vec(1, (@open(clause-tail1)((fn(ix){
                (@open(default)((@open(@index)((local-get(xs, @Hnodiv)), (@open(ix/index)(ix)))), ""));
              }))), (@open(clause-tail1)((fn(s){
                val i : int
                  = (@open(length)((local-get(xs, @Hnodiv))));
                val _ : ()
                  = (local-set(xs, (@open((++))((local-get(xs, @Hnodiv)), (Cons(s, Nil))))));
                (Ix(i));
              }))))), (fn(@res){
              @res;
            }), (fn(){
              (@mask-builtin((fn(){
                (action1());
              })));
            })));
        }));
    }));
  };
pub fun analyze-main : () -> string
  = fn(){
    vec((forall<s> fn(){
      val ix : analysis/benchmarks/handlers/vec/ix<s>
            = push("hello");
      @open((++))((lookup(ix)), " world");
    }));
  };
pub fun result-main : () -> string
  = fn(){
    "hello world";
  };
Evaluating: vec((forall<s> fn(){
  val ix : analysis/benchmarks/handlers/vec/ix<s>
        = @open(push)("hello");
  @open((++))((@open(lookup)(ix)), " world");
})):t_[top]@[] with env fromList []
Evaluating: local-scope((forall<h> fn(){
  val iev@654 : hdiv<h,list<string>,e>;
  val iev@722 : hdiv<h,list<string>,e>;
  val iev@766 : hdiv<h,list<string>,e>;
  local-var(Nil, (fn(xs){
      ((fn(@action){
        vec/@handle((@Hnd-vec(1, (@open(clause-tail1)((fn(ix){
              (@open(default)((@open(@index)((local-get(xs, iev@654)), (@open(ix/index)(ix)))), ""));
            }))), (@open(clause-tail1)((fn(s){
              val i : int;
              val _ : ();
              (Ix(i));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        ((fn(){
          @mask-builtin((fn(){
            (action1());
          }));
        })());
      })));
    }));
})):t_[a298,top]@[] with env fromList [(action1,(t_[a298,top]@[],vec:25))]
Evaluating: @open(unsafe-no-local-cast)((forall<h> action))():t_[a164,a298,top]@[] with env fromList [(action,(t_[a164,a298,top]@[],types:430))]
Evaluating: val iev@654 : hdiv<h,list<string>,e>;
val iev@722 : hdiv<h,list<string>,e>;
val iev@766 : hdiv<h,list<string>,e>;
local-var(Nil, (fn(xs){
    ((fn(@action){
      vec/@handle((@Hnd-vec(1, (@open(clause-tail1)((fn(ix){
            (@open(default)((@open(@index)((local-get(xs, iev@654)), (@open(ix/index)(ix)))), ""));
          }))), (@open(clause-tail1)((fn(s){
            val i : int;
            val _ : ();
            (Ix(i));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      ((fn(){
        @mask-builtin((fn(){
          (action1());
        }));
      })());
    })));
  })):t_[a437,a164,a298,top]@[] with env fromList [(action1,(t_[a298,top]@[],vec:25))]
Evaluating: local-var(Nil, (fn(xs){
    ((fn(@action){
      vec/@handle((@Hnd-vec(1, (@open(clause-tail1)((fn(ix){
            (@open(default)((@open(@index)((local-get(xs, iev@654)), (@open(ix/index)(ix)))), ""));
          }))), (@open(clause-tail1)((fn(s){
            val i : int;
            val _ : ();
            (Ix(i));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      ((fn(){
        @mask-builtin((fn(){
          (action1());
        }));
      })());
    })));
  })):t_[a437,a164,a298,top]@[] with env fromList [(action1,(t_[a298,top]@[],vec:25)),(iev@654,(t_[a437,a164,a298,top]@[],vec:168)),(iev@722,(t_[a437,a164,a298,top]@[],vec:168)),(iev@766,(t_[a437,a164,a298,top]@[],vec:168))]
Evaluating: (fn(@action){
  vec/@handle((@Hnd-vec(1, (@open(clause-tail1)((fn(ix){
        (@open(default)((@open(@index)((local-get(xs, iev@654)), (@open(ix/index)(ix)))), ""));
      }))), (@open(clause-tail1)((fn(s){
        val i : int;
        val _ : ();
        (Ix(i));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(){
    @mask-builtin((fn(){
      (action1());
    }));
  })());
})):d_[delim]@[((vec:175,xs),t_[a437,a164,a298,top])] with env fromList [(action1,(t_[a298,top]@[],vec:25)),(iev@654,(t_[a437,a164,a298,top]@[],vec:168)),(iev@722,(t_[a437,a164,a298,top]@[],vec:168)),(iev@766,(t_[a437,a164,a298,top]@[],vec:168)),(xs,(t_[a437,a164,a298,top]@[],vec:178))]
Evaluating: vec/@handle((@Hnd-vec(1, (@open(clause-tail1)((fn(ix){
      (@open(default)((@open(@index)((local-get(xs, iev@654)), (@open(ix/index)(ix)))), ""));
    }))), (@open(clause-tail1)((fn(s){
      val i : int;
      val _ : ();
      (Ix(i));
    }))))), (fn(@res){
    @res;
  }), @action):d_[a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])] with env fromList [(@action,(d_[a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])],vec:182)),(iev@654,(t_[a437,a164,a298,top]@[],vec:168)),(iev@722,(t_[a437,a164,a298,top]@[],vec:168)),(iev@766,(t_[a437,a164,a298,top]@[],vec:168)),(xs,(t_[a437,a164,a298,top]@[],vec:178))]
Evaluating: @Hnd-vec(1, (@open(clause-tail1)((fn(ix){
    (@open(default)((@open(@index)((local-get(xs, iev@654)), (@open(ix/index)(ix)))), ""));
  }))), (@open(clause-tail1)((fn(s){
    val i : int;
    val _ : ();
    (Ix(i));
  })))):d_[a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])] with env fromList [(iev@654,(t_[a437,a164,a298,top]@[],vec:168)),(iev@722,(t_[a437,a164,a298,top]@[],vec:168)),(iev@766,(t_[a437,a164,a298,top]@[],vec:168)),(xs,(t_[a437,a164,a298,top]@[],vec:178))]
Result: @Hnd-vec(1, (@open(clause-tail1)((fn(ix){
    (@open(default)((@open(@index)((local-get(xs, iev@654)), (@open(ix/index)(ix)))), ""));
  }))), (@open(clause-tail1)((fn(s){
    val i : int;
    val _ : ();
    (Ix(i));
  })))):d_[a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])] with env fromList [(iev@654,(t_[a437,a164,a298,top]@[],vec:168)),(iev@722,(t_[a437,a164,a298,top]@[],vec:168)),(iev@766,(t_[a437,a164,a298,top]@[],vec:168)),(xs,(t_[a437,a164,a298,top]@[],vec:178))]
RV (RVAddr BI@(186:d_[a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])]))
Evaluating: @hhandle(vec/@tag, hnd, ret, action):d_[a184,a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])] with env fromList [(action,(d_[a184,a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])],vec:11)),(hnd,(d_[a184,a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])],vec:11)),(ret,(d_[a184,a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])],vec:11))]
Evaluating: (fn(){
  @mask-builtin((fn(){
    (action1());
  }));
})():d_[delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])] with env fromList [(action1,(t_[a298,top]@[],vec:25))]
Evaluating: @mask-builtin((fn(){
  (action1());
})):d_[a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])] with env fromList [(action1,(t_[a298,top]@[],vec:25))]
Evaluating: action1():d_[a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])] with env fromList [(action1,(t_[a298,top]@[],vec:25))]
Evaluating: val ix : analysis/benchmarks/handlers/vec/ix<s>
      = @open(push)("hello");
@open((++))((@open(lookup)(ix)), " world"):d_[a292,a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])] with env fromList []
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> push/@select), s):d_[a304,a292,a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])] with env fromList [(s,(d_[a304,a292,a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])],vec:17))]
Result: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> push/@select), s):d_[a304,a292,a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])] with env fromList [(s,(d_[a304,a292,a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])],vec:17))]
RV (ROp (DVal {dLabel = analysis/benchmarks/handlers/vec/vec, dOpName = push, dExpr = LamBody [s] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> push/@select), s), dArgs = [B@(s:d_[a304,a292,a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])])], dCtx = d_[a304,a292,a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])]}) d_[a304,a292,a286,delim] FrameDone DFrameDone EndKAddr)
Result: val ix : analysis/benchmarks/handlers/vec/ix<s>
      = @open(push)("hello");
@open((++))((@open(lookup)(ix)), " world"):d_[a292,a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])] with env fromList []
RV (ROp (DVal {dLabel = analysis/benchmarks/handlers/vec/vec, dOpName = push, dExpr = LamBody [s] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> push/@select), s), dArgs = [B@(s:d_[a304,a292,a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])])], dCtx = d_[a304,a292,a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])]}) d_[a292,a286,delim] FLet((0,1,0,1,ix), [], LamBody([])) DFrameDone K@(FrameDone,d_[a304,a292,a286,delim],DFrameDone,DVal {dLabel = analysis/benchmarks/handlers/vec/vec, dOpName = push, dExpr = LamBody [s] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> push/@select), s), dArgs = [B@(s:d_[a304,a292,a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])])], dCtx = d_[a304,a292,a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])]}))
Result: action1():d_[a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])] with env fromList [(action1,(t_[a298,top]@[],vec:25))]
RV (ROp (DVal {dLabel = analysis/benchmarks/handlers/vec/vec, dOpName = push, dExpr = LamBody [s] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> push/@select), s), dArgs = [B@(s:d_[a304,a292,a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])])], dCtx = d_[a304,a292,a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])]}) d_[a292,a286,delim] FLet((0,1,0,1,ix), [], LamBody([])) DFrameDone K@(FrameDone,d_[a304,a292,a286,delim],DFrameDone,DVal {dLabel = analysis/benchmarks/handlers/vec/vec, dOpName = push, dExpr = LamBody [s] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> push/@select), s), dArgs = [B@(s:d_[a304,a292,a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])])], dCtx = d_[a304,a292,a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])]}))
Result: @mask-builtin((fn(){
  (action1());
})):d_[a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])] with env fromList [(action1,(t_[a298,top]@[],vec:25))]
RV (ROp (DVal {dLabel = analysis/benchmarks/handlers/vec/vec, dOpName = push, dExpr = LamBody [s] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> push/@select), s), dArgs = [B@(s:d_[a304,a292,a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])])], dCtx = d_[a304,a292,a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])]}) d_[a292,a286,delim] FLet((0,1,0,1,ix), [], LamBody([])) DFrameDone K@(FrameDone,d_[a304,a292,a286,delim],DFrameDone,DVal {dLabel = analysis/benchmarks/handlers/vec/vec, dOpName = push, dExpr = LamBody [s] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> push/@select), s), dArgs = [B@(s:d_[a304,a292,a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])])], dCtx = d_[a304,a292,a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])]}))
Result: (fn(){
  @mask-builtin((fn(){
    (action1());
  }));
})():d_[delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])] with env fromList [(action1,(t_[a298,top]@[],vec:25))]
RV (ROp (DVal {dLabel = analysis/benchmarks/handlers/vec/vec, dOpName = push, dExpr = LamBody [s] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> push/@select), s), dArgs = [B@(s:d_[a304,a292,a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])])], dCtx = d_[a304,a292,a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])]}) d_[a292,a286,delim] FLet((0,1,0,1,ix), [], LamBody([])) DFrameDone K@(FrameDone,d_[a304,a292,a286,delim],DFrameDone,DVal {dLabel = analysis/benchmarks/handlers/vec/vec, dOpName = push, dExpr = LamBody [s] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> push/@select), s), dArgs = [B@(s:d_[a304,a292,a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])])], dCtx = d_[a304,a292,a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])]}))
Evaluating: val i : int;
val _ : ();
Ix(i):d_[a184,a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])] with env fromList [(iev@722,(t_[a437,a164,a298,top]@[],vec:168)),(iev@766,(t_[a437,a164,a298,top]@[],vec:168)),(s,(d_[a184,a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])],vec:232)),(xs,(t_[a437,a164,a298,top]@[],vec:178))]
Evaluating: local-get(xs, iev@722):d_[a184,a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])] with env fromList [(iev@722,(t_[a437,a164,a298,top]@[],vec:168)),(xs,(t_[a437,a164,a298,top]@[],vec:178))]
Result: local-get(xs, iev@722):d_[a184,a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])] with env fromList [(iev@722,(t_[a437,a164,a298,top]@[],vec:168)),(xs,(t_[a437,a164,a298,top]@[],vec:178))]
RV (ROp (DVal {dLabel = xs, dOpName = std/core/types/local-get, dExpr = AppParam vec:272 0 local-get(xs, iev@722), dArgs = [], dCtx = d_[a184,a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])]}) d_[a184,a181,delim] FrameDone DFrameDone EndKAddr)
Result: val i : int;
val _ : ();
Ix(i):d_[a184,a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])] with env fromList [(iev@722,(t_[a437,a164,a298,top]@[],vec:168)),(iev@766,(t_[a437,a164,a298,top]@[],vec:168)),(s,(d_[a184,a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])],vec:232)),(xs,(t_[a437,a164,a298,top]@[],vec:178))]
RV (ROp (DVal {dLabel = xs, dOpName = std/core/types/local-get, dExpr = AppParam vec:272 0 local-get(xs, iev@722), dArgs = [], dCtx = d_[a184,a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])]}) d_[a184,a181,delim] FLet((0,2,0,1,i), [], LamBody([s])) DFrameDone K@(FApp(1, [], [BI@(457:t_[top]@[])], LetDef(i)),d_[a184,a181,delim],DFrameDone,DVal {dLabel = xs, dOpName = std/core/types/local-get, dExpr = AppParam vec:272 0 local-get(xs, iev@722), dArgs = [], dCtx = d_[a184,a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])]}))
Result: @hhandle(vec/@tag, hnd, ret, action):d_[a184,a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])] with env fromList [(action,(d_[a184,a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])],vec:11)),(hnd,(d_[a184,a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])],vec:11)),(ret,(d_[a184,a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])],vec:11))]
RV (ROp (DVal {dLabel = xs, dOpName = std/core/types/local-get, dExpr = AppParam vec:272 0 local-get(xs, iev@722), dArgs = [], dCtx = d_[a184,a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])]}) d_[a184,a181,delim] FResume(d_[a292,a286,delim], K@(FLet((0,1,0,1,ix), [], LamBody([])),d_[a292,a286,delim],DFrameDone,DVal {dLabel = analysis/benchmarks/handlers/vec/vec, dOpName = push, dExpr = LamBody [s] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> push/@select), s), dArgs = [B@(s:d_[a304,a292,a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])])], dCtx = d_[a304,a292,a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])]}), 237) DFrameDone K@(FLet((0,2,0,1,i), [], LamBody([s])),d_[a184,a181,delim],DFrameDone,DVal {dLabel = xs, dOpName = std/core/types/local-get, dExpr = AppParam vec:272 0 local-get(xs, iev@722), dArgs = [], dCtx = d_[a184,a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])]}))
Result: vec/@handle((@Hnd-vec(1, (@open(clause-tail1)((fn(ix){
      (@open(default)((@open(@index)((local-get(xs, iev@654)), (@open(ix/index)(ix)))), ""));
    }))), (@open(clause-tail1)((fn(s){
      val i : int;
      val _ : ();
      (Ix(i));
    }))))), (fn(@res){
    @res;
  }), @action):d_[a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])] with env fromList [(@action,(d_[a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])],vec:182)),(iev@654,(t_[a437,a164,a298,top]@[],vec:168)),(iev@722,(t_[a437,a164,a298,top]@[],vec:168)),(iev@766,(t_[a437,a164,a298,top]@[],vec:168)),(xs,(t_[a437,a164,a298,top]@[],vec:178))]
RV (ROp (DVal {dLabel = xs, dOpName = std/core/types/local-get, dExpr = AppParam vec:272 0 local-get(xs, iev@722), dArgs = [], dCtx = d_[a184,a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])]}) d_[a184,a181,delim] FResume(d_[a292,a286,delim], K@(FLet((0,1,0,1,ix), [], LamBody([])),d_[a292,a286,delim],DFrameDone,DVal {dLabel = analysis/benchmarks/handlers/vec/vec, dOpName = push, dExpr = LamBody [s] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> push/@select), s), dArgs = [B@(s:d_[a304,a292,a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])])], dCtx = d_[a304,a292,a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])]}), 237) DFrameDone K@(FLet((0,2,0,1,i), [], LamBody([s])),d_[a184,a181,delim],DFrameDone,DVal {dLabel = xs, dOpName = std/core/types/local-get, dExpr = AppParam vec:272 0 local-get(xs, iev@722), dArgs = [], dCtx = d_[a184,a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])]}))
Result: (fn(@action){
  vec/@handle((@Hnd-vec(1, (@open(clause-tail1)((fn(ix){
        (@open(default)((@open(@index)((local-get(xs, iev@654)), (@open(ix/index)(ix)))), ""));
      }))), (@open(clause-tail1)((fn(s){
        val i : int;
        val _ : ();
        (Ix(i));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(){
    @mask-builtin((fn(){
      (action1());
    }));
  })());
})):d_[delim]@[((vec:175,xs),t_[a437,a164,a298,top])] with env fromList [(action1,(t_[a298,top]@[],vec:25)),(iev@654,(t_[a437,a164,a298,top]@[],vec:168)),(iev@722,(t_[a437,a164,a298,top]@[],vec:168)),(iev@766,(t_[a437,a164,a298,top]@[],vec:168)),(xs,(t_[a437,a164,a298,top]@[],vec:178))]
RV (ROp (DVal {dLabel = xs, dOpName = std/core/types/local-get, dExpr = AppParam vec:272 0 local-get(xs, iev@722), dArgs = [], dCtx = d_[a184,a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])]}) d_[a184,a181,delim] FResume(d_[a292,a286,delim], K@(FLet((0,1,0,1,ix), [], LamBody([])),d_[a292,a286,delim],DFrameDone,DVal {dLabel = analysis/benchmarks/handlers/vec/vec, dOpName = push, dExpr = LamBody [s] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> push/@select), s), dArgs = [B@(s:d_[a304,a292,a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])])], dCtx = d_[a304,a292,a286,delim]@[((vec:79,analysis/benchmarks/handlers/vec/vec),d_[a184,a181,delim]),((vec:175,xs),t_[a437,a164,a298,top])]}), 237) DFrameDone K@(FLet((0,2,0,1,i), [], LamBody([s])),d_[a184,a181,delim],DFrameDone,DVal {dLabel = xs, dOpName = std/core/types/local-get, dExpr = AppParam vec:272 0 local-get(xs, iev@722), dArgs = [], dCtx = d_[a184,a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])]}))
Evaluating: rec { val len : forall<a> (ys : list<a>, acc : int) -> int; }
@open(len)(xs, 0):d_[a239,a184,a181,delim]@[] with env fromList [(xs,(d_[a239,a184,a181,delim]@[],list:457))]
Evaluating: match (ys) {
  (Cons(_, (yy)) : list<a> )
     -> len(yy, (@open((+))(acc, 1)));
  (@skip Nil() : (list<a>) )
     -> acc;
}:d_[a611,a239,a184,a181]@[] with env fromList [(acc,(d_[a611,a239,a184,a181]@[],list:610)),(len,(d_[a239,a184,a181,delim]@[],list:608)),(ys,(d_[a611,a239,a184,a181]@[],list:610))]
Result: match (ys) {
  (Cons(_, (yy)) : list<a> )
     -> len(yy, (@open((+))(acc, 1)));
  (@skip Nil() : (list<a>) )
     -> acc;
}:d_[a611,a239,a184,a181]@[] with env fromList [(acc,(d_[a611,a239,a184,a181]@[],list:610)),(len,(d_[a239,a184,a181,delim]@[],list:608)),(ys,(d_[a611,a239,a184,a181]@[],list:610))]
RV (RVAddr B@(acc:d_[a611,a239,a184,a181]@[]))
Result: rec { val len : forall<a> (ys : list<a>, acc : int) -> int; }
@open(len)(xs, 0):d_[a239,a184,a181,delim]@[] with env fromList [(xs,(d_[a239,a184,a181,delim]@[],list:457))]
RV (RVAddr B@(acc:d_[a611,a239,a184,a181]@[]))
Evaluating: local-set(xs, (@open((++))((local-get(xs, iev@766)), (Cons(s, Nil))))):d_[a184,a181,delim]@[] with env fromList [(i,(d_[a184,a181,delim]@[],vec:237)),(iev@722,(t_[a437,a164,a298,top]@[],vec:168)),(iev@766,(t_[a437,a164,a298,top]@[],vec:168)),(s,(d_[a184,a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])],vec:232)),(xs,(t_[a437,a164,a298,top]@[],vec:178))]
Evaluating: local-get(xs, iev@766):d_[a184,a181,delim]@[] with env fromList [(iev@766,(t_[a437,a164,a298,top]@[],vec:168)),(xs,(t_[a437,a164,a298,top]@[],vec:178))]
Result: local-get(xs, iev@766):d_[a184,a181,delim]@[] with env fromList [(iev@766,(t_[a437,a164,a298,top]@[],vec:168)),(xs,(t_[a437,a164,a298,top]@[],vec:178))]
RV (ROp (DVal {dLabel = xs, dOpName = std/core/types/local-get, dExpr = AppParam vec:253 0 local-get(xs, iev@766), dArgs = [], dCtx = d_[a184,a181,delim]@[]}) d_[a184,a181,delim] FrameDone DFrameDone EndKAddr)
Result: local-set(xs, (@open((++))((local-get(xs, iev@766)), (Cons(s, Nil))))):d_[a184,a181,delim]@[] with env fromList [(i,(d_[a184,a181,delim]@[],vec:237)),(iev@722,(t_[a437,a164,a298,top]@[],vec:168)),(iev@766,(t_[a437,a164,a298,top]@[],vec:168)),(s,(d_[a184,a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])],vec:232)),(xs,(t_[a437,a164,a298,top]@[],vec:178))]
RV (ROp (DVal {dLabel = xs, dOpName = std/core/types/local-get, dExpr = AppParam vec:253 0 local-get(xs, iev@766), dArgs = [], dCtx = d_[a184,a181,delim]@[]}) d_[a184,a181,delim] FApp(2, [], [BI@(250:d_[a184,a181,delim]@[]),B@(xs:t_[a437,a164,a298,top]@[])], LetDef(_)) DFrameDone K@(FApp(2, ["AppParam(Cons(s, Nil))"], [BI@(475:t_[top]@[])], AppParam(@open((++))((local-get(xs, iev@766)), (Cons(s, Nil))))),d_[a184,a181,delim],DFrameDone,DVal {dLabel = xs, dOpName = std/core/types/local-get, dExpr = AppParam vec:253 0 local-get(xs, iev@766), dArgs = [], dCtx = d_[a184,a181,delim]@[]}))
Evaluating: Cons(s, Nil):d_[a184,a181,delim]@[] with env fromList [(s,(d_[a184,a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])],vec:232))]
Result: Cons(s, Nil):d_[a184,a181,delim]@[] with env fromList [(s,(d_[a184,a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])],vec:232))]
RV (RVAddr BI@(254:d_[a184,a181,delim]@[]))
Evaluating: match (xs) {
  (Cons((x), (xx)) : list<a> )
     -> Cons(x, (@open(append)(xx, ys)));
  (@skip Nil() : (list<a>) )
     -> ys;
}:d_[a624,a249,a184,a181]@[] with env fromList [(xs,(d_[a624,a249,a184,a181]@[],list:473)),(ys,(d_[a624,a249,a184,a181]@[],list:473))]
Result: match (xs) {
  (Cons((x), (xx)) : list<a> )
     -> Cons(x, (@open(append)(xx, ys)));
  (@skip Nil() : (list<a>) )
     -> ys;
}:d_[a624,a249,a184,a181]@[] with env fromList [(xs,(d_[a624,a249,a184,a181]@[],list:473)),(ys,(d_[a624,a249,a184,a181]@[],list:473))]
RV (RVAddr B@(ys:d_[a624,a249,a184,a181]@[]))
Evaluating: Ix(i):d_[a184,a181,delim]@[((vec:181,xs),t_[a181,a437,a164,a298])] with env fromList [(i,(d_[a184,a181,delim]@[((vec:175,xs),t_[a437,a164,a298,top])],vec:237))]
Failed to compile analysis/benchmarks/handlers/vec.kk
