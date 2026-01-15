koka-3.2.3: unregistering (local file changes: src/Core/FlowAnalysis/Full/DMCFA/Syntax.hs)
koka> build (lib + exe) with ghc-9.6.6
Preprocessing library for koka-3.2.3..
Building library for koka-3.2.3..
[127 of 141] Compiling Core.FlowAnalysis.Full.DMCFA.Syntax [Source file changed]
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
Failed to compile analysis/benchmarks/handlers/vec.kk
