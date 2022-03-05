module test/optimization/handler
// handlers for the `:ask` effect
pub recursive type test/optimization/handler/.hnd-ask <(e :: E),a> :: (E, V) -> V {
  pub con test/optimization/handler/.Hnd-ask(fun-ask: (std/core/hnd/clause0 :: (V, (E, V) -> V, E, V) -> V)<string,(test/optimization/handler/.hnd-ask :: (E, V
   ) -> V),(e :: E),a>) : forall<(e :: E),a> (fun-ask : (std/core/hnd/clause0 :: (V, (E, V) -> V, E, V) -> V)<string,(test/optimization/handler/.hnd-ask :: (E
   , V) -> V),(e :: E),a>) -> (test/optimization/handler/.hnd-ask :: (E, V) -> V)<(e :: E),a>;
};
// `:ask` effect
pub type test/optimization/handler/ask :: HX1 {
  con test/optimization/handler/Ask<(e :: E),a>((test/optimization/handler/.hnd-ask :: (E, V) -> V)<(e :: E),a>) : forall<(e :: E),a> ((
   test/optimization/handler/.hnd-ask :: (E, V) -> V)<(e :: E),a>) -> (test/optimization/handler/ask :: HX1);
};
// runtime tag for the `:ask` effect
pub val .tag-ask : std/core/hnd/htag<test/optimization/handler/.hnd-ask>
  = std/core/hnd/.new-htag("ask.handler");
// handler for the `:ask` effect
pub fun .handle-ask : forall<a,e,b> (cfc : int32, hnd : test/optimization/handler/.hnd-ask<e,b>, ret : (res : a) -> e b, action : () -> <
   test/optimization/handler/ask|e> a) -> e b
  = forall<a,e,b> fn<e>(cfc: int32, hnd: test/optimization/handler/.hnd-ask<e,b>, ret: (res : a) -> e b, action: () -> <test/optimization/handler/ask|e> a){
    std/core/hnd/.hhandle(test/optimization/handler/.tag-ask, cfc, hnd, ret, action);
  };
// select `ask` operation out of the `:ask` effect handler
pub fun .select-ask : forall<e,a> (^ hnd : test/optimization/handler/.hnd-ask<e,a>) -> std/core/hnd/clause0<string,test/optimization/handler/.hnd-ask,e,a>
  = forall<e,a> fn(hnd: test/optimization/handler/.hnd-ask<e,a>){
    (match (hnd) {
      ((.skip test/optimization/handler/.Hnd-ask((fun-ask: std/core/hnd/clause0<string,test/optimization/handler/.hnd-ask,e,a>)) : 
   test/optimization/handler/.hnd-ask<e,a> ) as .pat: (test/optimization/handler/.hnd-ask<e,a>))
         -> fun-ask;
    });
  };
// call `ask` operation of the `:ask` effect
pub fun ask : () -> test/optimization/handler/ask string
  = fn<test/optimization/handler/ask>(){
    std/core/hnd/.perform0((std/core/types/.open(std/core/hnd/.evv-at)((std/core/types/.open(std/core/ssize_t)(0)))), test/optimization/handler/.select-ask);
  };
pub fun hello : () -> <test/optimization/handler/ask,console> ()
  = fn<<test/optimization/handler/ask,console>>(){
    val name : string
          = std/core/hnd/.perform0((std/core/types/.open(std/core/hnd/.evv-at)((std/core/types/.open(std/core/ssize_t)(0)))), test/optimization/handler/
   .select-ask);
    std/core/types/.open(std/core/printsln)((std/core/types/.open(std/core/(++.1))("Hello ", (std/core/types/.open(std/core/(++.1))(name, (std/core/types/.open
   (std/core/(++.1))(", ", (std/core/hnd/.perform0((std/core/types/.open(std/core/hnd/.evv-at)((std/core/types/.open(std/core/ssize_t)(0)))), 
   test/optimization/handler/.select-ask)))))))));
  };
pub fun main : () -> console ()
  = fn<console>(){
    test/optimization/handler/.handle-ask((std/core/int32(1)), (test/optimization/handler/.Hnd-ask((std/core/hnd/clause-tail-noyield0((fn<console>(){
        "there";
      }))))), (fn<console>(.x: ()){
        .x;
      }), test/optimization/handler/hello);
  };