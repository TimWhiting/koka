]4;0;?\[6nload    : std/core
load    : std/jsextern
load    : std/data/json
load    : std/async/async
load    : std/core/types
load    : std/core/undiv
load    : std/core/unsafe
load    : std/core/hnd
load    : std/core/bool
load    : std/core/exn
load    : std/core/vector
load    : std/core/int
load    : std/core/char
load    : std/core/order
load    : std/core/sslice
load    : std/core/list
load    : std/core/maybe
load    : std/core/maybe2
load    : std/core/tuple
load    : std/core/either
load    : std/core/show
load    : std/core/debug
load    : std/core/lazy
load    : std/core/console
load    : std/core/delayed
load    : std/data/dict
load    : std/num/int32
load    : std/num/ddouble
load    : std/time/duration
load    : std/data/array
load    : std/num/float64
load    : std/time/timestamp
load    : std/async/null
load    : std/async/timer
load    : async
load    : std/pretty/pprint
load    : std/core/string
load    : std/num/decimal
load    : std/text/parse
load    : std/num/int64
load    : std/time/date
load    : std/os/path
load    : std/pretty/printer
load    : std/os/file
load    : std/core-extras
load    : std/os/env
load    : std/os/dir
parse   : .../std/data/array.kk
parse   : .../std/data/dict.kk
parse   : .../std/async/async.kk
parse   : .../std/async.kk
parse   : .../std/jsextern.kk
parse   : .../examples/async/x.kk
check   : std/data/dict
check   : std/data/array
check   : std/async/async
/* Dictionary (or a string map)

   Todo.
*/
module std/data/dict
import std/core/types = std/core/types pub = "";
import std/core/hnd = std/core/hnd pub = "";
import std/core/exn = std/core/exn pub = "";
import std/core/bool = std/core/bool pub = "";
import std/core/order = std/core/order pub = "";
import std/core/char = std/core/char pub = "";
import std/core/int = std/core/int pub = "";
import std/core/vector = std/core/vector pub = "";
import std/core/string = std/core/string pub = "";
import std/core/sslice = std/core/sslice pub = "";
import std/core/list = std/core/list pub = "";
import std/core/maybe = std/core/maybe pub = "";
import std/core/maybe2 = std/core/maybe2 pub = "";
import std/core/either = std/core/either pub = "";
import std/core/tuple = std/core/tuple pub = "";
import std/core/lazy = std/core/lazy pub = "";
import std/core/show = std/core/show pub = "";
import std/core/debug = std/core/debug pub = "";
import std/core/delayed = std/core/delayed pub = "";
import std/core/console = std/core/console pub = "";
import std/core = std/core = "";
/* Mutable arrays

   Todo.
*/
module std/data/array
import std/core/types = std/core/types pub = "";
import std/core/hnd = std/core/hnd pub = "";
import std/core/exn = std/core/exn pub = "";
import std/core/bool = std/core/bool pub = "";
import std/core/order = std/core/order pub = "";
import std/core/char = std/core/char pub = "";
import std/core/int = std/core/int pub = "";
import std/core/vector = std/core/vector pub = "";
import std/core/string = std/core/string pub = "";
import std/core/sslice = std/core/sslice pub = "";
import std/core/list = std/core/list pub = "";
import std/core/maybe = std/core/maybe pub = "";
import std/core/maybe2 = std/core/maybe2 pub = "";
import std/core/either = std/core/either pub = "";
import std/core/tuple = std/core/tuple pub = "";
import std/core/lazy = std/core/lazy pub = "";
import std/core/show = std/core/show pub = "";
import std/core/debug = std/core/debug pub = "";
import std/core/delayed = std/core/delayed pub = "";
import std/core/console = std/core/console pub = "";
import std/core = std/core = "";
check   : async
check   : std/jsextern
check   : examples/async/x
/* Asynchronous primitives

This module is based closely on [@Leijen:async] and aims to have robust and composable asynchronous
primitives. In particular, any outstanding asynchronous operation can be canceled (through `cancel`)
within a certain scope which allows for composable primitives like `timeout` and `firstof`.


## References {-
~ Bibliography { caption:"0"~~ BibItem { #Leijen:async; bibitem-label:"[1]"; searchterm:"Leijen+Daan+Structured+Asynchrony+with+Algebraic+Effects"Daan Leijen.
_Structured Asynchrony with Algebraic Effects_.
Microsoft Research technical report MSR-TR-2017-21, May 2017.
[pdf](https://www.microsoft.com/en-us/research/wp-content/uploads/2017/05/asynceffects-msr-tr-2017-21.pdf)
~~
~
\/
*/
module std/async/async
import std/core/types = std/core/types pub = "";
import std/core/hnd = std/core/hnd pub = "";
import std/core/exn = std/core/exn pub = "";
import std/core/bool = std/core/bool pub = "";
import std/core/order = std/core/order pub = "";
import std/core/char = std/core/char pub = "";
import std/core/int = std/core/int pub = "";
import std/core/vector = std/core/vector pub = "";
import std/core/string = std/core/string pub = "";
import std/core/sslice = std/core/sslice pub = "";
import std/core/list = std/core/list pub = "";
import std/core/maybe = std/core/maybe pub = "";
import std/core/maybe2 = std/core/maybe2 pub = "";
import std/core/either = std/core/either pub = "";
import std/core/tuple = std/core/tuple pub = "";
import std/core/lazy = std/core/lazy pub = "";
import std/core/show = std/core/show pub = "";
import std/core/debug = std/core/debug pub = "";
import std/core/delayed = std/core/delayed pub = "";
import std/core/console = std/core/console pub = "";
import std/core = std/core = "";
import std/data/dict = std/data/dict = "";
import std/data/array = std/data/array = "";
import std/num/int32 = std/num/int32 = "";
pub import std/num/ddouble = std/num/ddouble = "";
import std/time/duration = std/time/duration = "";
import std/async/null = std/async/null = "";
import std/core/unsafe = std/core/unsafe = "";
pub import std/num/float64 = std/num/float64 = "";
import std/time/timestamp = std/time/timestamp = "";
// Index into an evidence vector
local alias hnd/ev-index = ssize_t = 1;
// The `:io` effect is used for functions that perform arbitrary I/O operations.
local alias io :: E = <(exn :: (E, V) -> V),((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>)> = 4;
// The `:io-noexn` effect is used for functions that perform arbitrary I/O operations, but raise no exceptions
local alias io-noexn :: E = <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)> = 3;
// The `:io-total` effect is used for functions that perform arbitrary I/O operations, but are terminating without raising exceptions.
local alias io-total :: E = <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)> = 2;
// Stateful functions can manipulate heap `:h` using allocations, reads and writes.
local alias st<(h :: H)> :: H -> E = <(read :: H -> X)<(h :: H)>,(write :: H -> X)<(h :: H)>,(alloc :: H -> X)<(h :: H)>> = 1;
;
pub value{0,1,8} type scope[594,1,594,36] {
  con Scope[594,17,594,21]((list :: V -> V)<int>){0,1,8} : ((list :: V -> V)<int>) -> scope = 1;
};
// Asynchronous operations have the `:async` effect.
pub recursive effect type async[457,1,461,34] <(e :: E),a> :: (E, V) -> V {
  pub con @Hnd-async[457,1,457,16](@cfc: int, @ctl-async-iox: forall<b> (hnd/clause1 :: (V, V, (E, V) -> V, E, V) -> V)<() -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) b,b,(async :: (E, V) -> V),(e :: E),a>, @ctl-cancel: (hnd/clause1 :: (V, V, (E, V) -> V, E, V) -> V)<scope,(),(async ::
   (E, V) -> V),(e :: E),a>, @ctl-do-await: forall<b> (hnd/clause1 :: (V, V, (E, V) -> V, E, V) -> V)<(((await-setup :: V -> V)<b> == 4 (cb : ((error :: V -> V)<b>, bool) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet 
   :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) (maybe :: V -> V)<() -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()>), scope, 
   bool),(error :: V -> V)<b>,(async :: (E, V) -> V),(e :: E),a>, @ctl-no-await: forall<b> (hnd/clause1 :: (V, V, (E, V) -> V, E, V) -> V)<(((await-setup :: V -> V)<b> == 4 (cb : ((error :: V -> V)<b>, bool) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()) -> ((io-noexn :: E) == 3 <(div
   :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) (maybe :: V -> V)<() -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(
   global :: H)>>)>)>) ()>), scope, bool, ((error :: V -> V)<b>) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()),(),(async :: (E, V) -> V),(e :: E),a>){0,5,8} : forall<(e :: E),a> (int, forall<b> (hnd/clause1 :: (V, V, (E, V) -> V, E, V) -> V)<() -> ((io-noexn :: E) == 3 <(div :: X),((
   io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) b,b,(async :: (E, V) -> V),(e :: E),a>, (hnd/clause1 :: (V, V, (E, V) -> V, E, V) -> V)<scope,(),(async :: (E, V) -> V),(e :: E),a>, forall<b> (hnd/clause1 :: (V, V, (E, V) -> V, E, V) -> V)<(((await-setup :: V -> V)<b> == 4 (cb : ((error :: V -> V)<b>, bool) -> ((io-noexn :: E
   ) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(
   global :: H)>>)>)>) (maybe :: V -> V)<() -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()>), scope, bool),(error :: V -> V)<b>,(async :: (E, V) -> V),(e :: E),a>, forall<b> (hnd/clause1 :: (V, V, (E, V) -> V, E, V) -> V)<(((await-setup :: V -> V)<b> == 4 (cb : ((error :: V -> V)<b>, 
   bool) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>
   ,(alloc :: H -> X)<(global :: H)>>)>)>) (maybe :: V -> V)<() -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()>), scope, bool, ((error :: V -> V)<b>) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: 
   H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()),(),(async :: (E, V) -> V),(e :: E),a>) -> (async :: (E, V) -> V)<(e :: E),a> = 1;
};
pub alias async-exn :: E = <(async :: (E, V) -> V),(exn :: (E, V) -> V)> = 1;
// A type alias for asynchronous operations that can raise exceptions non-deterministically.
// This is common for almost all `:async` operations since `cancel` and `timeout` can
// cancel operations non-deterministically which raises the `Cancel` exception and cancels
// outstanding asynchronous requests.
pub alias asyncx :: E = <(async :: (E, V) -> V),(exn :: (E, V) -> V),(ndet :: X)> = 1;
;
// todo: use queue data type for the values and listeners for better complexity
pub type channel-state[111,1,114,81] <a> :: V -> V {
  con Empty[112,3,112,7]{0,0,0} : forall<a> (channel-state :: V -> V)<a> = 1;
  con Values[113,3,113,8](value: a, values: (list :: V -> V)<a>){0,2,8} : forall<a> (value : a, values : (list :: V -> V)<a>) -> (channel-state :: V -> V)<a> = 2;
  con Waiting[114,3,114,9](listener: (a) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) (), listeners: (list :: V -> V)<(a) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <
   (read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()>){0,2,8} : forall<a> (listener : (a) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) (), listeners : (list :: V -> V)<(a) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2
   <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()>) -> (channel-state :: V -> V)<a> = 3;
};
// A _channel_ of values of type `:a`. Values can be asynchronously `emit`ed into
// a channel, and asynchronously `receive`d.
pub value{0,2,8} type channel[105,1,108,1] <a> :: V -> V {
  // A _channel_ of values of type `:a`. Values can be asynchronously `emit`ed into
// a channel, and asynchronously `receive`d.
  con Channel[105,23,105,29](chid: int, state: (ref :: (H, V) -> V)<(global :: H),(channel-state :: V -> V)<a>>){0,2,8} : forall<a> (chid : int, state : (ref :: (H, V) -> V)<(global :: H),(channel-state :: V -> V)<a>>) -> (channel :: V -> V)<a> = 1;
};
pub value{0,2,8} type promise-state[60,1,62,42] <a> :: V -> V {
  con Resolved[61,3,61,10](value: a){0,2,8} : forall<a> (value : a) -> (promise-state :: V -> V)<a> = 1;
  con Awaiting[62,3,62,10](listeners: (list :: V -> V)<(a) -> ((io :: E) == 4 <(exn :: (E, V) -> V),((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>)>) ()>){0,2,8} : forall<a> (listeners : (list :: V -> V)<(a) -> ((io :: E) == 4 <(exn :: (E, V) -> V),((io-noexn :: E) == 3 <(div :: X),((io-total
   :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>)>) ()>) -> (promise-state :: V -> V)<a> = 2;
};
// A _promise_ that carries a value of type `:a`. A promise is initially empty
// but can be `await`ed  asynchronously until it gets `resolve`d unblocking any
// `await` operations. After that a promise stays resolved and any `await` will
// return immediately. It is an error to try to resolve a promise more than once.
pub value{0,1,8} type promise[56,1,57,38] <a> :: V -> V {
  // A _promise_ that carries a value of type `:a`. A promise is initially empty
// but can be `await`ed  asynchronously until it gets `resolve`d unblocking any
// `await` operations. After that a promise stays resolved and any `await` will
// return immediately. It is an error to try to resolve a promise more than once.
  con Promise[56,17,56,23](state: (ref :: (H, V) -> V)<(global :: H),(promise-state :: V -> V)<a>>){0,1,8} : forall<a> (state : (ref :: (H, V) -> V)<(global :: H),(promise-state :: V -> V)<a>>) -> (promise :: V -> V)<a> = 1;
};
// Private effect to keep track of when a strand in an interleaving is done.
// Preferred over using built-in state as this works well if there is an outer handler
// over the state that resumes more than once -- redoing part of the interleaving.
// See `test/algeff/async5.js`
recursive effect type strands[311,1,315,52] <a,(e :: E),b> :: (V, E, V) -> V {
  con @Hnd-strands[311,1,311,14](@cfc: int, @fun-strand-done: (hnd/clause2 :: (V, V, V, (E, V) -> V, E, V) -> V)<int,(error :: V -> V)<a>,(),(strands :: (V, E, V) -> V)<a>,(e :: E),b>, @fun-strands-are-busy: (hnd/clause0 :: (V, (E, V) -> V, E, V) -> V)<bool,(strands :: (V, E, V) -> V)<a>,(e :: E),b>){0,3,8} : forall<a,(e :: E),b> (int, (hnd/clause2 :: (V, V, V, (E, V) -> V, E, V) -> V)<int,(error :: V -> V)<a>,(),(strands :: (V, E, V) -> V)<a>,(e :: E),b>, (hnd/clause0 :: (V, (E, V) -> V, E, V) -> V)<bool,
   (strands :: (V, E, V) -> V)<a>,(e :: E),b>) -> (strands :: (V, E, V) -> V)<a,(e :: E),b> = 1;
};
// abstract wid for timeout handlers
pub value{0,1,8} type timeout-id[236,1,238,1] {
  // abstract wid for timeout handlers
  con Timeout-id[236,17,236,26](timer: any){0,1,8} : (timer : any) -> timeout-id = 1;
};
;
pub extend type exception-info[639,1,641,30] {
  con Cancel[640,7,640,12]{0,1,8} : exception-info = 1;
  con Finalize[641,7,641,14](yld: hnd/yield-info){0,2,8} : (yld : hnd/yield-info) -> exception-info = 2;
};
// Automatically generated. Retrieves the `state` constructor field of the `:promise` type.
fun promise/state : forall<a> (^ promise : promise<a>) -> ref<global,promise-state<a>>
  = forall<a> fn(promise@0: promise<a>){
    (match (promise@0) {
      ((@skip std/async/async/Promise((@x: ref<global,promise-state<a>>)) : promise<a> ) as @pat: (promise<a>))
         -> @x;
    });
  };
pub fun promise/@copy : forall<a> (@this : promise<a>, state : ? (ref<global,promise-state<a>>)) -> promise<a>
  = forall<a> fn(@this: promise<a>, state: ? (ref<global,promise-state<a>>)){
    std/async/async/Promise((match (state) {
      ((std/core/types/@Optional((@uniq-state@824: ref<global,promise-state<a>>)) : ? (ref<global,promise-state<a>>) ) as @pat: ? (ref<global,promise-state<a>>))
         -> @uniq-state@824;
      ((@skip std/core/types/@None() : ? (ref<global,promise-state<a>>) ) as @pat@0: ? (ref<global,promise-state<a>>))
         -> (match (@this) {
          ((@skip std/async/async/Promise((@x: ref<global,promise-state<a>>)) : promise<a> ) as @pat@1: (promise<a>))
             -> @x;
        });
    }));
  };
// Automatically generated. Tests for the `Resolved` constructor of the `:promise-state` type.
fip fun is-resolved : forall<a> (^ promise-state : promise-state<a>) -> bool
  = forall<a> fn(promise-state: promise-state<a>){
    (match (promise-state) {
      ((std/async/async/Resolved((@pat@0: a)) : promise-state<a> ) as @pat: (promise-state<a>))
         -> std/core/types/True;
      (@pat@1: (promise-state<a>))
         -> std/core/types/False;
    });
  };
// Automatically generated. Tests for the `Awaiting` constructor of the `:promise-state` type.
fip fun is-awaiting : forall<a> (^ promise-state : promise-state<a>) -> bool
  = forall<a> fn(promise-state: promise-state<a>){
    (match (promise-state) {
      ((std/async/async/Awaiting((@pat@0: list<(a) -> (io == 4 <exn,(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>) ()>)) : promise-state<a> ) as @pat: (promise-state<a>))
         -> std/core/types/True;
      (@pat@1: (promise-state<a>))
         -> std/core/types/False;
    });
  };
// Automatically generated. Retrieves the `chid` constructor field of the `:channel` type.
fun channel/chid : forall<a> (^ channel : channel<a>) -> int
  = forall<a> fn(channel@0: channel<a>){
    (match (channel@0) {
      ((@skip std/async/async/Channel((@x: int), (@pat@0: ref<global,channel-state<a>>)) : channel<a> ) as @pat: (channel<a>))
         -> @x;
    });
  };
// Automatically generated. Retrieves the `state` constructor field of the `:channel` type.
fun channel/state : forall<a> (^ channel : channel<a>) -> ref<global,channel-state<a>>
  = forall<a> fn(channel@0: channel<a>){
    (match (channel@0) {
      ((@skip std/async/async/Channel((@pat@0: int), (@x: ref<global,channel-state<a>>)) : channel<a> ) as @pat: (channel<a>))
         -> @x;
    });
  };
pub fun channel/@copy : forall<a> (@this : channel<a>, chid : ? int, state : ? (ref<global,channel-state<a>>)) -> channel<a>
  = forall<a> fn(@this: channel<a>, chid: ? int, state: ? (ref<global,channel-state<a>>)){
    std/async/async/Channel((match (chid) {
        ((std/core/types/@Optional((@uniq-chid@929: int)) : ? int ) as @pat: ? int)
           -> @uniq-chid@929;
        ((@skip std/core/types/@None() : ? int ) as @pat@0: ? int)
           -> (match (@this) {
            ((@skip std/async/async/Channel((@x: int), (@pat@0@0: ref<global,channel-state<a>>)) : channel<a> ) as @pat@1: (channel<a>))
               -> @x;
          });
      }), (match (state) {
        ((std/core/types/@Optional((@uniq-state@940: ref<global,channel-state<a>>)) : ? (ref<global,channel-state<a>>) ) as @pat@1@0: ? (ref<global,channel-state<a>>))
           -> @uniq-state@940;
        ((@skip std/core/types/@None() : ? (ref<global,channel-state<a>>) ) as @pat@2: ? (ref<global,channel-state<a>>))
           -> (match (@this) {
            ((@skip std/async/async/Channel((@pat@0@1: int), (@x@0: ref<global,channel-state<a>>)) : channel<a> ) as @pat@3: (channel<a>))
               -> @x@0;
          });
      }));
  };
fun @create-Values : forall<a> (value : a, values : ? (list<a>)) -> channel-state<a>
  = forall<a> fn(value: a, values: ? (list<a>)){
    std/async/async/Values(value, (match (values) {
        ((std/core/types/@Optional((@uniq-values@967: list<a>)) : ? (list<a>) ) as @pat: ? (list<a>))
           -> @uniq-values@967;
        ((@skip std/core/types/@None() : ? (list<a>) ) as @pat@0: ? (list<a>))
           -> std/core/types/Nil;
      }));
  };
fun @create-Waiting : forall<a> (listener : (a) -> io-noexn (), listeners : ? (list<(a) -> io-noexn ()>)) -> channel-state<a>
  = forall<a> fn(listener: (a) -> io-noexn (), listeners: ? (list<(a) -> io-noexn ()>)){
    std/async/async/Waiting(listener, (match (listeners) {
        ((std/core/types/@Optional((@uniq-listeners@994: list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)) : ? (list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>) ) as @pat: ? (list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<
   global>>)>)>) ()>))
           -> @uniq-listeners@994;
        ((@skip std/core/types/@None() : ? (list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>) ) as @pat@0: ? (list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>))
           -> std/core/types/Nil;
      }));
  };
// Automatically generated. Retrieves the `timer` constructor field of the `:timeout-id` type.
fun timeout-id/timer : (^ @this : timeout-id) -> any
  = fn(@this: timeout-id){
    match (@this) {
      ((@skip std/async/async/Timeout-id((@x: any)) : timeout-id ) as @pat: timeout-id)
         -> @x;
    };
  };
pub fun timeout-id/@copy : (@this : timeout-id, timer : ? any) -> timeout-id
  = fn(@this: timeout-id, timer: ? any){
    std/async/async/Timeout-id((match (timer) {
      ((std/core/types/@Optional((@uniq-timer@1032: any)) : ? any ) as @pat: ? any)
         -> @uniq-timer@1032;
      ((@skip std/core/types/@None() : ? any ) as @pat@0: ? any)
         -> (match (@this) {
          ((@skip std/async/async/Timeout-id((@x: any)) : timeout-id ) as @pat@1: timeout-id)
             -> @x;
        });
    }));
  };
// Automatically generated. Retrieves the `@cfc` constructor field of the `:strands` type.
fun strands/@cfc : forall<a,e,b> (^ strands : strands<a,e,b>) -> int
  = forall<a,e,b> fn(strands: strands<a,e,b>){
    (match (strands) {
      ((@skip std/async/async/@Hnd-strands((@x: int), (@pat@0: hnd/clause2<int,error<a>,(),strands<a>,e,b>), (@pat@1: hnd/clause0<bool,strands<a>,e,b>)) : strands<a,e,b> ) as @pat: (strands<a,e,b>))
         -> @x;
    });
  };
// runtime tag for the effect `:strands`
val strands/@tag : forall<a> hnd/htag<strands<a>>
  = forall<a> std/core/hnd/Htag("strands@async");
// handler for the effect `:strands`
fun strands/@handle : forall<a,b,e,c> (hnd : strands<a,e,c>, ret : (res : b) -> e c, action : () -> <strands<a>|e> b) -> e c
  = forall<a,b,e,c> fn<e>(hnd: strands<a,e,c>, ret: (res : b) -> e c, action: () -> <strands<a>|e> b){
    std/core/hnd/@hhandle(std/async/async/strands/@tag, hnd, ret, action);
  };
// Automatically generated. Retrieves the `@fun-strands-are-busy` constructor field of the `:strands` type.
fun strands/@fun-strands-are-busy : forall<a,e,b> (^ strands : strands<a,e,b>) -> hnd/clause0<bool,strands<a>,e,b>
  = forall<a,e,b> fn(strands: strands<a,e,b>){
    (match (strands) {
      ((@skip std/async/async/@Hnd-strands((@pat@0: int), (@pat@1: hnd/clause2<int,error<a>,(),strands<a>,e,b>), (@x: hnd/clause0<bool,strands<a>,e,b>)) : strands<a,e,b> ) as @pat: (strands<a,e,b>))
         -> @x;
    });
  };
// select `strands-are-busy` operation out of effect `:strands`
fun strands-are-busy/@select : forall<a,e,b> (^ hnd : strands<a,e,b>) -> hnd/clause0<bool,strands<a>,e,b>
  = forall<a,e,b> fn(hnd: strands<a,e,b>){
    (match (hnd) {
      ((@skip std/async/async/@Hnd-strands((@pat@0: int), (@pat@1: hnd/clause2<int,error<a>,(),strands<a>,e,b>), (@fun-strands-are-busy: hnd/clause0<bool,strands<a>,e,b>)) : strands<a,e,b> ) as @pat: (strands<a,e,b>))
         -> @fun-strands-are-busy;
    });
  };
// Automatically generated. Retrieves the `@fun-strand-done` constructor field of the `:strands` type.
fun strands/@fun-strand-done : forall<a,e,b> (^ strands : strands<a,e,b>) -> hnd/clause2<int,error<a>,(),strands<a>,e,b>
  = forall<a,e,b> fn(strands: strands<a,e,b>){
    (match (strands) {
      ((@skip std/async/async/@Hnd-strands((@pat@0: int), (@x: hnd/clause2<int,error<a>,(),strands<a>,e,b>), (@pat@1: hnd/clause0<bool,strands<a>,e,b>)) : strands<a,e,b> ) as @pat: (strands<a,e,b>))
         -> @x;
    });
  };
// select `strand-done` operation out of effect `:strands`
fun strand-done/@select : forall<a,e,b> (^ hnd : strands<a,e,b>) -> hnd/clause2<int,error<a>,(),strands<a>,e,b>
  = forall<a,e,b> fn(hnd: strands<a,e,b>){
    (match (hnd) {
      ((@skip std/async/async/@Hnd-strands((@pat@0: int), (@fun-strand-done: hnd/clause2<int,error<a>,(),strands<a>,e,b>), (@pat@1: hnd/clause0<bool,strands<a>,e,b>)) : strands<a,e,b> ) as @pat: (strands<a,e,b>))
         -> @fun-strand-done;
    });
  };
// Automatically generated. Retrieves the `@cfc` constructor field of the `:async` type.
fun async/@cfc : forall<e,a> (^ async : async<e,a>) -> int
  = forall<e,a> fn(async: async<e,a>){
    (match (async) {
      ((@skip std/async/async/@Hnd-async((@x: int), (@pat@0: forall<b> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) b,b,async,e,a>), (@pat@1: hnd/clause1<scope,(),async,e,a>), (@pat@2: forall<b> hnd/clause1<((await-setup<b> == 4 (cb : (error<b>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (
   io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<b>,async,e,a>), (@pat@3: (forall<b> hnd/clause1<((await-setup<b> == 4 (cb : (error<b>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<
   global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<b>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async,e,a>))) : 
   async<e,a> ) as @pat: (async<e,a>))
         -> @x;
    });
  };
// runtime tag for the effect `:async`
pub val async/@tag : hnd/htag<async>
  = std/core/hnd/Htag("async@async");
// handler for the effect `:async`
pub fun async/@handle : forall<a,e,b> (hnd : async<e,b>, ret : (res : a) -> e b, action : () -> <async|e> a) -> e b
  = forall<a,e,b> fn<e>(hnd: async<e,b>, ret: (res : a) -> e b, action: () -> <async|e> a){
    std/core/hnd/@hhandle(std/async/async/async/@tag, hnd, ret, action);
  };
// Automatically generated. Retrieves the `@ctl-do-await` constructor field of the `:async` type.
fun async/@ctl-do-await : forall<e,a,b> (^ async : async<e,a>) -> hnd/clause1<(await-setup<b>, scope, bool),error<b>,async,e,a>
  = forall<e,a,b> fn(async: async<e,a>){
    (match (async) {
      ((@skip std/async/async/@Hnd-async((@pat@0: int), (@pat@1: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e,a>), (@pat@2: hnd/clause1<scope,(),async,e,a>), (@x: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (
   io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e,a>), (@pat@3: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<
   global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async,e,a>))) : 
   async<e,a> ) as @pat: (async<e,a>))
         -> @x;
    });
  };
// select `do-await` operation out of effect `:async`
pub fun do-await/@select : forall<a,e,b> (^ hnd : async<e,b>) -> hnd/clause1<(await-setup<a>, scope, bool),error<a>,async,e,b>
  = forall<a,e,b> fn(hnd: async<e,b>){
    (match (hnd) {
      ((@skip std/async/async/@Hnd-async((@pat@0: int), (@pat@1: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e,b>), (@pat@2: hnd/clause1<scope,(),async,e,b>), (@ctl-do-await: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) 
   -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e,b>), (@pat@3: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,
   write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async,e,b>)))
   : async<e,b> ) as @pat: (async<e,b>))
         -> @ctl-do-await;
    });
  };
// Call the `ctl do-await` operation of the effect `:async`
pub fun do-await : forall<a> (setup : await-setup<a>, scope : scope, cancelable : bool) -> async error<a>
  = forall<a> fn<async>(setup: await-setup<a>, scope: scope, cancelable@0: bool){
    val ev@11469 : hnd/ev<async>
          = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
    (match (ev@11469) {
      ((@skip std/core/hnd/Ev<e,b>((@pat@0: hnd/htag<async>), (m: hnd/marker<e,b>), (h: async<e,b>), (@pat@1: hnd/evv<e>)) : hnd/ev<async> ) as @pat: (hnd/ev<async>))
         -> (match (h) {
          ((@skip std/async/async/@Hnd-async((@pat@0@0: int), (@pat@1@0: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e,b>), (@pat@2@0: hnd/clause1<scope,(),async,e,b>), (@ctl-do-await: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>
   )>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e,b>), (@pat@3: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async
   ,e,b>))) : async<e,b> ) as @pat@2: (async<e,b>))
             -> (match (@ctl-do-await) {
              ((@skip std/core/hnd/Clause1((f: (hnd/marker<e,b>, hnd/ev<async>, ((await-setup<a> == 4 (cb : (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()>), scope, bool)) -> e error<a>)) : hnd/clause1<((await-setup<a> == 4 (cb : (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global>
   == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<a>,async,e,b> ) as @pat@2@1: (hnd/clause1<((await-setup<a> == 4 (cb : (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/
   console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<a>,async,e,b>))
                 -> f(m, ev@11469, (std/core/types/Tuple3(setup, scope, cancelable@0)));
            });
        });
    });
  };
// Automatically generated. Retrieves the `@ctl-no-await` constructor field of the `:async` type.
fun async/@ctl-no-await : forall<e,a,b> (^ async : async<e,a>) -> hnd/clause1<(await-setup<b>, scope, bool, (error<b>) -> io-noexn ()),(),async,e,a>
  = forall<e,a,b> fn(async: async<e,a>){
    (match (async) {
      ((@skip std/async/async/@Hnd-async((@pat@0: int), (@pat@1: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e,a>), (@pat@2: hnd/clause1<scope,(),async,e,a>), (@pat@3: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (
   io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e,a>), (@x: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global
   >,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async,e,a>))) : async<e,a
   > ) as @pat: (async<e,a>))
         -> @x;
    });
  };
// select `no-await` operation out of effect `:async`
pub fun no-await/@select : forall<a,e,b> (^ hnd : async<e,b>) -> hnd/clause1<(await-setup<a>, scope, bool, (error<a>) -> io-noexn ()),(),async,e,b>
  = forall<a,e,b> fn(hnd: async<e,b>){
    (match (hnd) {
      ((@skip std/async/async/@Hnd-async((@pat@0: int), (@pat@1: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e,b>), (@pat@2: hnd/clause1<scope,(),async,e,b>), (@pat@3: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (
   io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e,b>), (@ctl-no-await: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,
   write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async,e,b>)))
   : async<e,b> ) as @pat: (async<e,b>))
         -> @ctl-no-await;
    });
  };
// Call the `ctl no-await` operation of the effect `:async`
pub fun no-await : forall<a> (setup : await-setup<a>, scope : scope, cancelable : bool, f : (error<a>) -> io-noexn ()) -> async ()
  = forall<a> fn<async>(setup: await-setup<a>, scope: scope, cancelable@0: bool, f: (error<a>) -> io-noexn ()){
    val ev@11474 : hnd/ev<async>
          = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
    (match (ev@11474) {
      ((@skip std/core/hnd/Ev<e,b>((@pat@0: hnd/htag<async>), (m: hnd/marker<e,b>), (h: async<e,b>), (@pat@1: hnd/evv<e>)) : hnd/ev<async> ) as @pat: (hnd/ev<async>))
         -> (match (h) {
          ((@skip std/async/async/@Hnd-async((@pat@0@0: int), (@pat@1@0: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e,b>), (@pat@2@0: hnd/clause1<scope,(),async,e,b>), (@pat@3: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) 
   ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e,b>), (@ctl-no-await: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async
   ,e,b>))) : async<e,b> ) as @pat@2: (async<e,b>))
             -> (match (@ctl-no-await) {
              ((@skip std/core/hnd/Clause1((f@0: (hnd/marker<e,b>, hnd/ev<async>, ((await-setup<a> == 4 (cb : (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<a>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())) -> e ())) : hnd/clause1<((await-setup<a> == 4 (cb : (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global>
   == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<a>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async,e,b> ) as @pat@2@1: (hnd/clause1<((await-setup<a> == 4 (cb : (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console
   /console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<a>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,
   write<global>,alloc<global>>)>)>) ()),(),async,e,b>))
                 -> f@0(m, ev@11474, (std/core/types/Tuple4(setup, scope, cancelable@0, f)));
            });
        });
    });
  };
// Automatically generated. Retrieves the `@ctl-async-iox` constructor field of the `:async` type.
fun async/@ctl-async-iox : forall<e,a,b> (^ async : async<e,a>) -> hnd/clause1<() -> io-noexn b,b,async,e,a>
  = forall<e,a,b> fn(async: async<e,a>){
    (match (async) {
      ((@skip std/async/async/@Hnd-async((@pat@0: int), (@x: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e,a>), (@pat@1: hnd/clause1<scope,(),async,e,a>), (@pat@2: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (
   io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e,a>), (@pat@3: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<
   global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async,e,a>))) : 
   async<e,a> ) as @pat: (async<e,a>))
         -> @x;
    });
  };
// select `async-iox` operation out of effect `:async`
pub fun async-iox/@select : forall<a,e,b> (^ hnd : async<e,b>) -> hnd/clause1<() -> io-noexn a,a,async,e,b>
  = forall<a,e,b> fn(hnd: async<e,b>){
    (match (hnd) {
      ((@skip std/async/async/@Hnd-async((@pat@0: int), (@ctl-async-iox: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e,b>), (@pat@1: hnd/clause1<scope,(),async,e,b>), (@pat@2: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())
   -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e,b>), (@pat@3: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,
   write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async,e,b>)))
   : async<e,b> ) as @pat: (async<e,b>))
         -> @ctl-async-iox;
    });
  };
// Call the `ctl async-iox` operation of the effect `:async`
pub fun async-iox : forall<a> (action : () -> io-noexn a) -> async a
  = forall<a> fn<async>(action: () -> io-noexn a){
    val ev@11480 : hnd/ev<async>
          = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
    (match (ev@11480) {
      ((@skip std/core/hnd/Ev<e,b>((@pat@0: hnd/htag<async>), (m: hnd/marker<e,b>), (h: async<e,b>), (@pat@1: hnd/evv<e>)) : hnd/ev<async> ) as @pat: (hnd/ev<async>))
         -> (match (h) {
          ((@skip std/async/async/@Hnd-async((@pat@0@0: int), (@ctl-async-iox: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e,b>), (@pat@1@0: hnd/clause1<scope,(),async,e,b>), (@pat@2@0: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>
   >)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e,b>), (@pat@3: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async
   ,e,b>))) : async<e,b> ) as @pat@2: (async<e,b>))
             -> (match (@ctl-async-iox) {
              ((@skip std/core/hnd/Clause1((f: (hnd/marker<e,b>, hnd/ev<async>, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) a) -> e a)) : hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) a,a,async,e,b> ) as @pat@2@1: (hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<
   global> == 1 <read<global>,write<global>,alloc<global>>)>)>) a,a,async,e,b>))
                 -> f(m, ev@11480, action);
            });
        });
    });
  };
// Create a new promise.
pub fun promise : forall<a> () -> async promise<a>
  = forall<a> fn<async>(){
    val ev@11483 : hnd/ev<async>
          = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
    (match (ev@11483) {
      ((@skip std/core/hnd/Ev<e,b>((@pat@0: hnd/htag<async>), (m: hnd/marker<e,b>), (h: async<e,b>), (@pat@1: hnd/evv<e>)) : hnd/ev<async> ) as @pat: (hnd/ev<async>))
         -> (match (h) {
          ((@skip std/async/async/@Hnd-async((@pat@0@0: int), (@ctl-async-iox: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e,b>), (@pat@1@0: hnd/clause1<scope,(),async,e,b>), (@pat@2@0: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>
   >)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e,b>), (@pat@3: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async
   ,e,b>))) : async<e,b> ) as @pat@2: (async<e,b>))
             -> (match (@ctl-async-iox) {
              ((@skip std/core/hnd/Clause1((f: (hnd/marker<e,b>, hnd/ev<async>, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) promise<a>) -> e promise<a>)) : hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) promise<a>,promise<a>,async,e,b> ) as @pat@2@1: (hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet
   ,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) promise<a>,promise<a>,async,e,b>))
                 -> f(m, ev@11483, (fn<(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>(){
                    (std/async/async/Promise((std/core/types/ref((std/async/async/Awaiting(std/core/types/Nil))))));
                  }));
            });
        });
    });
  };
// Automatically generated. Retrieves the `@ctl-cancel` constructor field of the `:async` type.
fun async/@ctl-cancel : forall<e,a> (^ async : async<e,a>) -> hnd/clause1<scope,(),async,e,a>
  = forall<e,a> fn(async: async<e,a>){
    (match (async) {
      ((@skip std/async/async/@Hnd-async((@pat@0: int), (@pat@1: forall<b> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) b,b,async,e,a>), (@x: hnd/clause1<scope,(),async,e,a>), (@pat@2: forall<b> hnd/clause1<((await-setup<b> == 4 (cb : (error<b>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (
   io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<b>,async,e,a>), (@pat@3: (forall<b> hnd/clause1<((await-setup<b> == 4 (cb : (error<b>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<
   global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<b>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async,e,a>))) : 
   async<e,a> ) as @pat: (async<e,a>))
         -> @x;
    });
  };
// select `cancel` operation out of effect `:async`
pub fun cancel/@select : forall<e,a> (^ hnd : async<e,a>) -> hnd/clause1<scope,(),async,e,a>
  = forall<e,a> fn(hnd: async<e,a>){
    (match (hnd) {
      ((@skip std/async/async/@Hnd-async((@pat@0: int), (@pat@1: forall<b> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) b,b,async,e,a>), (@ctl-cancel: hnd/clause1<scope,(),async,e,a>), (@pat@2: forall<b> hnd/clause1<((await-setup<b> == 4 (cb : (error<b>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) ->
   (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<b>,async,e,a>), (@pat@3: (forall<b> hnd/clause1<((await-setup<b> == 4 (cb : (error<b>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<
   global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<b>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async,e,a>))) : 
   async<e,a> ) as @pat: (async<e,a>))
         -> @ctl-cancel;
    });
  };
// Call the `ctl cancel` operation of the effect `:async`
pub fun cancel : (scope : scope) -> async ()
  = fn<async>(scope: scope){
    val ev@11486 : hnd/ev<async>
          = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
    match (ev@11486) {
      ((@skip std/core/hnd/Ev<e,a>((@pat@0: hnd/htag<async>), (m: hnd/marker<e,a>), (h: async<e,a>), (@pat@1: hnd/evv<e>)) : hnd/ev<async> ) as @pat: (hnd/ev<async>))
         -> (match (h) {
          ((@skip std/async/async/@Hnd-async((@pat@0@0: int), (@pat@1@0: forall<b> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) b,b,async,e,a>), (@ctl-cancel: hnd/clause1<scope,(),async,e,a>), (@pat@2@0: forall<b> hnd/clause1<((await-setup<b> == 4 (cb : (error<b>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>
   )>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<b>,async,e,a>), (@pat@3: (forall<b> hnd/clause1<((await-setup<b> == 4 (cb : (error<b>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<b>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async
   ,e,a>))) : async<e,a> ) as @pat@2: (async<e,a>))
             -> (match (@ctl-cancel) {
              ((@skip std/core/hnd/Clause1((f: (hnd/marker<e,a>, hnd/ev<async>, scope) -> e ())) : hnd/clause1<scope,(),async,e,a> ) as @pat@2@1: (hnd/clause1<scope,(),async,e,a>))
                 -> f(m, ev@11486, scope);
            });
        });
    };
  };
pub fun scope/@copy : (@this : scope, list<int>) -> scope
  = fn(@this: scope, @field-x1: list<int>){
    std/async/async/Scope(@field-x1);
  };
val empty-scope : scope
  = std/async/async/Scope(std/core/types/Nil);
// The `cancel` operations cancels any outstanding asynchronous operation under the innermost
// `cancelable` handler by returning the `Cancel` exception. The `cancel` operation itself returns normally
// without raising a `Cancel` exception.
pub fun noscope/cancel : () -> async ()
  = fn<async>(){
    val ev@11489 : hnd/ev<async>
          = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
    match (ev@11489) {
      ((@skip std/core/hnd/Ev<e,a>((@pat@0: hnd/htag<async>), (m: hnd/marker<e,a>), (h: async<e,a>), (@pat@1: hnd/evv<e>)) : hnd/ev<async> ) as @pat: (hnd/ev<async>))
         -> (match (h) {
          ((@skip std/async/async/@Hnd-async((@pat@0@0: int), (@pat@1@0: forall<b> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) b,b,async,e,a>), (@ctl-cancel: hnd/clause1<scope,(),async,e,a>), (@pat@2@0: forall<b> hnd/clause1<((await-setup<b> == 4 (cb : (error<b>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>
   )>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<b>,async,e,a>), (@pat@3: (forall<b> hnd/clause1<((await-setup<b> == 4 (cb : (error<b>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<b>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async
   ,e,a>))) : async<e,a> ) as @pat@2: (async<e,a>))
             -> (match (@ctl-cancel) {
              ((@skip std/core/hnd/Clause1((f: (hnd/marker<e,a>, hnd/ev<async>, scope) -> e ())) : hnd/clause1<scope,(),async,e,a> ) as @pat@2@1: (hnd/clause1<scope,(),async,e,a>))
                 -> f(m, ev@11489, std/async/async/empty-scope);
            });
        });
    };
  };
// monadic lift
fun @mlift-await-exn@11379 : (@y-x10845 : maybe<() -> io-noexn ()>) -> io error<maybe<() -> io-noexn ()>>
  = fn<io>(@y-x10845: maybe<() -> io-noexn ()>){
    std/core/exn/Ok(@y-x10845);
  };
// Primitive: Execute `setup` to set up an asynchronous callback with the host platform. Invoke `cb` as the callback:
// it takes either an exception or a result `a`. Usually `setup` returns `Nothing` but you can return a `Just(cleanup)`
// value where the `cleanup` functions is invoked on cancellation to dispose of any resources (see the implementation of `wait`).
// The callback should be invoked exactly once -- when that happens `await-exn` is resumed with the result.
pub fun await-exn : forall<a> (setup : (cb : (error<a>) -> io-noexn ()) -> io maybe<() -> io-noexn ()>) -> async error<a>
  = forall<a> fn<async>(setup: (cb : (error<a>) -> io-noexn ()) -> io maybe<() -> io-noexn ()>){
    val ev@11492 : hnd/ev<async>
          = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
    (match (ev@11492) {
      ((@skip std/core/hnd/Ev<e,b>((@pat@0: hnd/htag<async>), (m: hnd/marker<e,b>), (h: async<e,b>), (@pat@1: hnd/evv<e>)) : hnd/ev<async> ) as @pat: (hnd/ev<async>))
         -> (match (h) {
          ((@skip std/async/async/@Hnd-async((@pat@0@0: int), (@pat@1@0: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e,b>), (@pat@2@0: hnd/clause1<scope,(),async,e,b>), (@ctl-do-await: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>
   )>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e,b>), (@pat@3: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async
   ,e,b>))) : async<e,b> ) as @pat@2: (async<e,b>))
             -> (match (@ctl-do-await) {
              ((@skip std/core/hnd/Clause1((f: (hnd/marker<e,b>, hnd/ev<async>, ((await-setup<a> == 4 (cb : (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()>), scope, bool)) -> e error<a>)) : hnd/clause1<((await-setup<a> == 4 (cb : (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global>
   == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<a>,async,e,b> ) as @pat@2@1: (hnd/clause1<((await-setup<a> == 4 (cb : (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/
   console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<a>,async,e,b>))
                 -> f(m, ev@11492, (std/core/types/Tuple3((fn<(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>(cb: (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()){
                      (match ((std/core/exn/exn/@handle((std/core/exn/@Hnd-exn(0, (forall<c> std/core/hnd/Clause1((fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(m@0: hnd/marker<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>,error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>>, @_wildcard-x653_16: hnd/ev<exn>, x: exception){
                            (std/core/hnd/yield-to-final(m@0, (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@_wildcard-x653_45: (hnd/resume-result<c,error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>>) -> <alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>> error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,
   fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>){
                                (std/core/exn/Error(x));
                              })));
                          }))))), (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@res: error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>){
                          @res;
                        }), (fn<<exn,alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(){
                          val x@0@11498 : (maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)
                                = (setup((fn<(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>(res: error<a>){
                                  (cb(res, std/core/types/True));
                                })));
                          (match ((std/core/hnd/yielding())) {
                            ((std/core/types/True() : bool ) as @pat@3@0: bool)
                               -> std/core/hnd/yield-extend(std/async/async/@mlift-await-exn@11379);
                            ((@skip std/core/types/False() : bool ) as @pat@0@0@0: bool)
                               -> std/core/exn/Ok(x@0@11498);
                          });
                        })))) {
                        ((std/core/exn/Ok((mcleanup: maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)) : error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>> ) as @pat@4: (error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,
   alloc<global>>)>)>) ()>>))
                           -> mcleanup;
                        ((@skip std/core/exn/Error(((@skip std/core/exn/Exception((@pat@1@0@0: string), (@pat@2@0@0: exception-info)) : exception ) as exn: exception)) : error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>> ) as @pat@0@1: (error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>))
                           -> val _ : ()
                                    = cb((std/core/exn/Error(exn)), std/core/types/True);
                          std/core/types/Nothing;
                      });
                    }), std/async/async/empty-scope, std/core/types/True)));
            });
        });
    });
  };
// monadic lift
fun setup/@mlift-await@11380 : forall<a> (@y-x10849 : error<a>) -> <async,exn,ndet> a
  = forall<a> fn<<async,exn,ndet>>(@y-x10849: error<a>){
    val i@11500 : hnd/ev-index
      = std/core/types/@make-ssize_t(1);
    val w : hnd/evv<<exn,async,ndet>>
      = std/core/hnd/evv-swap-create1(i@11500);
    val y : a
      = (match (@y-x10849) {
        ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@0: string), (@pat@1@0: exception-info)) : exception ) as exn@0: exception)) : error<a> ) as @pat@1: (error<a>))
           -> val ev@11503 : hnd/ev<exn>
                    = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
          (match (ev@11503) {
            ((@skip std/core/hnd/Ev<e,b>((@pat@0@1: hnd/htag<exn>), (m: hnd/marker<e,b>), (h: exn<e,b>), (@pat@1@1: hnd/evv<e>)) : hnd/ev<exn> ) as @pat@2: (hnd/ev<exn>))
               -> (match ((std/core/exn/throw-exn/@select(h))) {
                ((@skip std/core/hnd/Clause1((f@0: (hnd/marker<e,b>, hnd/ev<exn>, exception) -> e a)) : hnd/clause1<exception,a,exn,e,b> ) as @pat@2@0: (hnd/clause1<exception,a,exn,e,b>))
                   -> f@0(m, ev@11503, exn@0);
              });
          });
        ((@skip std/core/exn/Ok((x@1: a)) : error<a> ) as @pat@2@1: (error<a>))
           -> x@1;
      });
    val _ : ()
      = std/core/hnd/evv-set(w);
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-cont((forall<b> fn<<exn,async,ndet>>(cont: (b) -> <exn,async,ndet> a, res: b){
          std/core/hnd/open-at1(i@11500, cont, res);
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> y;
    });
  };
// Execute `setup` to set up an asynchronous callback with the host platform. Invoke `cb` as the callback:
// it takes either an exception or a result `a`. Usually `setup` returns `Nothing` but you can return a `Just(cleanup)`
// value where the `cleanup` functions is invoked on cancellation to dispose of any resources (see the implementation of `wait`).
// The callback should be invoked exactly once -- when that happens `await` is resumed with the result using `untry`
// either raise an exception or return the plain result.
pub fun setup/await : forall<a> (setup : (cb : (error<a>) -> io-noexn ()) -> io maybe<() -> io-noexn ()>) -> asyncx a
  = forall<a> fn<asyncx>(setup: (cb : (error<a>) -> io-noexn ()) -> io maybe<() -> io-noexn ()>){
    val i@11509 : hnd/ev-index
      = std/core/types/@make-ssize_t(0);
    val w : hnd/evv<<async,exn,ndet>>
      = std/core/hnd/evv-swap-create1(i@11509);
    val y : error<a>
      = std/async/async/await-exn(setup);
    val _ : ()
      = std/core/hnd/evv-set(w);
    val x@11506 : error<a>
      = (match ((std/core/hnd/yielding())) {
        ((std/core/types/True() : bool ) as @pat@1: bool)
           -> std/core/hnd/yield-cont((forall<b> fn<<async,exn,ndet>>(cont: (b) -> <async,exn,ndet> error<a>, res: b){
            std/core/hnd/open-at1(i@11509, cont, res);
          }));
        ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
           -> y;
      });
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-extend((fn<<async,exn,ndet>>(@y-x10849: error<a>){
          (std/async/async/setup/@mlift-await@11380(@y-x10849));
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> val i@0@11512 : (hnd/ev-index == 1 ssize_t)
              = std/core/types/@make-ssize_t(1);
            val w@0 : hnd/evv<<exn,async,ndet>>
              = std/core/hnd/evv-swap-create1(i@0@11512);
            val y@0 : a
              = (match (x@11506) {
                ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@2: string), (@pat@1@0: exception-info)) : exception ) as exn@0: exception)) : error<a> ) as @pat@3: (error<a>))
                   -> val ev@11515 : hnd/ev<exn>
                            = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
                  (match (ev@11515) {
                    ((@skip std/core/hnd/Ev<e,b>((@pat@0@3: hnd/htag<exn>), (m: hnd/marker<e,b>), (h: exn<e,b>), (@pat@1@1: hnd/evv<e>)) : hnd/ev<exn> ) as @pat@4: (hnd/ev<exn>))
                       -> (match ((std/core/exn/throw-exn/@select(h))) {
                        ((@skip std/core/hnd/Clause1((f@1: (hnd/marker<e,b>, hnd/ev<exn>, exception) -> e a)) : hnd/clause1<exception,a,exn,e,b> ) as @pat@2@0: (hnd/clause1<exception,a,exn,e,b>))
                           -> f@1(m, ev@11515, exn@0);
                      });
                  });
                ((@skip std/core/exn/Ok((x@3: a)) : error<a> ) as @pat@2@1: (error<a>))
                   -> x@3;
              });
            val _ : ()
              = std/core/hnd/evv-set(w@0);
        (match ((std/core/hnd/yielding())) {
          ((std/core/types/True() : bool ) as @pat@2: bool)
             -> std/core/hnd/yield-cont((forall<b> fn<<exn,async,ndet>>(cont@0: (b) -> <exn,async,ndet> a, res@0: b){
              std/core/hnd/open-at1(i@0@11512, cont@0, res@0);
            }));
          ((@skip std/core/types/False() : bool ) as @pat@0@1: bool)
             -> y@0;
        });
    });
  };
fun async-io-noexn : forall<a> (f : () -> io-noexn a) -> <async,ndet> a
  = forall<a> fn<<async,ndet>>(f: () -> io-noexn a){
    val ev@11518 : hnd/ev<async>
          = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
    (match (ev@11518) {
      ((@skip std/core/hnd/Ev<e,b>((@pat@0: hnd/htag<async>), (m: hnd/marker<e,b>), (h: async<e,b>), (@pat@1: hnd/evv<e>)) : hnd/ev<async> ) as @pat: (hnd/ev<async>))
         -> (match (h) {
          ((@skip std/async/async/@Hnd-async((@pat@0@0: int), (@ctl-async-iox: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e,b>), (@pat@1@0: hnd/clause1<scope,(),async,e,b>), (@pat@2@0: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>
   >)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e,b>), (@pat@3: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async
   ,e,b>))) : async<e,b> ) as @pat@2: (async<e,b>))
             -> (match (@ctl-async-iox) {
              ((@skip std/core/hnd/Clause1((f@0: (hnd/marker<e,b>, hnd/ev<async>, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) a) -> e a)) : hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) a,a,async,e,b> ) as @pat@2@1: (hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<
   global> == 1 <read<global>,write<global>,alloc<global>>)>)>) a,a,async,e,b>))
                 -> f@0(m, ev@11518, f);
            });
        });
    });
  };
// Returns immediately if the promise was already resolved and otherwise return `Nothing`.
pub fun try-await : forall<a> (p : promise<a>) -> <async,ndet> maybe<a>
  = forall<a> fn<<async,ndet>>(p: promise<a>){
    val ev@11521 : hnd/ev<async>
          = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
    (match (ev@11521) {
      ((@skip std/core/hnd/Ev<e,b>((@pat@0: hnd/htag<async>), (m: hnd/marker<e,b>), (h: async<e,b>), (@pat@1: hnd/evv<e>)) : hnd/ev<async> ) as @pat: (hnd/ev<async>))
         -> (match (h) {
          ((@skip std/async/async/@Hnd-async((@pat@0@0: int), (@ctl-async-iox: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e,b>), (@pat@1@0: hnd/clause1<scope,(),async,e,b>), (@pat@2@0: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>
   >)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e,b>), (@pat@3: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async
   ,e,b>))) : async<e,b> ) as @pat@2: (async<e,b>))
             -> (match (@ctl-async-iox) {
              ((@skip std/core/hnd/Clause1((f: (hnd/marker<e,b>, hnd/ev<async>, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<a>) -> e maybe<a>)) : hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<a>,maybe<a>,async,e,b> ) as @pat@2@1: (hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console
   /console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<a>,maybe<a>,async,e,b>))
                 -> f(m, ev@11521, (fn<(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>(){
                    (match ((std/core/types/ref/(!)((match (p) {
                        ((@skip std/async/async/Promise((@x: ref<global,promise-state<a>>)) : promise<a> ) as @pat@3@0: (promise<a>))
                           -> @x;
                      }), std/core/types/@Hdiv))) {
                      ((std/async/async/Resolved((value: a)) : promise-state<a> ) as @pat@0@0@0: (promise-state<a>))
                         -> std/core/types/Just(value);
                      (@pat@0@0@0@0: (promise-state<a>))
                         -> std/core/types/Nothing;
                    });
                  }));
            });
        });
    });
  };
// monadic lift
fun @mlift-async-io@11381 : forall<a> (@y-x10856 : error<a>) -> <async,ndet,exn> a
  = forall<a> fn<<async,ndet,exn>>(@y-x10856: error<a>){
    val i@11524 : hnd/ev-index
      = std/core/types/@make-ssize_t(1);
    val w : hnd/evv<<exn,async,ndet>>
      = std/core/hnd/evv-swap-create1(i@11524);
    val y : a
      = (match (@y-x10856) {
        ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@0: string), (@pat@1@0: exception-info)) : exception ) as exn@0: exception)) : error<a> ) as @pat@1: (error<a>))
           -> val ev@11527 : hnd/ev<exn>
                    = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
          (match (ev@11527) {
            ((@skip std/core/hnd/Ev<e,b>((@pat@0@1: hnd/htag<exn>), (m: hnd/marker<e,b>), (h: exn<e,b>), (@pat@1@1: hnd/evv<e>)) : hnd/ev<exn> ) as @pat@2: (hnd/ev<exn>))
               -> (match ((std/core/exn/throw-exn/@select(h))) {
                ((@skip std/core/hnd/Clause1((f@0: (hnd/marker<e,b>, hnd/ev<exn>, exception) -> e a)) : hnd/clause1<exception,a,exn,e,b> ) as @pat@2@0: (hnd/clause1<exception,a,exn,e,b>))
                   -> f@0(m, ev@11527, exn@0);
              });
          });
        ((@skip std/core/exn/Ok((x@1: a)) : error<a> ) as @pat@2@1: (error<a>))
           -> x@1;
      });
    val _ : ()
      = std/core/hnd/evv-set(w);
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-cont((forall<b> fn<<exn,async,ndet>>(cont: (b) -> <exn,async,ndet> a, res: b){
          std/core/hnd/open-at1(i@11524, cont, res);
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> y;
    });
  };
// Perform an I/O operation at the outer level; exceptions are propagated back.
fun async-io : forall<a> (f : () -> io a) -> asyncx a
  = forall<a> fn<asyncx>(f: () -> io a){
    val i@11533 : hnd/ev-index
      = std/core/types/@make-ssize_t(0);
    val w : hnd/evv<<async,ndet,exn>>
      = std/core/hnd/evv-swap-create1(i@11533);
    val ev@11536 : hnd/ev<async>
      = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
    val y : error<a>
      = (match (ev@11536) {
        ((@skip std/core/hnd/Ev<e,b>((@pat@0@1: hnd/htag<async>), (m: hnd/marker<e,b>), (h: async<e,b>), (@pat@1@0: hnd/evv<e>)) : hnd/ev<async> ) as @pat@2: (hnd/ev<async>))
           -> (match (h) {
            ((@skip std/async/async/@Hnd-async((@pat@0: int), (@ctl-async-iox: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e,b>), (@pat@1: hnd/clause1<scope,(),async,e,b>), (@pat@2@0: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)
   >)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e,b>), (@pat@3: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async
   ,e,b>))) : async<e,b> ) as @pat: (async<e,b>))
               -> (match (@ctl-async-iox) {
                ((@skip std/core/hnd/Clause1((f@1: (hnd/marker<e,b>, hnd/ev<async>, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) error<a>) -> e error<a>)) : hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) error<a>,error<a>,async,e,b> ) as @pat@2@0@0: (hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,
   console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) error<a>,error<a>,async,e,b>))
                   -> f@1(m, ev@11536, (fn<(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>(){
                      (std/core/exn/error/try(f));
                    }));
              });
          });
      });
    val _ : ()
      = std/core/hnd/evv-set(w);
    val x@11530 : error<a>
      = (match ((std/core/hnd/yielding())) {
        ((std/core/types/True() : bool ) as @pat@1@1: bool)
           -> std/core/hnd/yield-cont((forall<b> fn<<async,ndet,exn>>(cont: (b) -> <async,ndet,exn> error<a>, res: b){
            std/core/hnd/open-at1(i@11533, cont, res);
          }));
        ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
           -> y;
      });
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat@4: bool)
         -> std/core/hnd/yield-extend((fn<<async,ndet,exn>>(@y-x10856: error<a>){
          (std/async/async/@mlift-async-io@11381(@y-x10856));
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0@2: bool)
         -> val i@0@11539 : (hnd/ev-index == 1 ssize_t)
              = std/core/types/@make-ssize_t(1);
            val w@0 : hnd/evv<<exn,async,ndet>>
              = std/core/hnd/evv-swap-create1(i@0@11539);
            val y@0 : a
              = (match (x@11530) {
                ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@3: string), (@pat@1@1@0: exception-info)) : exception ) as exn@0: exception)) : error<a> ) as @pat@4@0: (error<a>))
                   -> val ev@0@11542 : hnd/ev<exn>
                            = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
                  (match (ev@0@11542) {
                    ((@skip std/core/hnd/Ev<e,b>((@pat@0@4: hnd/htag<exn>), (m@0: hnd/marker<e,b>), (h@0: exn<e,b>), (@pat@1@2: hnd/evv<e>)) : hnd/ev<exn> ) as @pat@5: (hnd/ev<exn>))
                       -> (match ((std/core/exn/throw-exn/@select(h@0))) {
                        ((@skip std/core/hnd/Clause1((f@3: (hnd/marker<e,b>, hnd/ev<exn>, exception) -> e a)) : hnd/clause1<exception,a,exn,e,b> ) as @pat@2@1: (hnd/clause1<exception,a,exn,e,b>))
                           -> f@3(m@0, ev@0@11542, exn@0);
                      });
                  });
                ((@skip std/core/exn/Ok((x@4: a)) : error<a> ) as @pat@2@2: (error<a>))
                   -> x@4;
              });
            val _ : ()
              = std/core/hnd/evv-set(w@0);
        (match ((std/core/hnd/yielding())) {
          ((std/core/types/True() : bool ) as @pat@3@0: bool)
             -> std/core/hnd/yield-cont((forall<b> fn<<exn,async,ndet>>(cont@0: (b) -> <exn,async,ndet> a, res@0: b){
              std/core/hnd/open-at1(i@0@11539, cont@0, res@0);
            }));
          ((@skip std/core/types/False() : bool ) as @pat@0@2@0: bool)
             -> y@0;
        });
    });
  };
fun nodispose : () -> <st<global>,console/console,div,fsys,ndet,net,ui> ()
  = fn<io-noexn>(){
    std/core/types/Unit;
  };
fun child-scope : (id : int, scope : scope) -> scope
  = fn(id: int, scope: scope){
    match (scope) {
      ((@skip std/async/async/Scope((cids: list<int>)) : scope ) as @pat: scope)
         -> val ys@10017 : list<int>
                  = std/core/types/Cons(id, std/core/types/Nil);
        std/async/async/Scope((match (cids) {
          ((std/core/types/Nil() : list<int> ) as @pat@0: (list<int>))
             -> ys@10017;
          (@pat@1: (list<int>))
             -> std/core/list/@unroll-append@10004(cids, ys@10017);
        }));
    };
  };
// lifted local: scope/(@lift-x@10731==), scope/(==), @spec-x10323
// specialized: std/core/list/(@unroll-x@10001==), on parameters @implicit/(@uniq-x@10308==), using:
// @implicit/(@uniq-x@10308==) = (std/core/int/(==),Own)
fun scope/(@lift-x@10732==) : (@uniq-xs@10306 : list<int>, @uniq-ys@10307 : list<int>) -> bool
  = fn(@uniq-xs@10306: list<int>, @uniq-ys@10307: list<int>){
    match (@uniq-xs@10306) {
      ((std/core/types/Cons((@uniq-x@10310: int), (@uniq-xx@10311: list<int>)) : list<int> ) as @uniq-pat@10309: (list<int>))
         -> (match (@uniq-ys@10307) {
          ((std/core/types/Nil() : list<int> ) as @uniq-pat@0@10312: (list<int>))
             -> std/core/types/False;
          ((@skip std/core/types/Cons((@uniq-y@10314: int), (@uniq-yy@10315: list<int>)) : list<int> ) as @uniq-pat@1@10313: (list<int>))
             -> (match ((std/core/int/(==)(@uniq-x@10310, @uniq-y@10314))) {
              ((std/core/types/True() : bool ) as @uniq-pat@2@10316: bool)
                 -> std/async/async/scope/(@lift-x@10732==)(@uniq-xx@10311, @uniq-yy@10315);
              (@uniq-pat@3@10317: bool)
                 -> std/core/types/False;
            });
        });
      ((@skip std/core/types/Nil() : list<int> ) as @uniq-pat@4@10318: (list<int>))
         -> (match (@uniq-ys@10307) {
          ((std/core/types/Nil() : list<int> ) as @uniq-pat@5@10319: (list<int>))
             -> std/core/types/True;
          ((@skip std/core/types/Cons((@uniq-pat@7@10321: int), (@uniq-pat@8@10322: list<int>)) : list<int> ) as @uniq-pat@6@10320: (list<int>))
             -> std/core/types/False;
        });
    };
  };
// lifted local: scope/(==), @spec-x10305
// specialized: std/core/list/(==), on parameters @implicit/(@uniq-x@10298==), using:
// @implicit/(@uniq-x@10298==) = (std/core/int/(==),Own)
fun scope/(@lift-x@10731==) : (@uniq-xs@10296 : list<int>, @uniq-ys@10297 : list<int>) -> bool
  = fn(@uniq-xs@10296: list<int>, @uniq-ys@10297: list<int>){
    match (@uniq-xs@10296) {
      ((std/core/types/Nil() : list<int> ) as @uniq-pat@4@10299: (list<int>))
         -> (match (@uniq-ys@10297) {
          ((std/core/types/Nil() : list<int> ) as @uniq-pat@5@10300: (list<int>))
             -> std/core/types/True;
          ((@skip std/core/types/Cons((@uniq-pat@7@10302: int), (@uniq-pat@8@10303: list<int>)) : list<int> ) as @uniq-pat@6@10301: (list<int>))
             -> std/core/types/False;
        });
      (@uniq-pat@10304: (list<int>))
         -> std/async/async/scope/(@lift-x@10732==)(@uniq-xs@10296, @uniq-ys@10297);
    };
  };
fun scope/(==) : (scope1 : scope, scope2 : scope) -> bool
  = fn(scope1: scope, scope2: scope){
    match (scope1) {
      ((@skip std/async/async/Scope((ids1: list<int>)) : scope ) as @pat: scope)
         -> (match (scope2) {
          ((@skip std/async/async/Scope((ids2: list<int>)) : scope ) as @pat@0: scope)
             -> std/async/async/scope/(@lift-x@10731==)(ids1, ids2);
        });
    };
  };
fun ids/@unroll-in-scope-of@10000 : (child : list<int>, parent : list<int>) -> bool
  = fn(child: list<int>, parent: list<int>){
    match (parent) {
      ((std/core/types/Nil() : list<int> ) as @pat: (list<int>))
         -> std/core/types/True;
      ((@skip std/core/types/Cons((p: int), (ps: list<int>)) : list<int> ) as @pat@0: (list<int>))
         -> (match (child) {
          ((std/core/types/Cons((c: int), (cs: list<int>)) : list<int> ) as @pat@1: (list<int>))
             -> (match ((std/core/int/(==)(c, p))) {
              ((std/core/types/True() : bool ) as @pat@2: bool)
                 -> std/async/async/ids/@unroll-in-scope-of@10000(cs, ps);
              (@pat@3: bool)
                 -> std/core/types/False;
            });
          ((@skip std/core/types/Nil() : list<int> ) as @pat@4: (list<int>))
             -> std/core/types/False;
        });
    };
  };
// unrolling of singleton matches of std/async/async/#ids/@unroll-in-scope-of@10000
fun ids/in-scope-of : (child : list<int>, parent : list<int>) -> bool
  = fn(child: list<int>, parent: list<int>){
    match (parent) {
      ((std/core/types/Nil() : list<int> ) as @pat: (list<int>))
         -> std/core/types/True;
      (@pat@0: (list<int>))
         -> std/async/async/ids/@unroll-in-scope-of@10000(child, parent);
    };
  };
fun in-scope-of : (child : scope, parent : scope) -> bool
  = fn(child: scope, parent: scope){
    match (parent) {
      ((@skip std/async/async/Scope((pids: list<int>)) : scope ) as @pat: scope)
         -> (match (child) {
          ((@skip std/async/async/Scope((cids: list<int>)) : scope ) as @pat@0: scope)
             -> (match (pids) {
              ((std/core/types/Nil() : list<int> ) as @pat@1: (list<int>))
                 -> std/core/types/True;
              (@pat@2: (list<int>))
                 -> std/async/async/ids/@unroll-in-scope-of@10000(cids, pids);
            });
        });
    };
  };
// lifted local: @lift-remove@10735, @uniq-b@10329, @lift-remove@10734, @lift-remove@10733, remove, @spec-x10371
// specialized: std/core/list/(@unroll-x@10001==), on parameters @implicit/(@uniq-x@10356==), using:
// @implicit/(@uniq-x@10356==) = (std/core/int/(==),Own)
fun @lift-remove@10736 : (@uniq-xs@10354 : list<int>, @uniq-ys@10355 : list<int>) -> bool
  = fn(@uniq-xs@10354: list<int>, @uniq-ys@10355: list<int>){
    match (@uniq-xs@10354) {
      ((std/core/types/Cons((@uniq-x@10358: int), (@uniq-xx@10359: list<int>)) : list<int> ) as @uniq-pat@10357: (list<int>))
         -> (match (@uniq-ys@10355) {
          ((std/core/types/Nil() : list<int> ) as @uniq-pat@0@10360: (list<int>))
             -> std/core/types/False;
          ((@skip std/core/types/Cons((@uniq-y@10362: int), (@uniq-yy@10363: list<int>)) : list<int> ) as @uniq-pat@1@10361: (list<int>))
             -> (match ((std/core/int/(==)(@uniq-x@10358, @uniq-y@10362))) {
              ((std/core/types/True() : bool ) as @uniq-pat@2@10364: bool)
                 -> std/async/async/@lift-remove@10736(@uniq-xx@10359, @uniq-yy@10363);
              (@uniq-pat@3@10365: bool)
                 -> std/core/types/False;
            });
        });
      ((@skip std/core/types/Nil() : list<int> ) as @uniq-pat@4@10366: (list<int>))
         -> (match (@uniq-ys@10355) {
          ((std/core/types/Nil() : list<int> ) as @uniq-pat@5@10367: (list<int>))
             -> std/core/types/True;
          ((@skip std/core/types/Cons((@uniq-pat@7@10369: int), (@uniq-pat@8@10370: list<int>)) : list<int> ) as @uniq-pat@6@10368: (list<int>))
             -> std/core/types/False;
        });
    };
  };
// lifted local: @uniq-b@10329, @lift-remove@10734, @lift-remove@10733, remove, @spec-x10353
// specialized: std/core/list/(==), on parameters @implicit/(@uniq-x@10346==), using:
// @implicit/(@uniq-x@10346==) = (std/core/int/(==),Own)
fun @lift-remove@10735 : (@uniq-xs@10344 : list<int>, @uniq-ys@10345 : list<int>) -> bool
  = fn(@uniq-xs@10344: list<int>, @uniq-ys@10345: list<int>){
    match (@uniq-xs@10344) {
      ((std/core/types/Nil() : list<int> ) as @uniq-pat@4@10347: (list<int>))
         -> (match (@uniq-ys@10345) {
          ((std/core/types/Nil() : list<int> ) as @uniq-pat@5@10348: (list<int>))
             -> std/core/types/True;
          ((@skip std/core/types/Cons((@uniq-pat@7@10350: int), (@uniq-pat@8@10351: list<int>)) : list<int> ) as @uniq-pat@6@10349: (list<int>))
             -> std/core/types/False;
        });
      (@uniq-pat@10352: (list<int>))
         -> std/async/async/@lift-remove@10736(@uniq-xs@10344, @uniq-ys@10345);
    };
  };
// lifted local: @lift-remove@10733, remove, @spec-x10342
// specialized: std/core/list/@unroll-filter@10007, on parameters @uniq-pred@10335, using:
// @uniq-pred@10335 = (fn(@uniq-x@10328: (std/async/async/scope, 2900)){
//   val @uniq-b@10329 : bool
//         = val x@10333 : (std/async/async/scope, a)
//                 = @uniq-x@10328;
//         match (x@10333) {
//           ((@skip std/core/types/Tuple2((@x: std/async/async/scope) : std/async/async/scope, (@pat@0@0: 2900) : a) : (std/async/async/scope, a) ) as @pat@1: (std/async/async/scope, 2900))
//              -> (match (@x) {
//               ((@skip std/async/async/Scope((ids1: (list :: V -> V)<int>) : (list :: V -> V)<int>) : std/async/async/scope ) as @pat: std/async/async/scope)
//                  -> (match (scope) {
//                   ((@skip std/async/async/Scope((ids2: (list :: V -> V)<int>) : (list :: V -> V)<int>) : std/async/async/scope ) as @pat@0: std/async/async/scope)
//                      -> std/core/list/(==)<int,(total :: E)>(ids1, ids2, std/core/int/(==));
//                 });
//             });
//         };
//   match (@uniq-b@10329) {
//     ((std/core/types/True() : bool ) as @uniq-pat@0@10330: bool)
//        -> std/core/types/False;
//     ((@skip std/core/types/False() : bool ) as @uniq-pat@0@0@10331: bool)
//        -> std/core/types/True;
//   };
// },Own)
fun @trmc-lift-remove@10734 : forall<a> (scope : scope, @uniq-xs@10334 : list<(scope, a)>, @acc : ctx<list<(scope, a)>>) -> list<(scope, a)>
  = forall<a> fn(scope: scope, @uniq-xs@10334: list<(scope, a)>, @acc: ctx<list<(scope, a)>>){
    (match (@uniq-xs@10334) {
      ((std/core/types/Cons((@uniq-x@10337: (scope, a)), (@uniq-xx@10338: list<(scope, a)>)) : list<(scope, a)> ) as @uniq-pat@10336: (list<(scope, a)>))
         -> val @uniq-b@10329 : bool
                  = (match (@uniq-x@10337) {
                    ((@skip std/core/types/Tuple2((@x: scope), (@pat@0@0: a)) : (scope, a) ) as @pat@1: (scope, a))
                       -> (match (@x) {
                        ((@skip std/async/async/Scope((ids1: list<int>)) : scope ) as @pat: scope)
                           -> (match (scope) {
                            ((@skip std/async/async/Scope((ids2: list<int>)) : scope ) as @pat@0: scope)
                               -> std/async/async/@lift-remove@10735(ids1, ids2);
                          });
                      });
                  });
        (match (@uniq-b@10329) {
          ((std/core/types/True() : bool ) as @uniq-pat@0@10330: bool)
             -> std/async/async/@trmc-lift-remove@10734(scope, @uniq-xx@10338, @acc);
          ((@skip std/core/types/False() : bool ) as @uniq-pat@0@0@10331: bool)
             -> val @trmc-x10802 : list<(scope, a)>
                  = std/core/types/@cctx-hole-create();
                val @trmc-x10803 : list<(scope, a)>
                  = std/core/types/Cons(@uniq-x@10337, @trmc-x10802);
            std/async/async/@trmc-lift-remove@10734(scope, @uniq-xx@10338, (std/core/types/@cctx-extend(@acc, @trmc-x10803, (std/core/types/@field-addr-of(@trmc-x10803, "(\x22std/core/types\x22,\x22\x22,\x22Cons\x22)", "(\x22\x22,\x22\x22,\x22tail\x22)")))));
        });
      ((@skip std/core/types/Nil() : list<(scope, a)> ) as @uniq-pat@2@10341: (list<(scope, a)>))
         -> std/core/types/cctx/((++.))(@acc, std/core/types/Nil);
    });
  };
// lifted local: @lift-remove@10733, remove, @spec-x10342
// specialized: std/core/list/@unroll-filter@10007, on parameters @uniq-pred@10335, using:
// @uniq-pred@10335 = (fn(@uniq-x@10328: (std/async/async/scope, 2900)){
//   val @uniq-b@10329 : bool
//         = val x@10333 : (std/async/async/scope, a)
//                 = @uniq-x@10328;
//         match (x@10333) {
//           ((@skip std/core/types/Tuple2((@x: std/async/async/scope) : std/async/async/scope, (@pat@0@0: 2900) : a) : (std/async/async/scope, a) ) as @pat@1: (std/async/async/scope, 2900))
//              -> (match (@x) {
//               ((@skip std/async/async/Scope((ids1: (list :: V -> V)<int>) : (list :: V -> V)<int>) : std/async/async/scope ) as @pat: std/async/async/scope)
//                  -> (match (scope) {
//                   ((@skip std/async/async/Scope((ids2: (list :: V -> V)<int>) : (list :: V -> V)<int>) : std/async/async/scope ) as @pat@0: std/async/async/scope)
//                      -> std/core/list/(==)<int,(total :: E)>(ids1, ids2, std/core/int/(==));
//                 });
//             });
//         };
//   match (@uniq-b@10329) {
//     ((std/core/types/True() : bool ) as @uniq-pat@0@10330: bool)
//        -> std/core/types/False;
//     ((@skip std/core/types/False() : bool ) as @uniq-pat@0@0@10331: bool)
//        -> std/core/types/True;
//   };
// },Own)
fun @lift-remove@10734 : forall<a> (scope : scope, @uniq-xs@10334 : list<(scope, a)>) -> list<(scope, a)>
  = forall<a> fn(scope@0: scope, @uniq-xs@10334@0: list<(scope, a)>){
    std/async/async/@trmc-lift-remove@10734(scope@0, @uniq-xs@10334@0, (std/core/types/cctx/empty()));
  };
// lifted local: remove, @spec-x10332
// specialized: std/core/list/remove, on parameters @uniq-pred@10325, using:
// @uniq-pred@10325 = (fn(x: (std/async/async/scope, 2900)){
//   match (x) {
//     ((@skip std/core/types/Tuple2((@x: std/async/async/scope) : std/async/async/scope, (@pat@0@0: 2900) : a) : (std/async/async/scope, a) ) as @pat@1: (std/async/async/scope, 2900))
//        -> (match (@x) {
//         ((@skip std/async/async/Scope((ids1: (list :: V -> V)<int>) : (list :: V -> V)<int>) : std/async/async/scope ) as @pat: std/async/async/scope)
//            -> (match (scope) {
//             ((@skip std/async/async/Scope((ids2: (list :: V -> V)<int>) : (list :: V -> V)<int>) : std/async/async/scope ) as @pat@0: std/async/async/scope)
//                -> std/core/list/(==)<int,(total :: E)>(ids1, ids2, std/core/int/(==));
//           });
//       });
//   };
// },Own)
fun @lift-remove@10733 : forall<a> (scope : scope, @uniq-xs@10324 : list<(scope, a)>) -> list<(scope, a)>
  = forall<a> fn(scope: scope, @uniq-xs@10324: list<(scope, a)>){
    (match (@uniq-xs@10324) {
      ((std/core/types/Nil() : list<(scope, a)> ) as @uniq-pat@2@10326: (list<(scope, a)>))
         -> std/core/types/Nil;
      (@uniq-pat@10327: (list<(scope, a)>))
         -> std/async/async/@trmc-lift-remove@10734(scope, @uniq-xs@10324, (std/core/types/cctx/empty()));
    });
  };
// Convenience functions for scope maps
fun remove : forall<a> (xs : list<(scope, a)>, scope : scope) -> list<(scope, a)>
  = forall<a> fn(xs: list<(scope, a)>, scope: scope){
    std/async/async/@lift-remove@10733(scope, xs);
  };
// lifted local: @lift-lookup@10739, @lift-lookup@10738, @lift-lookup@10737, lookup, @spec-x10426
// specialized: std/core/list/(@unroll-x@10001==), on parameters @implicit/(@uniq-x@10411==), using:
// @implicit/(@uniq-x@10411==) = (std/core/int/(==),Own)
fun @lift-lookup@10740 : (@uniq-xs@10409 : list<int>, @uniq-ys@10410 : list<int>) -> bool
  = fn(@uniq-xs@10409: list<int>, @uniq-ys@10410: list<int>){
    match (@uniq-xs@10409) {
      ((std/core/types/Cons((@uniq-x@10413: int), (@uniq-xx@10414: list<int>)) : list<int> ) as @uniq-pat@10412: (list<int>))
         -> (match (@uniq-ys@10410) {
          ((std/core/types/Nil() : list<int> ) as @uniq-pat@0@10415: (list<int>))
             -> std/core/types/False;
          ((@skip std/core/types/Cons((@uniq-y@10417: int), (@uniq-yy@10418: list<int>)) : list<int> ) as @uniq-pat@1@10416: (list<int>))
             -> (match ((std/core/int/(==)(@uniq-x@10413, @uniq-y@10417))) {
              ((std/core/types/True() : bool ) as @uniq-pat@2@10419: bool)
                 -> std/async/async/@lift-lookup@10740(@uniq-xx@10414, @uniq-yy@10418);
              (@uniq-pat@3@10420: bool)
                 -> std/core/types/False;
            });
        });
      ((@skip std/core/types/Nil() : list<int> ) as @uniq-pat@4@10421: (list<int>))
         -> (match (@uniq-ys@10410) {
          ((std/core/types/Nil() : list<int> ) as @uniq-pat@5@10422: (list<int>))
             -> std/core/types/True;
          ((@skip std/core/types/Cons((@uniq-pat@7@10424: int), (@uniq-pat@8@10425: list<int>)) : list<int> ) as @uniq-pat@6@10423: (list<int>))
             -> std/core/types/False;
        });
    };
  };
// lifted local: @lift-lookup@10738, @lift-lookup@10737, lookup, @spec-x10408
// specialized: std/core/list/(==), on parameters @implicit/(@uniq-x@10401==), using:
// @implicit/(@uniq-x@10401==) = (std/core/int/(==),Own)
fun @lift-lookup@10739 : (@uniq-xs@10399 : list<int>, @uniq-ys@10400 : list<int>) -> bool
  = fn(@uniq-xs@10399: list<int>, @uniq-ys@10400: list<int>){
    match (@uniq-xs@10399) {
      ((std/core/types/Nil() : list<int> ) as @uniq-pat@4@10402: (list<int>))
         -> (match (@uniq-ys@10400) {
          ((std/core/types/Nil() : list<int> ) as @uniq-pat@5@10403: (list<int>))
             -> std/core/types/True;
          ((@skip std/core/types/Cons((@uniq-pat@7@10405: int), (@uniq-pat@8@10406: list<int>)) : list<int> ) as @uniq-pat@6@10404: (list<int>))
             -> std/core/types/False;
        });
      (@uniq-pat@10407: (list<int>))
         -> std/async/async/@lift-lookup@10740(@uniq-xs@10399, @uniq-ys@10400);
    };
  };
// lifted local: @lift-lookup@10737, lookup, @spec-x10397
// specialized: std/core/list/@unroll-foreach-while@10009, on parameters @uniq-action@10390, using:
// @uniq-action@10390 = (fn(@uniq-kv@10376: (std/async/async/scope, 3030)){
//   match (val x@10388 : std/async/async/scope
//                = val @uniq-tuple2@10377 : (std/async/async/scope, a)
//                        = @uniq-kv@10376;
//                (match (@uniq-tuple2@10377) {
//                  ((@skip std/core/types/Tuple2((@uniq-x@10379: std/async/async/scope) : std/async/async/scope, (@uniq-pat@0@0@10380: 3030) : a) : (std/async/async/scope, a) ) as @uniq-pat@1@10378: (std/async/async/scope, 3030))
//                     -> @uniq-x@10379;
//                });
//   (match (x@10388) {
//     ((@skip std/async/async/Scope((ids1: (list :: V -> V)<int>) : (list :: V -> V)<int>) : std/async/async/scope ) as @pat: std/async/async/scope)
//        -> (match (scope) {
//         ((@skip std/async/async/Scope((ids2: (list :: V -> V)<int>) : (list :: V -> V)<int>) : std/async/async/scope ) as @pat@0: std/async/async/scope)
//            -> std/core/list/(==)<int,(total :: E)>(ids1, ids2, std/core/int/(==));
//       });
//   })) {
//     ((std/core/types/True() : bool ) as @uniq-pat@2@10381: bool)
//        -> std/core/types/Just<a>(val @uniq-tuple2@0@10382 : (std/async/async/scope, a)
//                                        = @uniq-kv@10376;
//       (match (@uniq-tuple2@0@10382) {
//         ((@skip std/core/types/Tuple2((@uniq-pat@0@1@10384: std/async/async/scope) : std/async/async/scope, (@uniq-x@0@10385: 3030) : a) : (std/async/async/scope, a) ) as @uniq-pat@3@10383: (std/async/async/scope, 3030))
//            -> @uniq-x@0@10385;
//       }));
//     ((@skip std/core/types/False() : bool ) as @uniq-pat@0@2@10386: bool)
//        -> std/core/types/Nothing<a>;
//   };
// },Own)
fun @lift-lookup@10738 : forall<a> (scope : scope, @uniq-xs@10389 : list<(scope, a)>) -> maybe<a>
  = forall<a> fn(scope: scope, @uniq-xs@10389: list<(scope, a)>){
    (match (@uniq-xs@10389) {
      ((std/core/types/Nil() : list<(scope, a)> ) as @uniq-pat@10391: (list<(scope, a)>))
         -> std/core/types/Nothing;
      ((@skip std/core/types/Cons((@uniq-x@10393: (scope, a)), (@uniq-xx@10394: list<(scope, a)>)) : list<(scope, a)> ) as @uniq-pat@0@10392: (list<(scope, a)>))
         -> (match (@uniq-x@10393) {
          ((@skip std/core/types/Tuple2((@uniq-x@10379: scope), (@uniq-pat@0@0@10380: a)) : (scope, a) ) as @uniq-pat@1@10378: (scope, a))
             -> (match (@uniq-x@10379) {
              ((@skip std/async/async/Scope((ids1: list<int>)) : scope ) as @pat: scope)
                 -> (match (scope) {
                  ((@skip std/async/async/Scope((ids2: list<int>)) : scope ) as @pat@0: scope)
                     -> (match ((std/async/async/@lift-lookup@10739(ids1, ids2))) {
                      ((std/core/types/True() : bool ) as @uniq-pat@2@10381: bool)
                         -> std/core/types/Just((match (@uniq-x@10393) {
                          ((@skip std/core/types/Tuple2((@uniq-pat@0@1@10384: scope), (@uniq-x@0@10385: a)) : (scope, a) ) as @uniq-pat@3@10383: (scope, a))
                             -> @uniq-x@0@10385;
                        }));
                      ((@skip std/core/types/False() : bool ) as @uniq-pat@0@2@10386: bool)
                         -> (match (std/core/types/Nothing) {
                          ((std/core/types/Nothing() : maybe<a> ) as @uniq-pat@1@10395: (maybe<a>))
                             -> std/async/async/@lift-lookup@10738(scope, @uniq-xx@10394);
                          (@uniq-just@10396: (maybe<a>))
                             -> @uniq-just@10396;
                        });
                    });
                });
            });
        });
    });
  };
// lifted local: lookup, @spec-x10387
// specialized: std/core/list/lookup, on parameters @uniq-pred@10373, using:
// @uniq-pred@10373 = (fn(x: std/async/async/scope){
//   match (x) {
//     ((@skip std/async/async/Scope((ids1: (list :: V -> V)<int>) : (list :: V -> V)<int>) : std/async/async/scope ) as @pat: std/async/async/scope)
//        -> (match (scope) {
//         ((@skip std/async/async/Scope((ids2: (list :: V -> V)<int>) : (list :: V -> V)<int>) : std/async/async/scope ) as @pat@0: std/async/async/scope)
//            -> std/core/list/(==)<int,(total :: E)>(ids1, ids2, std/core/int/(==));
//       });
//   };
// },Own)
fun @lift-lookup@10737 : forall<a> (scope : scope, @uniq-xs@10372 : list<(scope, a)>) -> maybe<a>
  = forall<a> fn(scope: scope, @uniq-xs@10372: list<(scope, a)>){
    (match (@uniq-xs@10372) {
      ((std/core/types/Nil() : list<(scope, a)> ) as @uniq-pat@10374: (list<(scope, a)>))
         -> std/core/types/Nothing;
      (@uniq-pat@0@10375: (list<(scope, a)>))
         -> std/async/async/@lift-lookup@10738(scope, @uniq-xs@10372);
    });
  };
fun lookup : forall<a> (xs : list<(scope, a)>, scope : scope) -> maybe<a>
  = forall<a> fn(xs: list<(scope, a)>, scope: scope){
    std/async/async/@lift-lookup@10737(scope, xs);
  };
// lifted local: @lift-contains@10743, @lift-contains@10742, @lift-contains@10741, contains, @spec-x10481
// specialized: std/core/list/(@unroll-x@10001==), on parameters @implicit/(@uniq-x@10466==), using:
// @implicit/(@uniq-x@10466==) = (std/core/int/(==),Own)
fun @lift-contains@10744 : (@uniq-xs@10464 : list<int>, @uniq-ys@10465 : list<int>) -> bool
  = fn(@uniq-xs@10464: list<int>, @uniq-ys@10465: list<int>){
    match (@uniq-xs@10464) {
      ((std/core/types/Cons((@uniq-x@10468: int), (@uniq-xx@10469: list<int>)) : list<int> ) as @uniq-pat@10467: (list<int>))
         -> (match (@uniq-ys@10465) {
          ((std/core/types/Nil() : list<int> ) as @uniq-pat@0@10470: (list<int>))
             -> std/core/types/False;
          ((@skip std/core/types/Cons((@uniq-y@10472: int), (@uniq-yy@10473: list<int>)) : list<int> ) as @uniq-pat@1@10471: (list<int>))
             -> (match ((std/core/int/(==)(@uniq-x@10468, @uniq-y@10472))) {
              ((std/core/types/True() : bool ) as @uniq-pat@2@10474: bool)
                 -> std/async/async/@lift-contains@10744(@uniq-xx@10469, @uniq-yy@10473);
              (@uniq-pat@3@10475: bool)
                 -> std/core/types/False;
            });
        });
      ((@skip std/core/types/Nil() : list<int> ) as @uniq-pat@4@10476: (list<int>))
         -> (match (@uniq-ys@10465) {
          ((std/core/types/Nil() : list<int> ) as @uniq-pat@5@10477: (list<int>))
             -> std/core/types/True;
          ((@skip std/core/types/Cons((@uniq-pat@7@10479: int), (@uniq-pat@8@10480: list<int>)) : list<int> ) as @uniq-pat@6@10478: (list<int>))
             -> std/core/types/False;
        });
    };
  };
// lifted local: @lift-contains@10742, @lift-contains@10741, contains, @spec-x10463
// specialized: std/core/list/(==), on parameters @implicit/(@uniq-x@10456==), using:
// @implicit/(@uniq-x@10456==) = (std/core/int/(==),Own)
fun @lift-contains@10743 : (@uniq-xs@10454 : list<int>, @uniq-ys@10455 : list<int>) -> bool
  = fn(@uniq-xs@10454: list<int>, @uniq-ys@10455: list<int>){
    match (@uniq-xs@10454) {
      ((std/core/types/Nil() : list<int> ) as @uniq-pat@4@10457: (list<int>))
         -> (match (@uniq-ys@10455) {
          ((std/core/types/Nil() : list<int> ) as @uniq-pat@5@10458: (list<int>))
             -> std/core/types/True;
          ((@skip std/core/types/Cons((@uniq-pat@7@10460: int), (@uniq-pat@8@10461: list<int>)) : list<int> ) as @uniq-pat@6@10459: (list<int>))
             -> std/core/types/False;
        });
      (@uniq-pat@10462: (list<int>))
         -> std/async/async/@lift-contains@10744(@uniq-xs@10454, @uniq-ys@10455);
    };
  };
// lifted local: @lift-contains@10741, contains, @spec-x10452
// specialized: std/core/list/@unroll-foreach-while@10009, on parameters @uniq-action@10445, using:
// @uniq-action@10445 = (fn(@uniq-kv@10431: (std/async/async/scope, 3079)){
//   match (val x@10443 : std/async/async/scope
//                = val @uniq-tuple2@10432 : (std/async/async/scope, a)
//                        = @uniq-kv@10431;
//                (match (@uniq-tuple2@10432) {
//                  ((@skip std/core/types/Tuple2((@uniq-x@10434: std/async/async/scope) : std/async/async/scope, (@uniq-pat@0@0@10435: 3079) : a) : (std/async/async/scope, a) ) as @uniq-pat@1@10433: (std/async/async/scope, 3079))
//                     -> @uniq-x@10434;
//                });
//   (match (x@10443) {
//     ((@skip std/async/async/Scope((ids1: (list :: V -> V)<int>) : (list :: V -> V)<int>) : std/async/async/scope ) as @pat@2: std/async/async/scope)
//        -> (match (scope) {
//         ((@skip std/async/async/Scope((ids2: (list :: V -> V)<int>) : (list :: V -> V)<int>) : std/async/async/scope ) as @pat@0@0: std/async/async/scope)
//            -> std/core/list/(==)<int,(total :: E)>(ids1, ids2, std/core/int/(==));
//       });
//   })) {
//     ((std/core/types/True() : bool ) as @uniq-pat@2@10436: bool)
//        -> std/core/types/Just<a>(val @uniq-tuple2@0@10437 : (std/async/async/scope, a)
//                                        = @uniq-kv@10431;
//       (match (@uniq-tuple2@0@10437) {
//         ((@skip std/core/types/Tuple2((@uniq-pat@0@1@10439: std/async/async/scope) : std/async/async/scope, (@uniq-x@0@10440: 3079) : a) : (std/async/async/scope, a) ) as @uniq-pat@3@10438: (std/async/async/scope, 3079))
//            -> @uniq-x@0@10440;
//       }));
//     ((@skip std/core/types/False() : bool ) as @uniq-pat@0@2@10441: bool)
//        -> std/core/types/Nothing<a>;
//   };
// },Own)
fun @lift-contains@10742 : forall<a> (scope : scope, @uniq-xs@10444 : list<(scope, a)>) -> maybe<a>
  = forall<a> fn(scope: scope, @uniq-xs@10444: list<(scope, a)>){
    (match (@uniq-xs@10444) {
      ((std/core/types/Nil() : list<(scope, a)> ) as @uniq-pat@10446: (list<(scope, a)>))
         -> std/core/types/Nothing;
      ((@skip std/core/types/Cons((@uniq-x@10448: (scope, a)), (@uniq-xx@10449: list<(scope, a)>)) : list<(scope, a)> ) as @uniq-pat@0@10447: (list<(scope, a)>))
         -> (match (@uniq-x@10448) {
          ((@skip std/core/types/Tuple2((@uniq-x@10434: scope), (@uniq-pat@0@0@10435: a)) : (scope, a) ) as @uniq-pat@1@10433: (scope, a))
             -> (match (@uniq-x@10434) {
              ((@skip std/async/async/Scope((ids1: list<int>)) : scope ) as @pat@2: scope)
                 -> (match (scope) {
                  ((@skip std/async/async/Scope((ids2: list<int>)) : scope ) as @pat@0@0: scope)
                     -> (match ((std/async/async/@lift-contains@10743(ids1, ids2))) {
                      ((std/core/types/True() : bool ) as @uniq-pat@2@10436: bool)
                         -> std/core/types/Just((match (@uniq-x@10448) {
                          ((@skip std/core/types/Tuple2((@uniq-pat@0@1@10439: scope), (@uniq-x@0@10440: a)) : (scope, a) ) as @uniq-pat@3@10438: (scope, a))
                             -> @uniq-x@0@10440;
                        }));
                      ((@skip std/core/types/False() : bool ) as @uniq-pat@0@2@10441: bool)
                         -> (match (std/core/types/Nothing) {
                          ((std/core/types/Nothing() : maybe<a> ) as @uniq-pat@1@10450: (maybe<a>))
                             -> std/async/async/@lift-contains@10742(scope, @uniq-xx@10449);
                          (@uniq-just@10451: (maybe<a>))
                             -> @uniq-just@10451;
                        });
                    });
                });
            });
        });
    });
  };
// lifted local: contains, @spec-x10442
// specialized: std/core/list/lookup, on parameters @uniq-pred@10428, using:
// @uniq-pred@10428 = (fn(x: std/async/async/scope){
//   match (x) {
//     ((@skip std/async/async/Scope((ids1: (list :: V -> V)<int>) : (list :: V -> V)<int>) : std/async/async/scope ) as @pat@2: std/async/async/scope)
//        -> (match (scope) {
//         ((@skip std/async/async/Scope((ids2: (list :: V -> V)<int>) : (list :: V -> V)<int>) : std/async/async/scope ) as @pat@0@0: std/async/async/scope)
//            -> std/core/list/(==)<int,(total :: E)>(ids1, ids2, std/core/int/(==));
//       });
//   };
// },Own)
fun @lift-contains@10741 : forall<a> (scope : scope, @uniq-xs@10427 : list<(scope, a)>) -> maybe<a>
  = forall<a> fn(scope: scope, @uniq-xs@10427: list<(scope, a)>){
    (match (@uniq-xs@10427) {
      ((std/core/types/Nil() : list<(scope, a)> ) as @uniq-pat@10429: (list<(scope, a)>))
         -> std/core/types/Nothing;
      (@uniq-pat@0@10430: (list<(scope, a)>))
         -> std/async/async/@lift-contains@10742(scope, @uniq-xs@10427);
    });
  };
fun contains : forall<a> (xs : list<(scope, a)>, scope : scope) -> bool
  = forall<a> fn(xs: list<(scope, a)>, scope: scope){
    val mb@10025 : maybe<a>
          = std/async/async/@lift-contains@10741(scope, xs);
    (match (mb@10025) {
      ((std/core/types/Just((@pat@0: a)) : maybe<a> ) as @pat: (maybe<a>))
         -> std/core/types/True;
      ((@skip std/core/types/Nothing() : maybe<a> ) as @pat@1: (maybe<a>))
         -> std/core/types/False;
    });
  };
// lifted local: async/@lift-handle@10747, async/@lift-handle@10746, async/@lift-handle@10745, cb, handle-await, async/handle, @spec-x10536
// specialized: std/core/list/(@unroll-x@10001==), on parameters @implicit/(@uniq-x@10521==), using:
// @implicit/(@uniq-x@10521==) = (std/core/int/(==),Own)
fun async/@lift-handle@10748 : (@uniq-xs@10519 : list<int>, @uniq-ys@10520 : list<int>) -> bool
  = fn(@uniq-xs@10519: list<int>, @uniq-ys@10520: list<int>){
    match (@uniq-xs@10519) {
      ((std/core/types/Cons((@uniq-x@10523: int), (@uniq-xx@10524: list<int>)) : list<int> ) as @uniq-pat@10522: (list<int>))
         -> (match (@uniq-ys@10520) {
          ((std/core/types/Nil() : list<int> ) as @uniq-pat@0@10525: (list<int>))
             -> std/core/types/False;
          ((@skip std/core/types/Cons((@uniq-y@10527: int), (@uniq-yy@10528: list<int>)) : list<int> ) as @uniq-pat@1@10526: (list<int>))
             -> (match ((std/core/int/(==)(@uniq-x@10523, @uniq-y@10527))) {
              ((std/core/types/True() : bool ) as @uniq-pat@2@10529: bool)
                 -> std/async/async/async/@lift-handle@10748(@uniq-xx@10524, @uniq-yy@10528);
              (@uniq-pat@3@10530: bool)
                 -> std/core/types/False;
            });
        });
      ((@skip std/core/types/Nil() : list<int> ) as @uniq-pat@4@10531: (list<int>))
         -> (match (@uniq-ys@10520) {
          ((std/core/types/Nil() : list<int> ) as @uniq-pat@5@10532: (list<int>))
             -> std/core/types/True;
          ((@skip std/core/types/Cons((@uniq-pat@7@10534: int), (@uniq-pat@8@10535: list<int>)) : list<int> ) as @uniq-pat@6@10533: (list<int>))
             -> std/core/types/False;
        });
    };
  };
// lifted local: async/@lift-handle@10746, async/@lift-handle@10745, cb, handle-await, async/handle, @spec-x10518
// specialized: std/core/list/(==), on parameters @implicit/(@uniq-x@10511==), using:
// @implicit/(@uniq-x@10511==) = (std/core/int/(==),Own)
fun async/@lift-handle@10747 : (@uniq-xs@10509 : list<int>, @uniq-ys@10510 : list<int>) -> bool
  = fn(@uniq-xs@10509: list<int>, @uniq-ys@10510: list<int>){
    match (@uniq-xs@10509) {
      ((std/core/types/Nil() : list<int> ) as @uniq-pat@4@10512: (list<int>))
         -> (match (@uniq-ys@10510) {
          ((std/core/types/Nil() : list<int> ) as @uniq-pat@5@10513: (list<int>))
             -> std/core/types/True;
          ((@skip std/core/types/Cons((@uniq-pat@7@10515: int), (@uniq-pat@8@10516: list<int>)) : list<int> ) as @uniq-pat@6@10514: (list<int>))
             -> std/core/types/False;
        });
      (@uniq-pat@10517: (list<int>))
         -> std/async/async/async/@lift-handle@10748(@uniq-xs@10509, @uniq-ys@10510);
    };
  };
// lifted local: async/@lift-handle@10745, cb, handle-await, async/handle, @spec-x10507
// specialized: std/core/list/@unroll-foreach-while@10009, on parameters @uniq-action@10500, using:
// @uniq-action@10500 = (fn(@uniq-kv@10486: (std/async/async/scope, () -> (io-noexn :: E) ())){
//   match (val x@0@10498 : std/async/async/scope
//                = val @uniq-tuple2@10487 : (std/async/async/scope, () -> (io-noexn :: E) ())
//                        = @uniq-kv@10486;
//                (match (@uniq-tuple2@10487) {
//                  ((@skip std/core/types/Tuple2((@uniq-x@10489: std/async/async/scope) : std/async/async/scope, (@uniq-pat@0@0@10490: () -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()) : () -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()) : (std/async/async/scope, () -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()) ) as @uniq-pat@1@10488: (std/async/async/scope, () -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()))
//                     -> @uniq-x@10489;
//                });
//   (match (x@0@10498) {
//     ((@skip std/async/async/Scope((ids1: (list :: V -> V)<int>) : (list :: V -> V)<int>) : std/async/async/scope ) as @pat@3: std/async/async/scope)
//        -> (match (cscope) {
//         ((@skip std/async/async/Scope((ids2: (list :: V -> V)<int>) : (list :: V -> V)<int>) : std/async/async/scope ) as @pat@0@1: std/async/async/scope)
//            -> std/core/list/(==)<int,(total :: E)>(ids1, ids2, std/core/int/(==));
//       });
//   })) {
//     ((std/core/types/True() : bool ) as @uniq-pat@2@10491: bool)
//        -> std/core/types/Just<() -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()>(val @uniq-tuple2@0@10492 : (std/async/async/scope, () -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ())
//                                                                                                                                                                                                                                                                                                                         = @uniq-kv@10486;
//       (match (@uniq-tuple2@0@10492) {
//         ((@skip std/core/types/Tuple2((@uniq-pat@0@1@10494: std/async/async/scope) : std/async/async/scope, (@uniq-x@0@10495: () -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()) : () -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()) : (std/async/async/scope, () -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()) ) as @uniq-pat@3@10493: (std/async/async/scope, () -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()))
//            -> @uniq-x@0@10495;
//       }));
//     ((@skip std/core/types/False() : bool ) as @uniq-pat@0@2@10496: bool)
//        -> std/core/types/Nothing<() -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()>;
//   };
// },Own)
fun async/@lift-handle@10746 : (cscope : scope, @uniq-xs@10499 : list<(scope, () -> io-noexn ())>) -> maybe<() -> io-noexn ()>
  = fn(cscope: scope, @uniq-xs@10499: list<(scope, () -> io-noexn ())>){
    match (@uniq-xs@10499) {
      ((std/core/types/Nil() : list<(scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())> ) as @uniq-pat@10501: (list<(scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())>))
         -> std/core/types/Nothing;
      ((@skip std/core/types/Cons((@uniq-x@10503: (scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())), (@uniq-xx@10504: list<(scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())>)) : list<(scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<
   global>,alloc<global>>)>)>) ())> ) as @uniq-pat@0@10502: (list<(scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())>))
         -> (match (@uniq-x@10503) {
          ((@skip std/core/types/Tuple2((@uniq-x@10489: scope), (@uniq-pat@0@0@10490: () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())) : (scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) ) as @uniq-pat@1@10488: (scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <
   read<global>,write<global>,alloc<global>>)>)>) ()))
             -> (match (@uniq-x@10489) {
              ((@skip std/async/async/Scope((ids1: list<int>)) : scope ) as @pat@3: scope)
                 -> (match (cscope) {
                  ((@skip std/async/async/Scope((ids2: list<int>)) : scope ) as @pat@0@1: scope)
                     -> (match ((std/async/async/async/@lift-handle@10747(ids1, ids2))) {
                      ((std/core/types/True() : bool ) as @uniq-pat@2@10491: bool)
                         -> std/core/types/Just((match (@uniq-x@10503) {
                          ((@skip std/core/types/Tuple2((@uniq-pat@0@1@10494: scope), (@uniq-x@0@10495: () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())) : (scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) ) as @uniq-pat@3@10493: (scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(
   st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()))
                             -> @uniq-x@0@10495;
                        }));
                      ((@skip std/core/types/False() : bool ) as @uniq-pat@0@2@10496: bool)
                         -> (match (std/core/types/Nothing) {
                          ((std/core/types/Nothing() : maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()> ) as @uniq-pat@1@10505: (maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>))
                             -> std/async/async/async/@lift-handle@10746(cscope, @uniq-xx@10504);
                          (@uniq-just@10506: (maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>))
                             -> @uniq-just@10506;
                        });
                    });
                });
            });
        });
    };
  };
// lifted local: cb, handle-await, async/handle, @spec-x10497
// specialized: std/core/list/lookup, on parameters @uniq-pred@10483, using:
// @uniq-pred@10483 = (fn(x@0: std/async/async/scope){
//   match (x@0) {
//     ((@skip std/async/async/Scope((ids1: (list :: V -> V)<int>) : (list :: V -> V)<int>) : std/async/async/scope ) as @pat@3: std/async/async/scope)
//        -> (match (cscope) {
//         ((@skip std/async/async/Scope((ids2: (list :: V -> V)<int>) : (list :: V -> V)<int>) : std/async/async/scope ) as @pat@0@1: std/async/async/scope)
//            -> std/core/list/(==)<int,(total :: E)>(ids1, ids2, std/core/int/(==));
//       });
//   };
// },Own)
fun async/@lift-handle@10745 : (cscope : scope, @uniq-xs@10482 : list<(scope, () -> io-noexn ())>) -> maybe<() -> io-noexn ()>
  = fn(cscope: scope, @uniq-xs@10482: list<(scope, () -> io-noexn ())>){
    match (@uniq-xs@10482) {
      ((std/core/types/Nil() : list<(scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())> ) as @uniq-pat@10484: (list<(scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())>))
         -> std/core/types/Nothing;
      (@uniq-pat@0@10485: (list<(scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())>))
         -> std/async/async/async/@lift-handle@10746(cscope, @uniq-xs@10482);
    };
  };
// lifted local: async/@lift-handle@10751, @uniq-b@10542, async/@lift-handle@10750, async/@lift-handle@10749, _@0, cb, handle-await, async/handle, @spec-x10584
// specialized: std/core/list/(@unroll-x@10001==), on parameters @implicit/(@uniq-x@10569==), using:
// @implicit/(@uniq-x@10569==) = (std/core/int/(==),Own)
fun async/@lift-handle@10752 : (@uniq-xs@10567 : list<int>, @uniq-ys@10568 : list<int>) -> bool
  = fn(@uniq-xs@10567: list<int>, @uniq-ys@10568: list<int>){
    match (@uniq-xs@10567) {
      ((std/core/types/Cons((@uniq-x@10571: int), (@uniq-xx@10572: list<int>)) : list<int> ) as @uniq-pat@10570: (list<int>))
         -> (match (@uniq-ys@10568) {
          ((std/core/types/Nil() : list<int> ) as @uniq-pat@0@10573: (list<int>))
             -> std/core/types/False;
          ((@skip std/core/types/Cons((@uniq-y@10575: int), (@uniq-yy@10576: list<int>)) : list<int> ) as @uniq-pat@1@10574: (list<int>))
             -> (match ((std/core/int/(==)(@uniq-x@10571, @uniq-y@10575))) {
              ((std/core/types/True() : bool ) as @uniq-pat@2@10577: bool)
                 -> std/async/async/async/@lift-handle@10752(@uniq-xx@10572, @uniq-yy@10576);
              (@uniq-pat@3@10578: bool)
                 -> std/core/types/False;
            });
        });
      ((@skip std/core/types/Nil() : list<int> ) as @uniq-pat@4@10579: (list<int>))
         -> (match (@uniq-ys@10568) {
          ((std/core/types/Nil() : list<int> ) as @uniq-pat@5@10580: (list<int>))
             -> std/core/types/True;
          ((@skip std/core/types/Cons((@uniq-pat@7@10582: int), (@uniq-pat@8@10583: list<int>)) : list<int> ) as @uniq-pat@6@10581: (list<int>))
             -> std/core/types/False;
        });
    };
  };
// lifted local: @uniq-b@10542, async/@lift-handle@10750, async/@lift-handle@10749, _@0, cb, handle-await, async/handle, @spec-x10566
// specialized: std/core/list/(==), on parameters @implicit/(@uniq-x@10559==), using:
// @implicit/(@uniq-x@10559==) = (std/core/int/(==),Own)
fun async/@lift-handle@10751 : (@uniq-xs@10557 : list<int>, @uniq-ys@10558 : list<int>) -> bool
  = fn(@uniq-xs@10557: list<int>, @uniq-ys@10558: list<int>){
    match (@uniq-xs@10557) {
      ((std/core/types/Nil() : list<int> ) as @uniq-pat@4@10560: (list<int>))
         -> (match (@uniq-ys@10558) {
          ((std/core/types/Nil() : list<int> ) as @uniq-pat@5@10561: (list<int>))
             -> std/core/types/True;
          ((@skip std/core/types/Cons((@uniq-pat@7@10563: int), (@uniq-pat@8@10564: list<int>)) : list<int> ) as @uniq-pat@6@10562: (list<int>))
             -> std/core/types/False;
        });
      (@uniq-pat@10565: (list<int>))
         -> std/async/async/async/@lift-handle@10752(@uniq-xs@10557, @uniq-ys@10558);
    };
  };
// lifted local: async/@lift-handle@10749, _@0, cb, handle-await, async/handle, @spec-x10555
// specialized: std/core/list/@unroll-filter@10007, on parameters @uniq-pred@10548, using:
// @uniq-pred@10548 = (fn(@uniq-x@10541: (std/async/async/scope, () -> (io-noexn :: E) ())){
//   val @uniq-b@10542 : bool
//         = val x@1@10546 : (std/async/async/scope, () -> (io-noexn :: E) ())
//                 = @uniq-x@10541;
//         match (x@1@10546) {
//           ((@skip std/core/types/Tuple2((@x: std/async/async/scope) : std/async/async/scope, (@pat@0@4: () -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()) : () -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()) : (std/async/async/scope, () -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()) ) as @pat@6: (std/async/async/scope, () -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()))
//              -> (match (@x) {
//               ((@skip std/async/async/Scope((ids1@0: (list :: V -> V)<int>) : (list :: V -> V)<int>) : std/async/async/scope ) as @pat@5: std/async/async/scope)
//                  -> (match (cscope) {
//                   ((@skip std/async/async/Scope((ids2@0: (list :: V -> V)<int>) : (list :: V -> V)<int>) : std/async/async/scope ) as @pat@0@3: std/async/async/scope)
//                      -> std/core/list/(==)<int,(total :: E)>(ids1@0, ids2@0, std/core/int/(==));
//                 });
//             });
//         };
//   match (@uniq-b@10542) {
//     ((std/core/types/True() : bool ) as @uniq-pat@0@10543: bool)
//        -> std/core/types/False;
//     ((@skip std/core/types/False() : bool ) as @uniq-pat@0@0@10544: bool)
//        -> std/core/types/True;
//   };
// },Own)
fun async/@trmc-lift-handle@10750 : (cscope : scope, @uniq-xs@10547 : list<(scope, () -> io-noexn ())>, @acc : ctx<list<(scope, () -> io-noexn ())>>) -> list<(scope, () -> io-noexn ())>
  = fn(cscope: scope, @uniq-xs@10547: list<(scope, () -> io-noexn ())>, @acc: ctx<list<(scope, () -> io-noexn ())>>){
    match (@uniq-xs@10547) {
      ((std/core/types/Cons((@uniq-x@10550: (scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())), (@uniq-xx@10551: list<(scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())>)) : list<(scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,
   alloc<global>>)>)>) ())> ) as @uniq-pat@10549: (list<(scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())>))
         -> val @uniq-b@10542 : bool
                  = (match (@uniq-x@10550) {
                    ((@skip std/core/types/Tuple2((@x: scope), (@pat@0@4: () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())) : (scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) ) as @pat@6: (scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<
   global>,alloc<global>>)>)>) ()))
                       -> (match (@x) {
                        ((@skip std/async/async/Scope((ids1@0: list<int>)) : scope ) as @pat@5: scope)
                           -> (match (cscope) {
                            ((@skip std/async/async/Scope((ids2@0: list<int>)) : scope ) as @pat@0@3: scope)
                               -> std/async/async/async/@lift-handle@10751(ids1@0, ids2@0);
                          });
                      });
                  });
        (match (@uniq-b@10542) {
          ((std/core/types/True() : bool ) as @uniq-pat@0@10543: bool)
             -> std/async/async/async/@trmc-lift-handle@10750(cscope, @uniq-xx@10551, @acc);
          ((@skip std/core/types/False() : bool ) as @uniq-pat@0@0@10544: bool)
             -> val @trmc-x10804 : list<(scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())>
                  = std/core/types/@cctx-hole-create();
                val @trmc-x10805 : list<(scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())>
                  = std/core/types/Cons(@uniq-x@10550, @trmc-x10804);
            std/async/async/async/@trmc-lift-handle@10750(cscope, @uniq-xx@10551, (std/core/types/@cctx-extend(@acc, @trmc-x10805, (std/core/types/@field-addr-of(@trmc-x10805, "(\x22std/core/types\x22,\x22\x22,\x22Cons\x22)", "(\x22\x22,\x22\x22,\x22tail\x22)")))));
        });
      ((@skip std/core/types/Nil() : list<(scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())> ) as @uniq-pat@2@10554: (list<(scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())>))
         -> std/core/types/cctx/((++.))(@acc, std/core/types/Nil);
    };
  };
// lifted local: async/@lift-handle@10749, _@0, cb, handle-await, async/handle, @spec-x10555
// specialized: std/core/list/@unroll-filter@10007, on parameters @uniq-pred@10548, using:
// @uniq-pred@10548 = (fn(@uniq-x@10541: (std/async/async/scope, () -> (io-noexn :: E) ())){
//   val @uniq-b@10542 : bool
//         = val x@1@10546 : (std/async/async/scope, () -> (io-noexn :: E) ())
//                 = @uniq-x@10541;
//         match (x@1@10546) {
//           ((@skip std/core/types/Tuple2((@x: std/async/async/scope) : std/async/async/scope, (@pat@0@4: () -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()) : () -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()) : (std/async/async/scope, () -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()) ) as @pat@6: (std/async/async/scope, () -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()))
//              -> (match (@x) {
//               ((@skip std/async/async/Scope((ids1@0: (list :: V -> V)<int>) : (list :: V -> V)<int>) : std/async/async/scope ) as @pat@5: std/async/async/scope)
//                  -> (match (cscope) {
//                   ((@skip std/async/async/Scope((ids2@0: (list :: V -> V)<int>) : (list :: V -> V)<int>) : std/async/async/scope ) as @pat@0@3: std/async/async/scope)
//                      -> std/core/list/(==)<int,(total :: E)>(ids1@0, ids2@0, std/core/int/(==));
//                 });
//             });
//         };
//   match (@uniq-b@10542) {
//     ((std/core/types/True() : bool ) as @uniq-pat@0@10543: bool)
//        -> std/core/types/False;
//     ((@skip std/core/types/False() : bool ) as @uniq-pat@0@0@10544: bool)
//        -> std/core/types/True;
//   };
// },Own)
fun async/@lift-handle@10750 : (cscope : scope, @uniq-xs@10547 : list<(scope, () -> io-noexn ())>) -> list<(scope, () -> io-noexn ())>
  = fn(cscope@0: scope, @uniq-xs@10547@0: list<(scope, () -> io-noexn ())>){
    std/async/async/async/@trmc-lift-handle@10750(cscope@0, @uniq-xs@10547@0, (std/core/types/cctx/empty()));
  };
// lifted local: _@0, cb, handle-await, async/handle, @spec-x10545
// specialized: std/core/list/remove, on parameters @uniq-pred@10538, using:
// @uniq-pred@10538 = (fn(x@1: (std/async/async/scope, () -> (io-noexn :: E) ())){
//   match (x@1) {
//     ((@skip std/core/types/Tuple2((@x: std/async/async/scope) : std/async/async/scope, (@pat@0@4: () -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()) : () -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()) : (std/async/async/scope, () -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()) ) as @pat@6: (std/async/async/scope, () -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()))
//        -> (match (@x) {
//         ((@skip std/async/async/Scope((ids1@0: (list :: V -> V)<int>) : (list :: V -> V)<int>) : std/async/async/scope ) as @pat@5: std/async/async/scope)
//            -> (match (cscope) {
//             ((@skip std/async/async/Scope((ids2@0: (list :: V -> V)<int>) : (list :: V -> V)<int>) : std/async/async/scope ) as @pat@0@3: std/async/async/scope)
//                -> std/core/list/(==)<int,(total :: E)>(ids1@0, ids2@0, std/core/int/(==));
//           });
//       });
//   };
// },Own)
fun async/@lift-handle@10749 : (cscope : scope, @uniq-xs@10537 : list<(scope, () -> io-noexn ())>) -> list<(scope, () -> io-noexn ())>
  = fn(cscope: scope, @uniq-xs@10537: list<(scope, () -> io-noexn ())>){
    match (@uniq-xs@10537) {
      ((std/core/types/Nil() : list<(scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())> ) as @uniq-pat@2@10539: (list<(scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())>))
         -> std/core/types/Nil;
      (@uniq-pat@10540: (list<(scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())>))
         -> std/async/async/async/@trmc-lift-handle@10750(cscope, @uniq-xs@10537, (std/core/types/cctx/empty()));
    };
  };
// lifted local: async/@lift-handle@10753, async/handle, @spec-x10596
// specialized: std/core/list/@unroll-foreach@10016, on parameters @uniq-action@10591, using:
// @uniq-action@10591 = (fn<<(alloc :: H -> X)<(global :: H)>,(console/console :: X),(div :: X),(fsys :: X),(ndet :: X),(net :: X),(read :: H -> X)<(global :: H)>,(ui :: X),(write :: H -> X)<(global :: H)>>>(entry: (std/async/async/scope, () -> (io-noexn :: E) ())){
//   match (entry) {
//     ((@skip std/core/types/Tuple2(((@skip std/async/async/Scope((@pat@10: (list :: V -> V)<int>) : (list :: V -> V)<int>) : std/async/async/scope ) as cscope@0: std/async/async/scope) : std/async/async/scope, (cb@0: () -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()) : () -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()) : (std/async/async/scope, () -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()) ) as @pat@9: (std/async/async/scope, () -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()))
//        -> (match (scope@1@0) {
//         ((@skip std/async/async/Scope((pids: (list :: V -> V)<int>) : (list :: V -> V)<int>) : std/async/async/scope ) as @pat@11: std/async/async/scope)
//            -> (match (cscope@0) {
//             ((@skip std/async/async/Scope((cids@0: (list :: V -> V)<int>) : (list :: V -> V)<int>) : std/async/async/scope ) as @pat@0@7: std/async/async/scope)
//                -> (match (pids) {
//                 ((std/core/types/Nil() : (list :: V -> V)<int> ) as @pat@12: ((list :: V -> V)<int>))
//                    -> cb@0();
//                 (@pat@13: ((list :: V -> V)<int>))
//                    -> (match ((std/async/async/ids/@unroll-in-scope-of@10000(cids@0, pids))) {
//                     ((std/core/types/True() : bool ) as @pat@11@0: bool)
//                        -> cb@0();
//                     ((@skip std/core/types/False() : bool ) as @pat@12@0: bool)
//                        -> std/core/types/Unit;
//                   });
//               });
//           });
//       });
//   };
// },Own)
fun async/@lift-handle@10754 : (scope@1@0 : scope, @uniq-xs@10590 : list<(scope, () -> io-noexn ())>) -> <alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>> ()
  = fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(scope@1@0: scope, @uniq-xs@10590: list<(scope, () -> io-noexn ())>){
    match (@uniq-xs@10590) {
      ((std/core/types/Cons((@uniq-x@10593: (scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())), (@uniq-xx@10594: list<(scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())>)) : list<(scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,
   alloc<global>>)>)>) ())> ) as @uniq-pat@10592: (list<(scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())>))
         -> val _ : ()
                  = (match (@uniq-x@10593) {
                    ((@skip std/core/types/Tuple2(((@skip std/async/async/Scope((@pat@10: list<int>)) : scope ) as cscope@0: scope), (cb@0: () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())) : (scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) ) as @pat@9: (scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,
   console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()))
                       -> (match (scope@1@0) {
                        ((@skip std/async/async/Scope((pids: list<int>)) : scope ) as @pat@11: scope)
                           -> (match (cscope@0) {
                            ((@skip std/async/async/Scope((cids@0: list<int>)) : scope ) as @pat@0@7: scope)
                               -> (match (pids) {
                                ((std/core/types/Nil() : list<int> ) as @pat@12: (list<int>))
                                   -> cb@0();
                                (@pat@13: (list<int>))
                                   -> (match ((std/async/async/ids/@unroll-in-scope-of@10000(cids@0, pids))) {
                                    ((std/core/types/True() : bool ) as @pat@11@0: bool)
                                       -> cb@0();
                                    ((@skip std/core/types/False() : bool ) as @pat@12@0: bool)
                                       -> std/core/types/Unit;
                                  });
                              });
                          });
                      });
                  });
        std/async/async/async/@lift-handle@10754(scope@1@0, @uniq-xx@10594);
      ((@skip std/core/types/Nil() : list<(scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())> ) as @uniq-pat@0@10595: (list<(scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())>))
         -> std/core/types/Unit;
    };
  };
// lifted local: async/handle, @spec-x10589
// specialized: std/core/list/foreach, on parameters @uniq-action@10586, using:
// @uniq-action@10586 = (fn<<(alloc :: H -> X)<(global :: H)>,(console/console :: X),(div :: X),(fsys :: X),(ndet :: X),(net :: X),(read :: H -> X)<(global :: H)>,(ui :: X),(write :: H -> X)<(global :: H)>>>(entry: (std/async/async/scope, () -> (io-noexn :: E) ())){
//   match (entry) {
//     ((@skip std/core/types/Tuple2(((@skip std/async/async/Scope((@pat@10: (list :: V -> V)<int>) : (list :: V -> V)<int>) : std/async/async/scope ) as cscope@0: std/async/async/scope) : std/async/async/scope, (cb@0: () -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()) : () -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()) : (std/async/async/scope, () -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()) ) as @pat@9: (std/async/async/scope, () -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()))
//        -> (match (scope@1@0) {
//         ((@skip std/async/async/Scope((pids: (list :: V -> V)<int>) : (list :: V -> V)<int>) : std/async/async/scope ) as @pat@11: std/async/async/scope)
//            -> (match (cscope@0) {
//             ((@skip std/async/async/Scope((cids@0: (list :: V -> V)<int>) : (list :: V -> V)<int>) : std/async/async/scope ) as @pat@0@7: std/async/async/scope)
//                -> (match (pids) {
//                 ((std/core/types/Nil() : (list :: V -> V)<int> ) as @pat@12: ((list :: V -> V)<int>))
//                    -> cb@0();
//                 (@pat@13: ((list :: V -> V)<int>))
//                    -> (match ((std/async/async/ids/@unroll-in-scope-of@10000(cids@0, pids))) {
//                     ((std/core/types/True() : bool ) as @pat@11@0: bool)
//                        -> cb@0();
//                     ((@skip std/core/types/False() : bool ) as @pat@12@0: bool)
//                        -> std/core/types/Unit;
//                   });
//               });
//           });
//       });
//   };
// },Own)
fun async/@lift-handle@10753 : (scope@1@0 : scope, @uniq-xs@10585 : list<(scope, () -> io-noexn ())>) -> <alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>> ()
  = fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(scope@1@0: scope, @uniq-xs@10585: list<(scope, () -> io-noexn ())>){
    match (@uniq-xs@10585) {
      ((std/core/types/Nil() : list<(scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())> ) as @uniq-pat@0@10587: (list<(scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())>))
         -> std/core/types/Unit;
      (@uniq-pat@10588: (list<(scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())>))
         -> std/async/async/async/@lift-handle@10754(scope@1@0, @uniq-xs@10585);
    };
  };
// monadic lift
fun async/@mlift-handle@11382 : (@y-x10858 : ()) -> <exn,alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>> error<()>
  = fn<<exn,alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@y-x10858: ()){
    std/core/exn/Ok(@y-x10858);
  };
// monadic lift
fun async/@mlift-handle@11383 : forall<a> (f : (error<a>) -> io-noexn (), res : error<a>, @c-x10860 : ()) -> ()
  = forall<a> fn(f: (error<a>) -> io-noexn (), res: error<a>, @c-x10860: ()){
    f(res);
  };
// The outer `:async` effect handler. This is automatically applied by the compiler
// around the `main` function if it has an `:async` effect.
pub fun async/handle : (action : () -> <st<global>,async,console/console,div,fsys,ndet,net,ui> ()) -> <st<global>,console/console,div,fsys,ndet,net,ui> ()
  = fn<io-noexn>(action: () -> <async,io-noexn> ()){
    val callbacks : ref<global,list<(scope, () -> io-noexn ())>>
      = std/core/types/ref(std/core/types/Nil);
    val handle-await : forall<a> (setup : await-setup<a>, scope : scope, f : (error<a>) -> io-noexn (), cancelable@0 : bool) -> io-noexn ()
      = forall<a> fn<io-noexn>(setup: await-setup<a>, scope: scope, f: (error<a>) -> io-noexn (), cancelable@0: bool){
        val u : int
          = std/core/types/ref/(!)(std/core/unique-count, std/core/types/@Hnodiv);
        val _ : ()
          = std/core/types/set(std/core/unique-count, (std/core/int/int-add(u, 1)));
        val cscope : scope
          = (match (scope) {
            ((@skip std/async/async/Scope((cids: list<int>)) : scope ) as @pat: scope)
               -> val ys@10034 : list<int>
                        = std/core/types/Cons(u, std/core/types/Nil);
              std/async/async/Scope((match (cids) {
                ((std/core/types/Nil() : list<int> ) as @pat@0: (list<int>))
                   -> ys@10034;
                (@pat@1: (list<int>))
                   -> std/core/list/@unroll-append@10004(cids, ys@10034);
              }));
          });
        val dispose : ref<global,() -> <alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>,exn> ()>
          = std/core/types/ref((fn<io-noexn>(){
            std/core/types/Unit;
          }));
        val cb : (res : error<a>, is-done : bool) -> io-noexn ()
          = fn<io-noexn>(res: error<a>, is-done: bool){
            val xs@0@10035 : list<(scope, () -> io-noexn ())>
              = std/core/types/ref/(!)(callbacks, std/core/types/@Hdiv);
            val mb@10037 : maybe<() -> io-noexn ()>
              = std/async/async/async/@lift-handle@10745(cscope, xs@0@10035);
            (match (mb@10037) {
              ((std/core/types/Just((@pat@0@0: () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())) : maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()> ) as @pat@2: (maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>))
                 -> val x@11549 : ()
                          = (match (is-done) {
                            ((std/core/types/True() : bool ) as @pat@0@2: bool)
                               -> val xs@2@10042 : list<(scope, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())>
                                    = std/core/types/ref/(!)(callbacks, std/core/types/@Hdiv);
                                  val _ : ()
                                    = std/core/types/set(callbacks, (std/async/async/async/@lift-handle@10749(cscope, xs@2@10042)));
                              (match (res) {
                                ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@1@1: string), (@pat@2@0: exception-info)) : exception ) as @pat@0@5: exception)) : error<a> ) as @pat@7: (error<a>))
                                   -> val action@1@10050 : () -> <exn,alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>> ()
                                        = std/core/types/ref/(!)(dispose, std/core/types/@Hdiv);
                                      val t@10048 : error<()>
                                        = std/core/exn/exn/@handle((std/core/exn/@Hnd-exn(0, (forall<b> std/core/hnd/Clause1((fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(m: hnd/marker<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>,error<()>>, @_wildcard-x653_16: hnd/ev<exn>, x@0: exception){
                                              (std/core/hnd/yield-to-final(m, (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@_wildcard-x653_45: (hnd/resume-result<b,error<()>>) -> <alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>> error<()>){
                                                  (std/core/exn/Error(x@0));
                                                })));
                                            }))))), (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@res: error<()>){
                                            @res;
                                          }), (fn<<exn,alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(){
                                            val x@1@11552 : ()
                                                  = (action@1@10050());
                                            (match ((std/core/hnd/yielding())) {
                                              ((std/core/types/True() : bool ) as @pat@4: bool)
                                                 -> std/core/hnd/yield-extend(std/async/async/async/@mlift-handle@11382);
                                              ((@skip std/core/types/False() : bool ) as @pat@0@3: bool)
                                                 -> std/core/exn/Ok(x@1@11552);
                                            });
                                          }));
                                  (match (t@10048) {
                                    ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@1@3: string), (@pat@2@1: exception-info)) : exception ) as @pat@0@6: exception)) : error<()> ) as @pat@8: (error<()>))
                                       -> std/core/types/Unit;
                                    ((@skip std/core/exn/Ok((x@2: ())) : error<()> ) as @pat@3@1: (error<()>))
                                       -> x@2;
                                  });
                                (@pat@3@0: (error<a>))
                                   -> std/core/types/Unit;
                              });
                            ((@skip std/core/types/False() : bool ) as @pat@3@2: bool)
                               -> std/core/types/Unit;
                          });
                (match ((std/core/hnd/yielding())) {
                  ((std/core/types/True() : bool ) as @pat@3: bool)
                     -> std/core/hnd/yield-extend((fn(@c-x10860: ()){
                      (f(res));
                    }));
                  ((@skip std/core/types/False() : bool ) as @pat@0@1: bool)
                     -> f(res);
                });
              ((@skip std/core/types/Nothing() : maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()> ) as @pat@1@0: (maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>))
                 -> std/core/types/Unit;
            });
          };
        val _@1 : ()
          = std/core/types/set(callbacks, (std/core/types/Cons((std/core/types/Tuple2(cscope, (match (cancelable@0) {
                  ((std/core/types/True() : bool ) as @pat@5@0: bool)
                     -> fn<(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>(){
                      cb((std/core/exn/Error((std/core/exn/Exception("cancel", std/async/async/Cancel)))), std/core/types/True);
                    };
                  ((@skip std/core/types/False() : bool ) as @pat@6@0: bool)
                     -> fn<(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>(){
                      std/core/types/Unit;
                    };
                }))), (std/core/types/ref/(!)(callbacks, std/core/types/@Hdiv)))));
        std/core/exn/exn/@handle((std/core/exn/@Hnd-exn(0, (forall<b> std/core/hnd/Clause1((fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(m@0: hnd/marker<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>,()>, @_wildcard-x653_16@0: hnd/ev<exn>, x@3: exception){
              (std/core/hnd/yield-to-final(m@0, (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@_wildcard-x653_45@0: (hnd/resume-result<b,()>) -> <alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>> ()){
                  (cb((std/core/exn/Error(x@3)), std/core/types/True));
                })));
            }))))), (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@res@0: ()){
            @res@0;
          }), (fn<<exn,alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(){
            (match ((std/core/hnd/@open-none1(setup, cb))) {
              ((std/core/types/Just((d: () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())) : maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()> ) as @pat@7@0: (maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>))
                 -> std/core/types/set(dispose, (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>,exn>>(){
                    (std/core/hnd/@open-none0(d));
                  }));
              ((@skip std/core/types/Nothing() : maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()> ) as @pat@8@0: (maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>))
                 -> std/core/types/Unit;
            });
          }));
      };
    std/async/async/async/@handle((std/async/async/@Hnd-async(3, (forall<a> std/core/hnd/Clause1((fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@_wildcard-x648_14: hnd/marker<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>,()>, @_wildcard-x648_17: hnd/ev<async>, x@4: () -> io-noexn _3520){
          (x@4());
        }))), (std/core/hnd/Clause1((fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@_wildcard-x648_14@0: hnd/marker<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>,()>, @_wildcard-x648_17@0: hnd/ev<async>, x@5: scope){
          val @uniq-xs@10585 : (list<(scope, () -> io-noexn ())>)
                = (std/core/types/ref/(!)(callbacks, std/core/types/@Hdiv));
          (std/async/async/async/@lift-handle@10753(x@5, @uniq-xs@10585));
        }))), (forall<a> std/core/hnd/Clause1((fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(m@1: hnd/marker<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>,()>, @_wildcard-x597_16: hnd/ev<async>, x@6: (await-setup<_3524>, scope, bool)){
          (std/core/hnd/yield-to(m@1, (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(k: (hnd/resume-result<error<_3524>,()>) -> <alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>> ()){
              (match (x@6) {
                ((@skip std/core/types/Tuple3((x1: (await-setup<_3524> == 4 (cb : (error<_3524>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,
   alloc<global>>)>)>) ()>)), (x2: scope), (x3: bool)) : ((await-setup<_b> == 4 (cb : (error<_b>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,
   alloc<global>>)>)>) ()>), scope, bool) ) as @pat@5: ((await-setup<_3524> == 4 (cb : (error<_3524>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>
   ,alloc<global>>)>)>) ()>), scope, bool))
                   -> handle-await(x1, x2, (fn<(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>(x@3@0: error<a>){
                      (k((std/core/hnd/Deep(x@3@0))));
                    }), x3);
              });
            })));
        }))), (forall<a> std/core/hnd/Clause1((fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@_wildcard-x648_14@1: hnd/marker<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>,()>, @_wildcard-x648_17@1: hnd/ev<async>, x@8: (await-setup<_3527>, scope, bool, (error<_3527>) -> io-noexn ())){
          (match (x@8) {
            ((@skip std/core/types/Tuple4((x1@0: (await-setup<_3527> == 4 (cb : (error<_3527>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<
   global>>)>)>) ()>)), (x2@0: scope), (x3@0: bool), (x4: (error<_3527>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())) : ((await-setup<_b> == 4 (cb : (error<_b>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,
   write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<_b>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) ) as @pat@9: ((await-setup<_3527> == 4 (cb : (error<_3527>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <
   read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<_3527>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())
   )
               -> handle-await(x1@0, x2@0, x4, x3@0);
          });
        }))))), (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@res@1: ()){
        @res@1;
      }), action);
  };
pub fun @default-async : (action : () -> <st<global>,async,console/console,div,fsys,ndet,net,ui> ()) -> <st<global>,console/console,div,fsys,ndet,net,ui> ()
  = fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(action: () -> <st<global>,async,console/console,div,fsys,ndet,net,ui> ()){
    std/async/async/async/handle(action);
  };
fun io-noexn1 : forall<a,b> (f : (b) -> io-noexn a, x1 : b) -> io a
  = forall<a,b> fn<io>(f: (b) -> io-noexn a, x1: b){
    std/core/hnd/@open-none1(f, x1);
  };
// monadic lift
fun @mlift-await1@11384 : (@y-x10866 : maybe<() -> io-noexn ()>) -> io error<maybe<() -> io-noexn ()>>
  = fn<io>(@y-x10866: maybe<() -> io-noexn ()>){
    std/core/exn/Ok(@y-x10866);
  };
// monadic lift
fun @mlift-await1@11385 : (wild_@0 : ()) -> io maybe<() -> io-noexn ()>
  = fn<io>(wild_@0: ()){
    std/core/types/Nothing;
  };
// monadic lift
fun @mlift-await1@11386 : forall<a> (@y-x10869 : error<a>) -> <async,exn,ndet> a
  = forall<a> fn<<async,exn,ndet>>(@y-x10869: error<a>){
    val i@11564 : hnd/ev-index
      = std/core/types/@make-ssize_t(1);
    val w : hnd/evv<<exn,async,ndet>>
      = std/core/hnd/evv-swap-create1(i@11564);
    val y : a
      = (match (@y-x10869) {
        ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@0: string), (@pat@1@0: exception-info)) : exception ) as exn@0: exception)) : error<a> ) as @pat@1: (error<a>))
           -> val ev@11567 : hnd/ev<exn>
                    = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
          (match (ev@11567) {
            ((@skip std/core/hnd/Ev<e,b>((@pat@0@1: hnd/htag<exn>), (m: hnd/marker<e,b>), (h: exn<e,b>), (@pat@1@1: hnd/evv<e>)) : hnd/ev<exn> ) as @pat@2: (hnd/ev<exn>))
               -> (match ((std/core/exn/throw-exn/@select(h))) {
                ((@skip std/core/hnd/Clause1((f@0: (hnd/marker<e,b>, hnd/ev<exn>, exception) -> e a)) : hnd/clause1<exception,a,exn,e,b> ) as @pat@2@0: (hnd/clause1<exception,a,exn,e,b>))
                   -> f@0(m, ev@11567, exn@0);
              });
          });
        ((@skip std/core/exn/Ok((x@1: a)) : error<a> ) as @pat@2@1: (error<a>))
           -> x@1;
      });
    val _ : ()
      = std/core/hnd/evv-set(w);
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-cont((forall<b> fn<<exn,async,ndet>>(cont: (b) -> <exn,async,ndet> a, res: b){
          std/core/hnd/open-at1(i@11564, cont, res);
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> y;
    });
  };
// Convenience function for awaiting a single argument callback.
pub fun await1 : forall<a> (setup : (cb : (a) -> io-noexn ()) -> io ()) -> asyncx a
  = forall<a> fn<asyncx>(setup: (cb : (a) -> io-noexn ()) -> io ()){
    val i@11573 : hnd/ev-index
      = std/core/types/@make-ssize_t(0);
    val w : hnd/evv<<async,exn,ndet>>
      = std/core/hnd/evv-swap-create1(i@11573);
    val ev@11576 : hnd/ev<async>
      = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
    val y : error<a>
      = (match (ev@11576) {
        ((@skip std/core/hnd/Ev<e,b>((@pat@0@1: hnd/htag<async>), (m: hnd/marker<e,b>), (h: async<e,b>), (@pat@1@0: hnd/evv<e>)) : hnd/ev<async> ) as @pat@2: (hnd/ev<async>))
           -> (match (h) {
            ((@skip std/async/async/@Hnd-async((@pat@0: int), (@pat@1: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e,b>), (@pat@2@0: hnd/clause1<scope,(),async,e,b>), (@ctl-do-await: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>
   )>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e,b>), (@pat@3: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async
   ,e,b>))) : async<e,b> ) as @pat: (async<e,b>))
               -> (match (@ctl-do-await) {
                ((@skip std/core/hnd/Clause1((f@0: (hnd/marker<e,b>, hnd/ev<async>, ((await-setup<a> == 4 (cb : (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()>), scope, bool)) -> e error<a>)) : hnd/clause1<((await-setup<a> == 4 (cb : (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global>
   == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<a>,async,e,b> ) as @pat@2@0@0: (hnd/clause1<((await-setup<a> == 4 (cb : (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/
   console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<a>,async,e,b>))
                   -> f@0(m, ev@11576, (std/core/types/Tuple3((fn<(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>(cb: (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()){
                        (match ((std/core/exn/exn/@handle((std/core/exn/@Hnd-exn(0, (forall<c> std/core/hnd/Clause1((fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(m@0: hnd/marker<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>,error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>>, @_wildcard-x653_16: hnd/ev<exn>, x@1: exception){
                              (std/core/hnd/yield-to-final(m@0, (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@_wildcard-x653_45: (hnd/resume-result<c,error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>>) -> <alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>> error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,
   fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>){
                                  (std/core/exn/Error(x@1));
                                })));
                            }))))), (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@res: error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>){
                            @res;
                          }), (fn<<exn,alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(){
                            val x@3@11584 : ()
                              = (setup((fn<(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>(x@0@0: a){
                                (cb((std/core/exn/Ok(x@0@0)), std/core/types/True));
                              })));
                            val x@2@11582 : (maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)
                              = (match ((std/core/hnd/yielding())) {
                                ((std/core/types/True() : bool ) as @pat@4: bool)
                                   -> std/core/hnd/yield-extend(std/async/async/@mlift-await1@11385);
                                ((@skip std/core/types/False() : bool ) as @pat@0@3: bool)
                                   -> std/core/types/Nothing;
                              });
                            (match ((std/core/hnd/yielding())) {
                              ((std/core/types/True() : bool ) as @pat@3@0: bool)
                                 -> std/core/hnd/yield-extend(std/async/async/@mlift-await1@11384);
                              ((@skip std/core/types/False() : bool ) as @pat@0@2: bool)
                                 -> std/core/exn/Ok(x@2@11582);
                            });
                          })))) {
                          ((std/core/exn/Ok((mcleanup: maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)) : error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>> ) as @pat@3@0@0: (error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<
   global>,alloc<global>>)>)>) ()>>))
                             -> mcleanup;
                          ((@skip std/core/exn/Error(((@skip std/core/exn/Exception((@pat@1@0@0: string), (@pat@2@0@0@0: exception-info)) : exception ) as exn: exception)) : error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>> ) as @pat@0@0@0: (error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>))
                             -> val _ : ()
                                      = cb((std/core/exn/Error(exn)), std/core/types/True);
                            std/core/types/Nothing;
                        });
                      }), std/async/async/empty-scope, std/core/types/True)));
              });
          });
      });
    val _ : ()
      = std/core/hnd/evv-set(w);
    val x@11570 : error<a>
      = (match ((std/core/hnd/yielding())) {
        ((std/core/types/True() : bool ) as @pat@1@1: bool)
           -> std/core/hnd/yield-cont((forall<b> fn<<async,exn,ndet>>(cont: (b) -> <async,exn,ndet> error<a>, res: b){
            std/core/hnd/open-at1(i@11573, cont, res);
          }));
        ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
           -> y;
      });
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat@5: bool)
         -> std/core/hnd/yield-extend((fn<<async,exn,ndet>>(@y-x10869: error<a>){
          (std/async/async/@mlift-await1@11386(@y-x10869));
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0@4: bool)
         -> val i@0@11586 : (hnd/ev-index == 1 ssize_t)
              = std/core/types/@make-ssize_t(1);
            val w@0 : hnd/evv<<exn,async,ndet>>
              = std/core/hnd/evv-swap-create1(i@0@11586);
            val y@0 : a
              = (match (x@11570) {
                ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@5: string), (@pat@1@1@0: exception-info)) : exception ) as exn@0: exception)) : error<a> ) as @pat@6: (error<a>))
                   -> val ev@0@11589 : hnd/ev<exn>
                            = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
                  (match (ev@0@11589) {
                    ((@skip std/core/hnd/Ev<e,b>((@pat@0@6: hnd/htag<exn>), (m@1: hnd/marker<e,b>), (h@0: exn<e,b>), (@pat@1@2: hnd/evv<e>)) : hnd/ev<exn> ) as @pat@7: (hnd/ev<exn>))
                       -> (match ((std/core/exn/throw-exn/@select(h@0))) {
                        ((@skip std/core/hnd/Clause1((f@2: (hnd/marker<e,b>, hnd/ev<exn>, exception) -> e a)) : hnd/clause1<exception,a,exn,e,b> ) as @pat@2@1: (hnd/clause1<exception,a,exn,e,b>))
                           -> f@2(m@1, ev@0@11589, exn@0);
                      });
                  });
                ((@skip std/core/exn/Ok((x@6: a)) : error<a> ) as @pat@2@2: (error<a>))
                   -> x@6;
              });
            val _ : ()
              = std/core/hnd/evv-set(w@0);
        (match ((std/core/hnd/yielding())) {
          ((std/core/types/True() : bool ) as @pat@5@0: bool)
             -> std/core/hnd/yield-cont((forall<b> fn<<exn,async,ndet>>(cont@0: (b) -> <exn,async,ndet> a, res@1: b){
              std/core/hnd/open-at1(i@0@11586, cont@0, res@1);
            }));
          ((@skip std/core/types/False() : bool ) as @pat@0@4@0: bool)
             -> y@0;
        });
    });
  };
// monadic lift
fun promise/@mlift-await@11387 : (@y-x10874 : maybe<() -> io-noexn ()>) -> io error<maybe<() -> io-noexn ()>>
  = fn<io>(@y-x10874: maybe<() -> io-noexn ()>){
    std/core/exn/Ok(@y-x10874);
  };
// monadic lift
fun promise/@mlift-await@11388 : (@c-x10876 : ()) -> maybe<() -> io-noexn ()>
  = fn(@c-x10876: ()){
    std/core/types/Nothing;
  };
// monadic lift
fun promise/@mlift-await@11389 : forall<a> (@y-x10877 : error<a>) -> <async,exn,ndet> a
  = forall<a> fn<<async,exn,ndet>>(@y-x10877: error<a>){
    val i@11592 : hnd/ev-index
      = std/core/types/@make-ssize_t(1);
    val w : hnd/evv<<exn,async,ndet>>
      = std/core/hnd/evv-swap-create1(i@11592);
    val y : a
      = (match (@y-x10877) {
        ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@0: string), (@pat@1@0: exception-info)) : exception ) as exn@0: exception)) : error<a> ) as @pat@1: (error<a>))
           -> val ev@11595 : hnd/ev<exn>
                    = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
          (match (ev@11595) {
            ((@skip std/core/hnd/Ev<e,b>((@pat@0@1: hnd/htag<exn>), (m: hnd/marker<e,b>), (h: exn<e,b>), (@pat@1@1: hnd/evv<e>)) : hnd/ev<exn> ) as @pat@2: (hnd/ev<exn>))
               -> (match ((std/core/exn/throw-exn/@select(h))) {
                ((@skip std/core/hnd/Clause1((f@0: (hnd/marker<e,b>, hnd/ev<exn>, exception) -> e a)) : hnd/clause1<exception,a,exn,e,b> ) as @pat@2@0: (hnd/clause1<exception,a,exn,e,b>))
                   -> f@0(m, ev@11595, exn@0);
              });
          });
        ((@skip std/core/exn/Ok((x@1: a)) : error<a> ) as @pat@2@0@0: (error<a>))
           -> x@1;
      });
    val _ : ()
      = std/core/hnd/evv-set(w);
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-cont((forall<b> fn<<exn,async,ndet>>(cont: (b) -> <exn,async,ndet> a, res: b){
          std/core/hnd/open-at1(i@11592, cont, res);
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> y;
    });
  };
// monadic lift
fun promise/@mlift-await@11390 : forall<a> (p : promise<a>, @y-x10871 : maybe<a>) -> <async,ndet,exn> a
  = forall<a> fn<<async,ndet,exn>>(p: promise<a>, @y-x10871: maybe<a>){
    (match (@y-x10871) {
      ((std/core/types/Just((v: a)) : maybe<a> ) as @pat@1: (maybe<a>))
         -> v;
      ((@skip std/core/types/Nothing() : maybe<a> ) as @pat@2: (maybe<a>))
         -> val i@11600 : (hnd/ev-index == 1 ssize_t)
              = std/core/types/@make-ssize_t(0);
            val w : hnd/evv<<async,exn,ndet>>
              = std/core/hnd/evv-swap-create1(i@11600);
            val ev@11603 : hnd/ev<async>
              = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
            val y : error<a>
              = (match (ev@11603) {
                ((@skip std/core/hnd/Ev<e,b>((@pat@0@1: hnd/htag<async>), (m: hnd/marker<e,b>), (h: async<e,b>), (@pat@1@0: hnd/evv<e>)) : hnd/ev<async> ) as @pat@4: (hnd/ev<async>))
                   -> (match (h) {
                    ((@skip std/async/async/@Hnd-async((@pat@0: int), (@pat@1@1: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e,b>), (@pat@2@0: hnd/clause1<scope,(),async,e,b>), (@ctl-do-await: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<
   global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e,b>), (@pat@3: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 
   <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),()
   ,async,e,b>))) : async<e,b> ) as @pat: (async<e,b>))
                       -> (match (@ctl-do-await) {
                        ((@skip std/core/hnd/Clause1((f@0: (hnd/marker<e,b>, hnd/ev<async>, ((await-setup<a> == 4 (cb : (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 
   1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool)) -> e error<a>)) : hnd/clause1<((await-setup<a> == 4 (cb : (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<
   global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<a>,async,e,b> ) as @pat@2@0@0: (hnd/clause1<((await-setup<a> == 4 (cb : (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,
   console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<a>,async,e,b>))
                           -> f@0(m, ev@11603, (std/core/types/Tuple3((fn<(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>(cb: (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()){
                                (match ((std/core/exn/exn/@handle((std/core/exn/@Hnd-exn(0, (forall<c> std/core/hnd/Clause1((fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(m@0: hnd/marker<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>,error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>>, @_wildcard-x653_16: hnd/ev<exn>, x@1: exception
   ){
                                      (std/core/hnd/yield-to-final(m@0, (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@_wildcard-x653_45: (hnd/resume-result<c,error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>>) -> <alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>> error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/
   console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>){
                                          (std/core/exn/Error(x@1));
                                        })));
                                    }))))), (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@res: error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>){
                                    @res;
                                  }), (fn<<exn,alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(){
                                    val w@0 : (hnd/evv<<alloc<global>,console/console,div,exn,fsys,ndet,net,read<global>,ui,write<global>>>)
                                      = (std/core/hnd/evv-swap-create0());
                                    val keep : ()
                                      = (std/core/hnd/evv-set(w@0));
                                    val x@4@11613 : ()
                                      = (match ((std/core/types/ref/(!)((match (p) {
                                          ((@skip std/async/async/Promise((@x: ref<global,promise-state<a>>)) : promise<a> ) as @pat@3@0@0: (promise<a>))
                                             -> @x;
                                        }), std/core/types/@Hnodiv))) {
                                        ((std/async/async/Awaiting((listeners: list<(a) -> (io == 4 <exn,(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>) ()>)) : promise-state<a> ) as @pat@4@0: (promise-state<a>))
                                           -> std/core/types/set((match (p) {
                                              ((@skip std/async/async/Promise((@x@0: ref<global,promise-state<a>>)) : promise<a> ) as @pat@3@0@0@0: (promise<a>))
                                                 -> @x@0;
                                            }), (std/async/async/Awaiting((std/core/types/Cons((fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>,exn>>(@x-x1@2: a){
                                                val w@1 : (hnd/evv<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>,exn>>)
                                                  = (std/core/hnd/evv-swap-create0());
                                                val x@5 : ()
                                                  = (cb((std/core/exn/Ok(@x-x1@2)), std/core/types/True));
                                                val keep@0 : ()
                                                  = (std/core/hnd/evv-set(w@1));
                                                x@5;
                                              }), listeners)))));
                                        ((@skip std/async/async/Resolved((value: a)) : promise-state<a> ) as @pat@0@0@0@0: (promise-state<a>))
                                           -> val w@2 : hnd/evv<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>,exn>>
                                                = std/core/hnd/evv-swap-create0();
                                              val x@6 : ()
                                                = cb((std/core/exn/Ok(value)), std/core/types/True);
                                              val keep@1 : ()
                                                = std/core/hnd/evv-set(w@2);
                                          x@6;
                                      });
                                    val x@2@11609 : (maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)
                                      = (match ((std/core/hnd/yielding())) {
                                        ((std/core/types/True() : bool ) as @pat@6: bool)
                                           -> std/core/hnd/yield-extend(std/async/async/promise/@mlift-await@11388);
                                        ((@skip std/core/types/False() : bool ) as @pat@0@3: bool)
                                           -> std/core/types/Nothing;
                                      });
                                    (match ((std/core/hnd/yielding())) {
                                      ((std/core/types/True() : bool ) as @pat@5: bool)
                                         -> std/core/hnd/yield-extend(std/async/async/promise/@mlift-await@11387);
                                      ((@skip std/core/types/False() : bool ) as @pat@0@2: bool)
                                         -> std/core/exn/Ok(x@2@11609);
                                    });
                                  })))) {
                                  ((std/core/exn/Ok((mcleanup: maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)) : error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>> ) as @pat@3@0: (error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,
   write<global>,alloc<global>>)>)>) ()>>))
                                     -> mcleanup;
                                  ((@skip std/core/exn/Error(((@skip std/core/exn/Exception((@pat@1@1@0: string), (@pat@2@1: exception-info)) : exception ) as exn: exception)) : error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>> ) as @pat@0@0@0: (error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>))
                                     -> val _ : ()
                                              = cb((std/core/exn/Error(exn)), std/core/types/True);
                                    std/core/types/Nothing;
                                });
                              }), std/async/async/empty-scope, std/core/types/True)));
                      });
                  });
              });
            val _ : ()
              = std/core/hnd/evv-set(w);
            val x@11598 : error<a>
              = (match ((std/core/hnd/yielding())) {
                ((std/core/types/True() : bool ) as @pat@3@1: bool)
                   -> std/core/hnd/yield-cont((forall<b> fn<<async,exn,ndet>>(cont: (b) -> <async,exn,ndet> error<a>, res: b){
                    std/core/hnd/open-at1(i@11600, cont, res);
                  }));
                ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
                   -> y;
              });
        (match ((std/core/hnd/yielding())) {
          ((std/core/types/True() : bool ) as @pat@7: bool)
             -> std/core/hnd/yield-extend((fn<<async,exn,ndet>>(@y-x10877: error<a>){
              (std/async/async/promise/@mlift-await@11389(@y-x10877));
            }));
          ((@skip std/core/types/False() : bool ) as @pat@0@4: bool)
             -> std/async/async/promise/@mlift-await@11389(x@11598);
        });
    });
  };
// Await a promise; returns immediately if the promise was already resolved and otherwise
// waits asynchronously.
pub fun promise/await : forall<a> (p : promise<a>) -> asyncx a
  = forall<a> fn<asyncx>(p: promise<a>){
    val i@11622 : hnd/ev-index
      = std/core/types/@make-ssize_t(0);
    val w : hnd/evv<<async,ndet,exn>>
      = std/core/hnd/evv-swap-create1(i@11622);
    val y : maybe<a>
      = std/async/async/try-await(p);
    val _ : ()
      = std/core/hnd/evv-set(w);
    val x@11619 : maybe<a>
      = (match ((std/core/hnd/yielding())) {
        ((std/core/types/True() : bool ) as @pat@1: bool)
           -> std/core/hnd/yield-cont((forall<b> fn<<async,ndet,exn>>(cont: (b) -> <async,ndet,exn> maybe<a>, res: b){
            std/core/hnd/open-at1(i@11622, cont, res);
          }));
        ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
           -> y;
      });
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-extend((fn<<async,ndet,exn>>(@y-x10871: maybe<a>){
          (std/async/async/promise/@mlift-await@11390(p, @y-x10871));
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> (match (x@11619) {
          ((std/core/types/Just((v: a)) : maybe<a> ) as @pat@1@0: (maybe<a>))
             -> v;
          ((@skip std/core/types/Nothing() : maybe<a> ) as @pat@2: (maybe<a>))
             -> val i@0@11628 : (hnd/ev-index == 1 ssize_t)
                  = std/core/types/@make-ssize_t(0);
                val w@0 : hnd/evv<<async,exn,ndet>>
                  = std/core/hnd/evv-swap-create1(i@0@11628);
                val ev@11631 : hnd/ev<async>
                  = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
                val y@0 : error<a>
                  = (match (ev@11631) {
                    ((@skip std/core/hnd/Ev<e,b>((@pat@0@3: hnd/htag<async>), (m: hnd/marker<e,b>), (h: async<e,b>), (@pat@1@1: hnd/evv<e>)) : hnd/ev<async> ) as @pat@5: (hnd/ev<async>))
                       -> (match (h) {
                        ((@skip std/async/async/@Hnd-async((@pat@0@1: int), (@pat@1@2: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e,b>), (@pat@2@0: hnd/clause1<scope,(),async,e,b>), (@ctl-do-await: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,
   alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e,b>), (@pat@3@0: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<
   global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>
   >)>)>) ()),(),async,e,b>))) : async<e,b> ) as @pat@3: (async<e,b>))
                           -> (match (@ctl-do-await) {
                            ((@skip std/core/hnd/Clause1((f@1: (hnd/marker<e,b>, hnd/ev<async>, ((await-setup<a> == 4 (cb : (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global>
   == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool)) -> e error<a>)) : hnd/clause1<((await-setup<a> == 4 (cb : (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(
   st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<a>,async,e,b> ) as @pat@2@0@0: (hnd/clause1<((await-setup<a> == 4 (cb : (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet
   ,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<a>,async,e,b>))
                               -> f@1(m, ev@11631, (std/core/types/Tuple3((fn<(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>(cb: (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()){
                                    (match ((std/core/exn/exn/@handle((std/core/exn/@Hnd-exn(0, (forall<c> std/core/hnd/Clause1((fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(m@0: hnd/marker<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>,error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>>, @_wildcard-x653_16: hnd/ev<exn>, x@3: 
   exception){
                                          (std/core/hnd/yield-to-final(m@0, (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@_wildcard-x653_45: (hnd/resume-result<c,error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>>) -> <alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>> error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/
   console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>){
                                              (std/core/exn/Error(x@3));
                                            })));
                                        }))))), (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@res: error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>){
                                        @res;
                                      }), (fn<<exn,alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(){
                                        val w@1 : (hnd/evv<<alloc<global>,console/console,div,exn,fsys,ndet,net,read<global>,ui,write<global>>>)
                                          = (std/core/hnd/evv-swap-create0());
                                        val keep : ()
                                          = (std/core/hnd/evv-set(w@1));
                                        val x@6@11641 : ()
                                          = (match ((std/core/types/ref/(!)((match (p) {
                                              ((@skip std/async/async/Promise((@x: ref<global,promise-state<a>>)) : promise<a> ) as @pat@3@0@0@0: (promise<a>))
                                                 -> @x;
                                            }), std/core/types/@Hnodiv))) {
                                            ((std/async/async/Awaiting((listeners: list<(a) -> (io == 4 <exn,(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>) ()>)) : promise-state<a> ) as @pat@4@0: (promise-state<a>))
                                               -> std/core/types/set((match (p) {
                                                  ((@skip std/async/async/Promise((@x@0: ref<global,promise-state<a>>)) : promise<a> ) as @pat@3@0@0@0@0: (promise<a>))
                                                     -> @x@0;
                                                }), (std/async/async/Awaiting((std/core/types/Cons((fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>,exn>>(@x-x1@2: a){
                                                    val w@2 : (hnd/evv<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>,exn>>)
                                                      = (std/core/hnd/evv-swap-create0());
                                                    val x@7 : ()
                                                      = (cb((std/core/exn/Ok(@x-x1@2)), std/core/types/True));
                                                    val keep@0 : ()
                                                      = (std/core/hnd/evv-set(w@2));
                                                    x@7;
                                                  }), listeners)))));
                                            ((@skip std/async/async/Resolved((value: a)) : promise-state<a> ) as @pat@0@0@0@0: (promise-state<a>))
                                               -> val w@3 : hnd/evv<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>,exn>>
                                                    = std/core/hnd/evv-swap-create0();
                                                  val x@8 : ()
                                                    = cb((std/core/exn/Ok(value)), std/core/types/True);
                                                  val keep@1 : ()
                                                    = std/core/hnd/evv-set(w@3);
                                              x@8;
                                          });
                                        val x@4@11637 : (maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)
                                          = (match ((std/core/hnd/yielding())) {
                                            ((std/core/types/True() : bool ) as @pat@7: bool)
                                               -> std/core/hnd/yield-extend(std/async/async/promise/@mlift-await@11388);
                                            ((@skip std/core/types/False() : bool ) as @pat@0@5: bool)
                                               -> std/core/types/Nothing;
                                          });
                                        (match ((std/core/hnd/yielding())) {
                                          ((std/core/types/True() : bool ) as @pat@6: bool)
                                             -> std/core/hnd/yield-extend(std/async/async/promise/@mlift-await@11387);
                                          ((@skip std/core/types/False() : bool ) as @pat@0@4: bool)
                                             -> std/core/exn/Ok(x@4@11637);
                                        });
                                      })))) {
                                      ((std/core/exn/Ok((mcleanup: maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)) : error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>> ) as @pat@3@0@0: (error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()>>))
                                         -> mcleanup;
                                      ((@skip std/core/exn/Error(((@skip std/core/exn/Exception((@pat@1@1@0: string), (@pat@2@1: exception-info)) : exception ) as exn: exception)) : error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>> ) as @pat@0@0@0: (error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()
   >>))
                                         -> val _ : ()
                                                  = cb((std/core/exn/Error(exn)), std/core/types/True);
                                        std/core/types/Nothing;
                                    });
                                  }), std/async/async/empty-scope, std/core/types/True)));
                          });
                      });
                  });
                val _ : ()
                  = std/core/hnd/evv-set(w@0);
                val x@1@11625 : error<a>
                  = (match ((std/core/hnd/yielding())) {
                    ((std/core/types/True() : bool ) as @pat@4: bool)
                       -> std/core/hnd/yield-cont((forall<b> fn<<async,exn,ndet>>(cont@0: (b) -> <async,exn,ndet> error<a>, res@0: b){
                        std/core/hnd/open-at1(i@0@11628, cont@0, res@0);
                      }));
                    ((@skip std/core/types/False() : bool ) as @pat@0@2: bool)
                       -> y@0;
                  });
            (match ((std/core/hnd/yielding())) {
              ((std/core/types/True() : bool ) as @pat@3@1: bool)
                 -> std/core/hnd/yield-extend((fn<<async,exn,ndet>>(@y-x10877: error<a>){
                  (std/async/async/promise/@mlift-await@11389(@y-x10877));
                }));
              ((@skip std/core/types/False() : bool ) as @pat@0@1@0: bool)
                 -> val i@1@11647 : (hnd/ev-index == 1 ssize_t)
                      = std/core/types/@make-ssize_t(1);
                    val w@4 : hnd/evv<<exn,async,ndet>>
                      = std/core/hnd/evv-swap-create1(i@1@11647);
                    val y@1 : a
                      = (match (x@1@11625) {
                        ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@7: string), (@pat@1@0@0: exception-info)) : exception ) as exn@0: exception)) : error<a> ) as @pat@9: (error<a>))
                           -> val ev@0@11650 : hnd/ev<exn>
                                    = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
                          (match (ev@0@11650) {
                            ((@skip std/core/hnd/Ev<e,b>((@pat@0@8: hnd/htag<exn>), (m@1: hnd/marker<e,b>), (h@0: exn<e,b>), (@pat@1@2@0: hnd/evv<e>)) : hnd/ev<exn> ) as @pat@10: (hnd/ev<exn>))
                               -> (match ((std/core/exn/throw-exn/@select(h@0))) {
                                ((@skip std/core/hnd/Clause1((f@6: (hnd/marker<e,b>, hnd/ev<exn>, exception) -> e a)) : hnd/clause1<exception,a,exn,e,b> ) as @pat@2@2: (hnd/clause1<exception,a,exn,e,b>))
                                   -> f@6(m@1, ev@0@11650, exn@0);
                              });
                          });
                        ((@skip std/core/exn/Ok((x@11: a)) : error<a> ) as @pat@2@0@0@0: (error<a>))
                           -> x@11;
                      });
                    val _ : ()
                      = std/core/hnd/evv-set(w@4);
                (match ((std/core/hnd/yielding())) {
                  ((std/core/types/True() : bool ) as @pat@8: bool)
                     -> std/core/hnd/yield-cont((forall<b> fn<<exn,async,ndet>>(cont@1: (b) -> <exn,async,ndet> a, res@2: b){
                      std/core/hnd/open-at1(i@1@11647, cont@1, res@2);
                    }));
                  ((@skip std/core/types/False() : bool ) as @pat@0@6: bool)
                     -> y@1;
                });
            });
        });
    });
  };
// monadic lift
fun @mlift-lift-resolve@10756@11391 : forall<a> (@uniq-xx@10607 : list<(a) -> io ()>, value : a, wild : ()) -> io ()
  = forall<a> fn<io>(@uniq-xx@10607: list<(a) -> io ()>, value: a, wild: ()){
    std/async/async/@lift-resolve@10756(value, @uniq-xx@10607);
  };
// lifted local: @lift-resolve@10755, resolve, @spec-x10609
// specialized: std/core/list/@unroll-foreach@10016, on parameters @uniq-action@10604, using:
// @uniq-action@10604 = (fn<<(alloc :: H -> X)<(global :: H)>,(console/console :: X),(div :: X),(exn :: (E, V) -> V),(fsys :: X),(ndet :: X),(net :: X),(read :: H -> X)<(global :: H)>,(ui :: X),(write :: H -> X)<(global :: H)>>>(cbx: (4086) -> (io :: E) ()){
//   cbx(value);
// },Own)
fun @lift-resolve@10756 : forall<a> (value : a, @uniq-xs@10603 : list<(a) -> io ()>) -> <alloc<global>,console/console,div,exn,fsys,ndet,net,read<global>,ui,write<global>> ()
  = forall<a> fn<<alloc<global>,console/console,div,exn,fsys,ndet,net,read<global>,ui,write<global>>>(value@0: a, @uniq-xs@10603: list<(a) -> io ()>){
    (match (@uniq-xs@10603) {
      ((std/core/types/Cons((@uniq-x@10606: (a) -> (io == 4 <exn,(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>) ()), (@uniq-xx@10607@0: list<(a) -> (io == 4 <exn,(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>) ()>)) : list<(a) -> (io == 4 <exn,(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <
   read<global>,write<global>,alloc<global>>)>)>)>) ()> ) as @uniq-pat@10605: (list<(a) -> (io == 4 <exn,(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>) ()>))
         -> val x@11653 : ()
                  = @uniq-x@10606(value@0);
        (match ((std/core/hnd/yielding())) {
          ((std/core/types/True() : bool ) as @pat: bool)
             -> std/core/hnd/yield-extend((fn<(io == 4 <exn,(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>)>(wild@0: ()){
              (std/async/async/@mlift-lift-resolve@10756@11391(@uniq-xx@10607@0, value@0, wild@0));
            }));
          ((@skip std/core/types/False() : bool ) as @pat@0: bool)
             -> std/async/async/@lift-resolve@10756(value@0, @uniq-xx@10607@0);
        });
      ((@skip std/core/types/Nil() : list<(a) -> (io == 4 <exn,(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>) ()> ) as @uniq-pat@0@10608: (list<(a) -> (io == 4 <exn,(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>) ()>))
         -> std/core/types/Unit;
    });
  };
// lifted local: resolve, @spec-x10602
// specialized: std/core/list/foreach, on parameters @uniq-action@10599, using:
// @uniq-action@10599 = (fn<<(alloc :: H -> X)<(global :: H)>,(console/console :: X),(div :: X),(exn :: (E, V) -> V),(fsys :: X),(ndet :: X),(net :: X),(read :: H -> X)<(global :: H)>,(ui :: X),(write :: H -> X)<(global :: H)>>>(cbx: (4086) -> (io :: E) ()){
//   cbx(value);
// },Own)
fun @lift-resolve@10755 : forall<a> (value : a, @uniq-xs@10598 : list<(a) -> io ()>) -> <alloc<global>,console/console,div,exn,fsys,ndet,net,read<global>,ui,write<global>> ()
  = forall<a> fn<<alloc<global>,console/console,div,exn,fsys,ndet,net,read<global>,ui,write<global>>>(value: a, @uniq-xs@10598: list<(a) -> io ()>){
    (match (@uniq-xs@10598) {
      ((std/core/types/Nil() : list<(a) -> (io == 4 <exn,(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>) ()> ) as @uniq-pat@0@10600: (list<(a) -> (io == 4 <exn,(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>) ()>))
         -> std/core/types/Unit;
      (@uniq-pat@10601: (list<(a) -> (io == 4 <exn,(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>) ()>))
         -> std/async/async/@lift-resolve@10756(value, @uniq-xs@10598);
    });
  };
// monadic lift
fun @mlift-resolve@11392 : (@c-x10890 : ()) -> error<()>
  = fn(@c-x10890: ()){
    std/core/exn/Ok(@c-x10890);
  };
// monadic lift
fun @mlift-resolve@11393 : (@y-x10891 : error<()>) -> <async,ndet,exn> ()
  = fn<<async,ndet,exn>>(@y-x10891: error<()>){
    val i@11656 : hnd/ev-index
      = std/core/types/@make-ssize_t(1);
    val w : hnd/evv<<exn,async,ndet>>
      = std/core/hnd/evv-swap-create1(i@11656);
    val y : ()
      = match (@y-x10891) {
        ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@0: string), (@pat@1@0: exception-info)) : exception ) as exn@0: exception)) : error<()> ) as @pat@1: (error<()>))
           -> val ev@11659 : hnd/ev<exn>
                    = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
          (match (ev@11659) {
            ((@skip std/core/hnd/Ev<e,a>((@pat@0@1: hnd/htag<exn>), (m: hnd/marker<e,a>), (h: exn<e,a>), (@pat@1@1: hnd/evv<e>)) : hnd/ev<exn> ) as @pat@2: (hnd/ev<exn>))
               -> (match ((std/core/exn/throw-exn/@select(h))) {
                ((@skip std/core/hnd/Clause1((f@0: (hnd/marker<e,a>, hnd/ev<exn>, exception) -> e ())) : hnd/clause1<exception,(),exn,e,a> ) as @pat@2@0: (hnd/clause1<exception,(),exn,e,a>))
                   -> f@0(m, ev@11659, exn@0);
              });
          });
        ((@skip std/core/exn/Ok((x@1: ())) : error<()> ) as @pat@2@1: (error<()>))
           -> x@1;
      };
    val _ : ()
      = std/core/hnd/evv-set(w);
    match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-cont((forall<a> fn<<exn,async,ndet>>(cont: (a) -> <exn,async,ndet> (), res: a){
          std/core/hnd/open-at1(i@11656, cont, res);
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> y;
    };
  };
// Resolve a promise to `value`. Raises an exception if the promise was already resolved.
pub fun resolve : forall<a> (p : promise<a>, value : a) -> asyncx ()
  = forall<a> fn<asyncx>(p: promise<a>, value: a){
    val i@11665 : hnd/ev-index
      = std/core/types/@make-ssize_t(0);
    val w : hnd/evv<<async,ndet,exn>>
      = std/core/hnd/evv-swap-create1(i@11665);
    val ev@11668 : hnd/ev<async>
      = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
    val y : error<()>
      = (match (ev@11668) {
        ((@skip std/core/hnd/Ev<e,b>((@pat@0@1: hnd/htag<async>), (m: hnd/marker<e,b>), (h: async<e,b>), (@pat@1@0: hnd/evv<e>)) : hnd/ev<async> ) as @pat@2: (hnd/ev<async>))
           -> (match (h) {
            ((@skip std/async/async/@Hnd-async((@pat@0: int), (@ctl-async-iox: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e,b>), (@pat@1: hnd/clause1<scope,(),async,e,b>), (@pat@2@0: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)
   >)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e,b>), (@pat@3: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async
   ,e,b>))) : async<e,b> ) as @pat: (async<e,b>))
               -> (match (@ctl-async-iox) {
                ((@skip std/core/hnd/Clause1((f@1: (hnd/marker<e,b>, hnd/ev<async>, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) error<()>) -> e error<()>)) : hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) error<()>,error<()>,async,e,b> ) as @pat@2@0@0: (hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <
   ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) error<()>,error<()>,async,e,b>))
                   -> f@1(m, ev@11668, (fn<(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>(){
                      (std/core/exn/exn/@handle((std/core/exn/@Hnd-exn(0, (forall<c> std/core/hnd/Clause1((fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(m@0: hnd/marker<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>,error<()>>, @_wildcard-x653_16: hnd/ev<exn>, x@2: exception){
                            (std/core/hnd/yield-to-final(m@0, (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@_wildcard-x653_45: (hnd/resume-result<c,error<()>>) -> <alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>> error<()>){
                                (std/core/exn/Error(x@2));
                              })));
                          }))))), (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@res: error<()>){
                          @res;
                        }), (fn<<exn,alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(){
                          val w@0 : (hnd/evv<<alloc<global>,console/console,div,exn,fsys,ndet,net,read<global>,ui,write<global>>>)
                            = (std/core/hnd/evv-swap-create0());
                          val keep : ()
                            = (std/core/hnd/evv-set(w@0));
                          val x@4@11674 : ()
                            = (match ((std/core/types/ref/(!)((match (p) {
                                ((@skip std/async/async/Promise((@x: ref<global,promise-state<a>>)) : promise<a> ) as @pat@3@0: (promise<a>))
                                   -> @x;
                              }), std/core/types/@Hdiv))) {
                              ((std/async/async/Awaiting((listeners: list<(a) -> (io == 4 <exn,(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>) ()>)) : promise-state<a> ) as @pat@4@0: (promise-state<a>))
                                 -> val _ : ()
                                          = std/core/types/set((match (p) {
                                              ((@skip std/async/async/Promise((@x@0: ref<global,promise-state<a>>)) : promise<a> ) as @pat@3@0@0: (promise<a>))
                                                 -> @x@0;
                                            }), (std/async/async/Resolved(value)));
                                std/async/async/@lift-resolve@10755(value, listeners);
                              (@pat@0@0@0: (promise-state<a>))
                                 -> val ev@0@11676 : hnd/ev<exn>
                                          = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
                                (match (ev@0@11676) {
                                  ((@skip std/core/hnd/Ev<e,b>((@pat@0@3: hnd/htag<exn>), (m@1: hnd/marker<e,b>), (h@0: exn<e,b>), (@pat@1@1: hnd/evv<e>)) : hnd/ev<exn> ) as @pat@5: (hnd/ev<exn>))
                                     -> (match ((std/core/exn/throw-exn/@select(h@0))) {
                                      ((@skip std/core/hnd/Clause1((f@3: (hnd/marker<e,b>, hnd/ev<exn>, exception) -> e ())) : hnd/clause1<exception,(),exn,e,b> ) as @pat@2@1: (hnd/clause1<exception,(),exn,e,b>))
                                         -> f@3(m@1, ev@0@11676, (std/core/exn/Exception("Promise was already resolved", (match (std/core/types/@None) {
                                              ((std/core/types/@Optional((@uniq-info@399: exception-info)) : ? exception-info ) as @pat@5@0: ? exception-info)
                                                 -> @uniq-info@399;
                                              ((@skip std/core/types/@None() : ? exception-info ) as @pat@0@1@0: ? exception-info)
                                                 -> std/core/exn/ExnError;
                                            }))));
                                    });
                                });
                            });
                          (match ((std/core/hnd/yielding())) {
                            ((std/core/types/True() : bool ) as @pat@4: bool)
                               -> std/core/hnd/yield-extend(std/async/async/@mlift-resolve@11392);
                            ((@skip std/core/types/False() : bool ) as @pat@0@2: bool)
                               -> std/core/exn/Ok(x@4@11674);
                          });
                        })));
                    }));
              });
          });
      });
    val _ : ()
      = std/core/hnd/evv-set(w);
    val x@11662 : error<()>
      = (match ((std/core/hnd/yielding())) {
        ((std/core/types/True() : bool ) as @pat@1@2: bool)
           -> std/core/hnd/yield-cont((forall<b> fn<<async,ndet,exn>>(cont: (b) -> <async,ndet,exn> error<()>, res: b){
            std/core/hnd/open-at1(i@11665, cont, res);
          }));
        ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
           -> y;
      });
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat@6: bool)
         -> std/core/hnd/yield-extend(std/async/async/@mlift-resolve@11393);
      ((@skip std/core/types/False() : bool ) as @pat@0@4: bool)
         -> val i@0@11679 : (hnd/ev-index == 1 ssize_t)
              = std/core/types/@make-ssize_t(1);
            val w@1 : hnd/evv<<exn,async,ndet>>
              = std/core/hnd/evv-swap-create1(i@0@11679);
            val y@0 : ()
              = (match (x@11662) {
                ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@5: string), (@pat@1@2@0: exception-info)) : exception ) as exn@0: exception)) : error<()> ) as @pat@7: (error<()>))
                   -> val ev@1@11682 : hnd/ev<exn>
                            = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
                  (match (ev@1@11682) {
                    ((@skip std/core/hnd/Ev<e,b>((@pat@0@6: hnd/htag<exn>), (m@2: hnd/marker<e,b>), (h@1: exn<e,b>), (@pat@1@3: hnd/evv<e>)) : hnd/ev<exn> ) as @pat@8: (hnd/ev<exn>))
                       -> (match ((std/core/exn/throw-exn/@select(h@1))) {
                        ((@skip std/core/hnd/Clause1((f@5: (hnd/marker<e,b>, hnd/ev<exn>, exception) -> e ())) : hnd/clause1<exception,(),exn,e,b> ) as @pat@2@2: (hnd/clause1<exception,(),exn,e,b>))
                           -> f@5(m@2, ev@1@11682, exn@0);
                      });
                  });
                ((@skip std/core/exn/Ok((x@8: ())) : error<()> ) as @pat@2@3: (error<()>))
                   -> x@8;
              });
            val _ : ()
              = std/core/hnd/evv-set(w@1);
        (match ((std/core/hnd/yielding())) {
          ((std/core/types/True() : bool ) as @pat@6@0: bool)
             -> std/core/hnd/yield-cont((forall<b> fn<<exn,async,ndet>>(cont@0: (b) -> <exn,async,ndet> (), res@0: b){
              std/core/hnd/open-at1(i@0@11679, cont@0, res@0);
            }));
          ((@skip std/core/types/False() : bool ) as @pat@0@4@0: bool)
             -> y@0;
        });
    });
  };
// Automatically generated. Tests for the `Empty` constructor of the `:channel-state` type.
fip fun is-empty : forall<a> (^ channel-state : channel-state<a>) -> bool
  = forall<a> fn(channel-state: channel-state<a>){
    (match (channel-state) {
      ((std/async/async/Empty() : channel-state<a> ) as @pat: (channel-state<a>))
         -> std/core/types/True;
      (@pat@0: (channel-state<a>))
         -> std/core/types/False;
    });
  };
// Automatically generated. Tests for the `Values` constructor of the `:channel-state` type.
fip fun is-values : forall<a> (^ channel-state : channel-state<a>) -> bool
  = forall<a> fn(channel-state: channel-state<a>){
    (match (channel-state) {
      ((std/async/async/Values((@pat@0: a), (@pat@1: list<a>)) : channel-state<a> ) as @pat: (channel-state<a>))
         -> std/core/types/True;
      (@pat@2: (channel-state<a>))
         -> std/core/types/False;
    });
  };
// Automatically generated. Tests for the `Waiting` constructor of the `:channel-state` type.
fip fun is-waiting : forall<a> (^ channel-state : channel-state<a>) -> bool
  = forall<a> fn(channel-state: channel-state<a>){
    (match (channel-state) {
      ((std/async/async/Waiting((@pat@0: (a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()), (@pat@1: list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)) : channel-state<a> ) as @pat: (channel-state<a>))
         -> std/core/types/True;
      (@pat@2: (channel-state<a>))
         -> std/core/types/False;
    });
  };
fun from-values : forall<a> (values : list<a>) -> channel-state<a>
  = forall<a> fn(values: list<a>){
    (match (values) {
      ((std/core/types/Nil() : list<a> ) as @pat: (list<a>))
         -> std/async/async/Empty;
      ((@skip std/core/types/Cons((v: a), (vs: list<a>)) : list<a> ) as @pat@0: (list<a>))
         -> std/async/async/Values(v, vs);
    });
  };
fun from-waiting : forall<a> (listeners : list<(a) -> io-noexn ()>) -> channel-state<a>
  = forall<a> fn(listeners: list<(a) -> io-noexn ()>){
    (match (listeners) {
      ((std/core/types/Nil() : list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()> ) as @pat: (list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>))
         -> std/async/async/Empty;
      ((@skip std/core/types/Cons((l: (a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()), (ls: list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)) : list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()> ) as @pat@0: (list
   <(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>))
         -> std/async/async/Waiting(l, ls);
    });
  };
// Create a new asynchronous channel.
pub fun channel : forall<a> () -> async channel<a>
  = forall<a> fn<async>(){
    val ev@11685 : hnd/ev<async>
          = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
    (match (ev@11685) {
      ((@skip std/core/hnd/Ev<e,b>((@pat@0: hnd/htag<async>), (m: hnd/marker<e,b>), (h: async<e,b>), (@pat@1: hnd/evv<e>)) : hnd/ev<async> ) as @pat: (hnd/ev<async>))
         -> (match (h) {
          ((@skip std/async/async/@Hnd-async((@pat@0@0: int), (@ctl-async-iox: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e,b>), (@pat@1@0: hnd/clause1<scope,(),async,e,b>), (@pat@2@0: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>
   >)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e,b>), (@pat@3: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async
   ,e,b>))) : async<e,b> ) as @pat@2: (async<e,b>))
             -> (match (@ctl-async-iox) {
              ((@skip std/core/hnd/Clause1((f: (hnd/marker<e,b>, hnd/ev<async>, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) channel<a>) -> e channel<a>)) : hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) channel<a>,channel<a>,async,e,b> ) as @pat@2@1: (hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet
   ,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) channel<a>,channel<a>,async,e,b>))
                 -> f(m, ev@11685, (fn<(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>(){
                    val u : int
                      = (std/core/types/ref/(!)(std/core/unique-count, std/core/types/@Hnodiv));
                    val _ : ()
                      = (std/core/types/set(std/core/unique-count, (std/core/int/int-add(u, 1))));
                    (std/async/async/Channel(u, (std/core/types/ref(std/async/async/Empty))));
                  }));
            });
        });
    });
  };
// Return immediately if a value is available on the channel and otherwise returns `Nothing`.
pub fun try-receive : forall<a> (ch : channel<a>) -> <async,ndet> maybe<a>
  = forall<a> fn<<async,ndet>>(ch: channel<a>){
    val ev@11688 : hnd/ev<async>
          = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
    (match (ev@11688) {
      ((@skip std/core/hnd/Ev<e,b>((@pat@0: hnd/htag<async>), (m: hnd/marker<e,b>), (h: async<e,b>), (@pat@1: hnd/evv<e>)) : hnd/ev<async> ) as @pat: (hnd/ev<async>))
         -> (match (h) {
          ((@skip std/async/async/@Hnd-async((@pat@0@0: int), (@ctl-async-iox: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e,b>), (@pat@1@0: hnd/clause1<scope,(),async,e,b>), (@pat@2@0: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>
   >)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e,b>), (@pat@3: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async
   ,e,b>))) : async<e,b> ) as @pat@2: (async<e,b>))
             -> (match (@ctl-async-iox) {
              ((@skip std/core/hnd/Clause1((f: (hnd/marker<e,b>, hnd/ev<async>, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<a>) -> e maybe<a>)) : hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<a>,maybe<a>,async,e,b> ) as @pat@2@1: (hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console
   /console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<a>,maybe<a>,async,e,b>))
                 -> f(m, ev@11688, (fn<(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>(){
                    (match ((std/core/types/ref/(!)((match (ch) {
                        ((@skip std/async/async/Channel((@pat@0@0@0: int), (@x: ref<global,channel-state<a>>)) : channel<a> ) as @pat@3@0: (channel<a>))
                           -> @x;
                      }), std/core/types/@Hdiv))) {
                      ((std/async/async/Values((v: a), (vs: list<a>)) : channel-state<a> ) as @pat@1@0@0: (channel-state<a>))
                         -> val _ : ()
                                  = std/core/types/set((match (ch) {
                                      ((@skip std/async/async/Channel((@pat@0@0@0@0: int), (@x@0: ref<global,channel-state<a>>)) : channel<a> ) as @pat@2@0@0: (channel<a>))
                                         -> @x@0;
                                    }), (match (vs) {
                                      ((std/core/types/Nil() : list<a> ) as @pat@2@0@0@0: (list<a>))
                                         -> std/async/async/Empty;
                                      ((@skip std/core/types/Cons((v@0: a), (vs@0: list<a>)) : list<a> ) as @pat@0@0@0@0@0: (list<a>))
                                         -> std/async/async/Values(v@0, vs@0);
                                    }));
                        std/core/types/Just(v);
                      (@pat@0@0@0@0@0@0: (channel-state<a>))
                         -> std/core/types/Nothing;
                    });
                  }));
            });
        });
    });
  };
// monadic lift
fun @mlift-receivex@11394 : forall<a> (cancelable@0 : ? bool, ch : channel<a>, @y-x10895 : maybe<a>) -> <async,ndet> error<a>
  = forall<a> fn<<async,ndet>>(cancelable@0: ? bool, ch: channel<a>, @y-x10895: maybe<a>){
    (match (@y-x10895) {
      ((std/core/types/Just((v@0: a)) : maybe<a> ) as @pat@4: (maybe<a>))
         -> std/core/exn/Ok(v@0);
      ((@skip std/core/types/Nothing() : maybe<a> ) as @pat@5: (maybe<a>))
         -> val ev@11691 : hnd/ev<async>
                  = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
        (match (ev@11691) {
          ((@skip std/core/hnd/Ev<e,b>((@pat@0: hnd/htag<async>), (m: hnd/marker<e,b>), (h: async<e,b>), (@pat@1: hnd/evv<e>)) : hnd/ev<async> ) as @pat: (hnd/ev<async>))
             -> (match (h) {
              ((@skip std/async/async/@Hnd-async((@pat@0@0: int), (@pat@1@0: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e,b>), (@pat@2@0: hnd/clause1<scope,(),async,e,b>), (@ctl-do-await: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<
   global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e,b>), (@pat@3: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 
   <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),()
   ,async,e,b>))) : async<e,b> ) as @pat@2: (async<e,b>))
                 -> (match (@ctl-do-await) {
                  ((@skip std/core/hnd/Clause1((f: (hnd/marker<e,b>, hnd/ev<async>, ((await-setup<a> == 4 (cb : (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()>), scope, bool)) -> e error<a>)) : hnd/clause1<((await-setup<a> == 4 (cb : (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global>
   == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<a>,async,e,b> ) as @pat@2@1: (hnd/clause1<((await-setup<a> == 4 (cb : (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/
   console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<a>,async,e,b>))
                     -> f(m, ev@11691, (std/core/types/Tuple3((fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(cb: (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()){
                          val cbr : ((x : a) -> <alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>> ())
                            = (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(x: a){
                              (cb((std/core/exn/Ok(x)), std/core/types/True));
                            });
                          val _@0 : ()
                            = (match ((std/core/types/ref/(!)((match (ch) {
                                ((@skip std/async/async/Channel((@pat@0@0@0: int), (@x: ref<global,channel-state<a>>)) : channel<a> ) as @pat@3@0: (channel<a>))
                                   -> @x;
                              }), std/core/types/@Hnodiv))) {
                              ((std/async/async/Empty() : channel-state<a> ) as @pat@1@0@0: (channel-state<a>))
                                 -> std/core/types/set((match (ch) {
                                    ((@skip std/async/async/Channel((@pat@0@0@0@0: int), (@x@0: ref<global,channel-state<a>>)) : channel<a> ) as @pat@2@0@0: (channel<a>))
                                       -> @x@0;
                                  }), (std/async/async/Waiting(cbr, std/core/types/Nil)));
                              ((std/async/async/Waiting((l: (a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()), (ls: list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)) : channel-state<a> ) as @pat@2@0@0@0: (channel-state<a>))
                                 -> val ys@10083 : list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>
                                      = std/core/types/Cons(cbr, std/core/types/Nil);
                                    val listeners@0@10081 : ? (list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)
                                      = std/core/types/@Optional((match (ls) {
                                        ((std/core/types/Nil() : list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()> ) as @pat@0@2: (list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>))
                                           -> ys@10083;
                                        (@pat@6: (list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>))
                                           -> std/core/list/@unroll-append@10004(ls, ys@10083);
                                      }));
                                std/core/types/set((match (ch) {
                                    ((@skip std/async/async/Channel((@pat@0@1: int), (@x@1: ref<global,channel-state<a>>)) : channel<a> ) as @pat@3@0@0: (channel<a>))
                                       -> @x@1;
                                  }), (std/async/async/Waiting(l, (match (listeners@0@10081) {
                                      ((std/core/types/@Optional((@uniq-listeners@994@0: list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)) : ? (list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>) ) as @pat@3@0@0@0: ? (list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global>
   == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>))
                                         -> @uniq-listeners@994@0;
                                      ((@skip std/core/types/@None() : ? (list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>) ) as @pat@0@1@0: ? (list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>))
                                         -> std/core/types/Nil;
                                    }))));
                              ((@skip std/async/async/Values((v: a), (vs: list<a>)) : channel-state<a> ) as @pat@3@0@0@0@0: (channel-state<a>))
                                 -> val _ : ()
                                          = std/core/types/set((match (ch) {
                                              ((@skip std/async/async/Channel((@pat@0@3: int), (@x@2: ref<global,channel-state<a>>)) : channel<a> ) as @pat@7: (channel<a>))
                                                 -> @x@2;
                                            }), (match (vs) {
                                              ((std/core/types/Nil() : list<a> ) as @pat@7@0: (list<a>))
                                                 -> std/async/async/Empty;
                                              ((@skip std/core/types/Cons((v@1: a), (vs@0: list<a>)) : list<a> ) as @pat@0@0@0@0@0: (list<a>))
                                                 -> std/async/async/Values(v@1, vs@0);
                                            }));
                                cbr(v);
                            });
                          std/core/types/Nothing;
                        }), std/async/async/empty-scope, (match (cancelable@0) {
                          ((std/core/types/@Optional((@uniq-cancelable@4377: bool)) : ? bool ) as @pat@7@0@0: ? bool)
                             -> @uniq-cancelable@4377;
                          ((@skip std/core/types/@None() : ? bool ) as @pat@0@3@0: ? bool)
                             -> std/core/types/True;
                        }))));
                });
            });
        });
    });
  };
fun receivex : forall<a> (ch : channel<a>, cancelable : ? bool) -> <async,ndet> error<a>
  = forall<a> fn<<async,ndet>>(ch: channel<a>, cancelable@0: ? bool){
    val x@11696 : maybe<a>
          = std/async/async/try-receive(ch);
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-extend((fn<<async,ndet>>(@y-x10895: maybe<a>){
          (std/async/async/@mlift-receivex@11394(cancelable@0, ch, @y-x10895));
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> (match (x@11696) {
          ((std/core/types/Just((v@0: a)) : maybe<a> ) as @pat@4: (maybe<a>))
             -> std/core/exn/Ok(v@0);
          ((@skip std/core/types/Nothing() : maybe<a> ) as @pat@5: (maybe<a>))
             -> val ev@11699 : hnd/ev<async>
                      = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
            (match (ev@11699) {
              ((@skip std/core/hnd/Ev<e,b>((@pat@0@0: hnd/htag<async>), (m: hnd/marker<e,b>), (h: async<e,b>), (@pat@1@0: hnd/evv<e>)) : hnd/ev<async> ) as @pat@1: (hnd/ev<async>))
                 -> (match (h) {
                  ((@skip std/async/async/@Hnd-async((@pat@0@1: int), (@pat@1@1: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e,b>), (@pat@2@0: hnd/clause1<scope,(),async,e,b>), (@ctl-do-await: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<
   global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e,b>), (@pat@3: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 
   <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),()
   ,async,e,b>))) : async<e,b> ) as @pat@2: (async<e,b>))
                     -> (match (@ctl-do-await) {
                      ((@skip std/core/hnd/Clause1((f: (hnd/marker<e,b>, hnd/ev<async>, ((await-setup<a> == 4 (cb : (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <
   read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool)) -> e error<a>)) : hnd/clause1<((await-setup<a> == 4 (cb : (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<
   global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<a>,async,e,b> ) as @pat@2@1: (hnd/clause1<((await-setup<a> == 4 (cb : (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,
   console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<a>,async,e,b>))
                         -> f(m, ev@11699, (std/core/types/Tuple3((fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(cb: (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()){
                              val cbr : ((x : a) -> <alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>> ())
                                = (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(x@0: a){
                                  (cb((std/core/exn/Ok(x@0)), std/core/types/True));
                                });
                              val _@0 : ()
                                = (match ((std/core/types/ref/(!)((match (ch) {
                                    ((@skip std/async/async/Channel((@pat@0@1@0: int), (@x: ref<global,channel-state<a>>)) : channel<a> ) as @pat@3@0: (channel<a>))
                                       -> @x;
                                  }), std/core/types/@Hnodiv))) {
                                  ((std/async/async/Empty() : channel-state<a> ) as @pat@1@1@0: (channel-state<a>))
                                     -> std/core/types/set((match (ch) {
                                        ((@skip std/async/async/Channel((@pat@0@0@0: int), (@x@0: ref<global,channel-state<a>>)) : channel<a> ) as @pat@2@0@0: (channel<a>))
                                           -> @x@0;
                                      }), (std/async/async/Waiting(cbr, std/core/types/Nil)));
                                  ((std/async/async/Waiting((l: (a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()), (ls: list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)) : channel-state<a> ) as @pat@2@0@0@0: (channel-state<a>))
                                     -> val ys@10083 : list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>
                                          = std/core/types/Cons(cbr, std/core/types/Nil);
                                        val listeners@0@10081 : ? (list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)
                                          = std/core/types/@Optional((match (ls) {
                                            ((std/core/types/Nil() : list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()> ) as @pat@0@2: (list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>))
                                               -> ys@10083;
                                            (@pat@6: (list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>))
                                               -> std/core/list/@unroll-append@10004(ls, ys@10083);
                                          }));
                                    std/core/types/set((match (ch) {
                                        ((@skip std/async/async/Channel((@pat@0@1@0@0: int), (@x@1: ref<global,channel-state<a>>)) : channel<a> ) as @pat@3@0@0: (channel<a>))
                                           -> @x@1;
                                      }), (std/async/async/Waiting(l, (match (listeners@0@10081) {
                                          ((std/core/types/@Optional((@uniq-listeners@994@0: list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)) : ? (list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>) ) as @pat@3@0@0@0: ? (list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<
   global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>))
                                             -> @uniq-listeners@994@0;
                                          ((@skip std/core/types/@None() : ? (list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>) ) as @pat@0@1@0@0@0: ? (list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>))
                                             -> std/core/types/Nil;
                                        }))));
                                  ((@skip std/async/async/Values((v: a), (vs: list<a>)) : channel-state<a> ) as @pat@3@0@0@0@0: (channel-state<a>))
                                     -> val _ : ()
                                              = std/core/types/set((match (ch) {
                                                  ((@skip std/async/async/Channel((@pat@0@3: int), (@x@2: ref<global,channel-state<a>>)) : channel<a> ) as @pat@7: (channel<a>))
                                                     -> @x@2;
                                                }), (match (vs) {
                                                  ((std/core/types/Nil() : list<a> ) as @pat@7@0: (list<a>))
                                                     -> std/async/async/Empty;
                                                  ((@skip std/core/types/Cons((v@1: a), (vs@0: list<a>)) : list<a> ) as @pat@0@0@0@0: (list<a>))
                                                     -> std/async/async/Values(v@1, vs@0);
                                                }));
                                    cbr(v);
                                });
                              std/core/types/Nothing;
                            }), std/async/async/empty-scope, (match (cancelable@0) {
                              ((std/core/types/@Optional((@uniq-cancelable@4377: bool)) : ? bool ) as @pat@7@0@0: ? bool)
                                 -> @uniq-cancelable@4377;
                              ((@skip std/core/types/@None() : ? bool ) as @pat@0@3@0: ? bool)
                                 -> std/core/types/True;
                            }))));
                    });
                });
            });
        });
    });
  };
// monadic lift
fun @mlift-receive@11395 : forall<a> (@y-x10900 : error<a>) -> <async,ndet,exn> a
  = forall<a> fn<<async,ndet,exn>>(@y-x10900: error<a>){
    val i@11704 : hnd/ev-index
      = std/core/types/@make-ssize_t(1);
    val w : hnd/evv<<exn,async,ndet>>
      = std/core/hnd/evv-swap-create1(i@11704);
    val y : a
      = (match (@y-x10900) {
        ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@0: string), (@pat@1@0: exception-info)) : exception ) as exn@0: exception)) : error<a> ) as @pat@1: (error<a>))
           -> val ev@11707 : hnd/ev<exn>
                    = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
          (match (ev@11707) {
            ((@skip std/core/hnd/Ev<e,b>((@pat@0@1: hnd/htag<exn>), (m: hnd/marker<e,b>), (h: exn<e,b>), (@pat@1@1: hnd/evv<e>)) : hnd/ev<exn> ) as @pat@2: (hnd/ev<exn>))
               -> (match ((std/core/exn/throw-exn/@select(h))) {
                ((@skip std/core/hnd/Clause1((f@0: (hnd/marker<e,b>, hnd/ev<exn>, exception) -> e a)) : hnd/clause1<exception,a,exn,e,b> ) as @pat@2@0: (hnd/clause1<exception,a,exn,e,b>))
                   -> f@0(m, ev@11707, exn@0);
              });
          });
        ((@skip std/core/exn/Ok((x@1: a)) : error<a> ) as @pat@2@1: (error<a>))
           -> x@1;
      });
    val _ : ()
      = std/core/hnd/evv-set(w);
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-cont((forall<b> fn<<exn,async,ndet>>(cont: (b) -> <exn,async,ndet> a, res: b){
          std/core/hnd/open-at1(i@11704, cont, res);
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> y;
    });
  };
// Receive (and remove) a value from the channel: returns immediately if a value is available and otherwise
// waits asynchronously until a value becomes available.
pub fun receive : forall<a> (ch : channel<a>) -> asyncx a
  = forall<a> fn<asyncx>(ch: channel<a>){
    val i@11713 : hnd/ev-index
      = std/core/types/@make-ssize_t(0);
    val w : hnd/evv<<async,ndet,exn>>
      = std/core/hnd/evv-swap-create1(i@11713);
    val y : error<a>
      = std/async/async/receivex(ch, std/core/types/@None);
    val _ : ()
      = std/core/hnd/evv-set(w);
    val x@11710 : error<a>
      = (match ((std/core/hnd/yielding())) {
        ((std/core/types/True() : bool ) as @pat@1: bool)
           -> std/core/hnd/yield-cont((forall<b> fn<<async,ndet,exn>>(cont: (b) -> <async,ndet,exn> error<a>, res: b){
            std/core/hnd/open-at1(i@11713, cont, res);
          }));
        ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
           -> y;
      });
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-extend((fn<<async,ndet,exn>>(@y-x10900: error<a>){
          (std/async/async/@mlift-receive@11395(@y-x10900));
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> val i@0@11717 : (hnd/ev-index == 1 ssize_t)
              = std/core/types/@make-ssize_t(1);
            val w@0 : hnd/evv<<exn,async,ndet>>
              = std/core/hnd/evv-swap-create1(i@0@11717);
            val y@0 : a
              = (match (x@11710) {
                ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@2: string), (@pat@1@0: exception-info)) : exception ) as exn@0: exception)) : error<a> ) as @pat@3: (error<a>))
                   -> val ev@11720 : hnd/ev<exn>
                            = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
                  (match (ev@11720) {
                    ((@skip std/core/hnd/Ev<e,b>((@pat@0@3: hnd/htag<exn>), (m: hnd/marker<e,b>), (h: exn<e,b>), (@pat@1@1: hnd/evv<e>)) : hnd/ev<exn> ) as @pat@4: (hnd/ev<exn>))
                       -> (match ((std/core/exn/throw-exn/@select(h))) {
                        ((@skip std/core/hnd/Clause1((f@1: (hnd/marker<e,b>, hnd/ev<exn>, exception) -> e a)) : hnd/clause1<exception,a,exn,e,b> ) as @pat@2@0: (hnd/clause1<exception,a,exn,e,b>))
                           -> f@1(m, ev@11720, exn@0);
                      });
                  });
                ((@skip std/core/exn/Ok((x@2: a)) : error<a> ) as @pat@2@1: (error<a>))
                   -> x@2;
              });
            val _ : ()
              = std/core/hnd/evv-set(w@0);
        (match ((std/core/hnd/yielding())) {
          ((std/core/types/True() : bool ) as @pat@2: bool)
             -> std/core/hnd/yield-cont((forall<b> fn<<exn,async,ndet>>(cont@0: (b) -> <exn,async,ndet> a, res@0: b){
              std/core/hnd/open-at1(i@0@11717, cont@0, res@0);
            }));
          ((@skip std/core/types/False() : bool ) as @pat@0@1: bool)
             -> y@0;
        });
    });
  };
fun emit-io : forall<a> (ch : channel<a>, value : a) -> io-noexn ()
  = forall<a> fn<io-noexn>(ch: channel<a>, value: a){
    (match ((std/core/types/ref/(!)((match (ch) {
        ((@skip std/async/async/Channel((@pat@0: int), (@x: ref<global,channel-state<a>>)) : channel<a> ) as @pat: (channel<a>))
           -> @x;
      }), std/core/types/@Hdiv))) {
      ((std/async/async/Empty() : channel-state<a> ) as @pat@1: (channel-state<a>))
         -> std/core/types/set((match (ch) {
            ((@skip std/async/async/Channel((@pat@0@0: int), (@x@0: ref<global,channel-state<a>>)) : channel<a> ) as @pat@2: (channel<a>))
               -> @x@0;
          }), (std/async/async/Values(value, std/core/types/Nil)));
      ((std/async/async/Values((v: a), (vs: list<a>)) : channel-state<a> ) as @pat@0@1: (channel-state<a>))
         -> val ys@10090 : list<a>
              = std/core/types/Cons(value, std/core/types/Nil);
            val values@0@10088 : ? (list<a>)
              = std/core/types/@Optional((match (vs) {
                ((std/core/types/Nil() : list<a> ) as @pat@0@3: (list<a>))
                   -> ys@10090;
                (@pat@4: (list<a>))
                   -> std/core/list/@unroll-append@10004(vs, ys@10090);
              }));
        std/core/types/set((match (ch) {
            ((@skip std/async/async/Channel((@pat@0@2: int), (@x@1: ref<global,channel-state<a>>)) : channel<a> ) as @pat@3: (channel<a>))
               -> @x@1;
          }), (std/async/async/Values(v, (match (values@0@10088) {
              ((std/core/types/@Optional((@uniq-values@967@0: list<a>)) : ? (list<a>) ) as @pat@3@0: ? (list<a>))
                 -> @uniq-values@967@0;
              ((@skip std/core/types/@None() : ? (list<a>) ) as @pat@0@2@0: ? (list<a>))
                 -> std/core/types/Nil;
            }))));
      ((@skip std/async/async/Waiting((l: (a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()), (ls: list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)) : channel-state<a> ) as @pat@1@0: (channel-state<a>))
         -> val _ : ()
                  = std/core/types/set((match (ch) {
                      ((@skip std/async/async/Channel((@pat@0@4: int), (@x@2: ref<global,channel-state<a>>)) : channel<a> ) as @pat@5: (channel<a>))
                         -> @x@2;
                    }), (match (ls) {
                      ((std/core/types/Nil() : list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()> ) as @pat@5@0: (list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>))
                         -> std/async/async/Empty;
                      ((@skip std/core/types/Cons((l@0: (a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()), (ls@0: list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)) : list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()
   > ) as @pat@0@0@0: (list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>))
                         -> std/async/async/Waiting(l@0, ls@0);
                    }));
        l(value);
    });
  };
// monadic lift
fun @mlift-emit@11396 : (@y-x10905 : error<()>) -> <async,ndet,exn> ()
  = fn<<async,ndet,exn>>(@y-x10905: error<()>){
    val i@11723 : hnd/ev-index
      = std/core/types/@make-ssize_t(1);
    val w : hnd/evv<<exn,async,ndet>>
      = std/core/hnd/evv-swap-create1(i@11723);
    val y : ()
      = match (@y-x10905) {
        ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@0: string), (@pat@1@0: exception-info)) : exception ) as exn@0: exception)) : error<()> ) as @pat@1: (error<()>))
           -> val ev@11726 : hnd/ev<exn>
                    = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
          (match (ev@11726) {
            ((@skip std/core/hnd/Ev<e,a>((@pat@0@1: hnd/htag<exn>), (m: hnd/marker<e,a>), (h: exn<e,a>), (@pat@1@1: hnd/evv<e>)) : hnd/ev<exn> ) as @pat@2: (hnd/ev<exn>))
               -> (match ((std/core/exn/throw-exn/@select(h))) {
                ((@skip std/core/hnd/Clause1((f@0: (hnd/marker<e,a>, hnd/ev<exn>, exception) -> e ())) : hnd/clause1<exception,(),exn,e,a> ) as @pat@2@0: (hnd/clause1<exception,(),exn,e,a>))
                   -> f@0(m, ev@11726, exn@0);
              });
          });
        ((@skip std/core/exn/Ok((x@1: ())) : error<()> ) as @pat@2@1: (error<()>))
           -> x@1;
      };
    val _ : ()
      = std/core/hnd/evv-set(w);
    match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-cont((forall<a> fn<<exn,async,ndet>>(cont: (a) -> <exn,async,ndet> (), res: a){
          std/core/hnd/open-at1(i@11723, cont, res);
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> y;
    };
  };
// Emit a value asynchronously into a channel.
pub fun emit : forall<a> (ch : channel<a>, value : a) -> asyncx ()
  = forall<a> fn<asyncx>(ch: channel<a>, value: a){
    val i@11732 : hnd/ev-index
      = std/core/types/@make-ssize_t(0);
    val w : hnd/evv<<async,ndet,exn>>
      = std/core/hnd/evv-swap-create1(i@11732);
    val ev@11735 : hnd/ev<async>
      = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
    val y : error<()>
      = (match (ev@11735) {
        ((@skip std/core/hnd/Ev<e,b>((@pat@0@1: hnd/htag<async>), (m: hnd/marker<e,b>), (h: async<e,b>), (@pat@1@0: hnd/evv<e>)) : hnd/ev<async> ) as @pat@2: (hnd/ev<async>))
           -> (match (h) {
            ((@skip std/async/async/@Hnd-async((@pat@0: int), (@ctl-async-iox: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e,b>), (@pat@1: hnd/clause1<scope,(),async,e,b>), (@pat@2@0: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)
   >)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e,b>), (@pat@3: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async
   ,e,b>))) : async<e,b> ) as @pat: (async<e,b>))
               -> (match (@ctl-async-iox) {
                ((@skip std/core/hnd/Clause1((f@1: (hnd/marker<e,b>, hnd/ev<async>, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) error<()>) -> e error<()>)) : hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) error<()>,error<()>,async,e,b> ) as @pat@2@0@0: (hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <
   ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) error<()>,error<()>,async,e,b>))
                   -> f@1(m, ev@11735, (fn<(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>(){
                      (std/core/exn/exn/@handle((std/core/exn/@Hnd-exn(0, (forall<c> std/core/hnd/Clause1((fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(m@0: hnd/marker<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>,error<()>>, @_wildcard-x653_16: hnd/ev<exn>, x@2: exception){
                            (std/core/hnd/yield-to-final(m@0, (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@_wildcard-x653_45: (hnd/resume-result<c,error<()>>) -> <alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>> error<()>){
                                (std/core/exn/Error(x@2));
                              })));
                          }))))), (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@res: error<()>){
                          @res;
                        }), (fn<<exn,alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(){
                          val w@0 : (hnd/evv<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>,exn>>)
                            = (std/core/hnd/evv-swap-create0());
                          val x@3 : ()
                            = (std/async/async/emit-io(ch, value));
                          val keep : ()
                            = (std/core/hnd/evv-set(w@0));
                          (std/core/exn/Ok(x@3));
                        })));
                    }));
              });
          });
      });
    val _ : ()
      = std/core/hnd/evv-set(w);
    val x@11729 : error<()>
      = (match ((std/core/hnd/yielding())) {
        ((std/core/types/True() : bool ) as @pat@1@1: bool)
           -> std/core/hnd/yield-cont((forall<b> fn<<async,ndet,exn>>(cont: (b) -> <async,ndet,exn> error<()>, res: b){
            std/core/hnd/open-at1(i@11732, cont, res);
          }));
        ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
           -> y;
      });
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat@4: bool)
         -> std/core/hnd/yield-extend(std/async/async/@mlift-emit@11396);
      ((@skip std/core/types/False() : bool ) as @pat@0@2: bool)
         -> val i@0@11742 : (hnd/ev-index == 1 ssize_t)
              = std/core/types/@make-ssize_t(1);
            val w@1 : hnd/evv<<exn,async,ndet>>
              = std/core/hnd/evv-swap-create1(i@0@11742);
            val y@0 : ()
              = (match (x@11729) {
                ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@3: string), (@pat@1@1@0: exception-info)) : exception ) as exn@0: exception)) : error<()> ) as @pat@4@0: (error<()>))
                   -> val ev@0@11745 : hnd/ev<exn>
                            = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
                  (match (ev@0@11745) {
                    ((@skip std/core/hnd/Ev<e,b>((@pat@0@4: hnd/htag<exn>), (m@1: hnd/marker<e,b>), (h@0: exn<e,b>), (@pat@1@2: hnd/evv<e>)) : hnd/ev<exn> ) as @pat@5: (hnd/ev<exn>))
                       -> (match ((std/core/exn/throw-exn/@select(h@0))) {
                        ((@skip std/core/hnd/Clause1((f@4: (hnd/marker<e,b>, hnd/ev<exn>, exception) -> e ())) : hnd/clause1<exception,(),exn,e,b> ) as @pat@2@1: (hnd/clause1<exception,(),exn,e,b>))
                           -> f@4(m@1, ev@0@11745, exn@0);
                      });
                  });
                ((@skip std/core/exn/Ok((x@6: ())) : error<()> ) as @pat@2@2: (error<()>))
                   -> x@6;
              });
            val _ : ()
              = std/core/hnd/evv-set(w@1);
        (match ((std/core/hnd/yielding())) {
          ((std/core/types/True() : bool ) as @pat@3@0: bool)
             -> std/core/hnd/yield-cont((forall<b> fn<<exn,async,ndet>>(cont@0: (b) -> <exn,async,ndet> (), res@0: b){
              std/core/hnd/open-at1(i@0@11742, cont@0, res@0);
            }));
          ((@skip std/core/types/False() : bool ) as @pat@0@2@0: bool)
             -> y@0;
        });
    });
  };
fun trace-anyx : forall<a> (s : string, x : a) -> async ()
  = forall<a> fn<async>(s: string, x: a){
    std/core/debug/trace-any(s, x);
  };
fun async/clear-timeout : (tid : timeout-id, ?clear-timeout : (any) -> <st<global>,console/console,div,fsys,ndet,net,ui> ()) -> <st<global>,console/console,div,fsys,ndet,net,ui> ()
  = fn<io-noexn>(tid: timeout-id, @implicit/clear-timeout: (any) -> io-noexn ()){
    ?clear-timeout((match (tid) {
      ((@skip std/async/async/Timeout-id((@x: any)) : timeout-id ) as @pat: timeout-id)
         -> @x;
    }));
  };
fun unleft : forall<a,b> (x : error<either<a,b>>) -> error<a>
  = forall<a,b> fn(x: error<either<a,b>>){
    (match (x) {
      ((std/core/exn/Ok(((std/core/types/Left((l: a)) : either<a,b> ) as @pat@0: either<a,b>)) : error<either<a,b>> ) as @pat: (error<either<a,b>>))
         -> std/core/exn/Ok(l);
      ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@2: string), (@pat@3: exception-info)) : exception ) as exn: exception)) : error<either<a,b>> ) as @pat@1: (error<either<a,b>>))
         -> std/core/exn/Error(exn);
      (@pat@4: (error<either<a,b>>))
         -> std/core/exn/Error((std/core/exn/Exception("invalid left interleaved result", (std/core/exn/ExnInternal("std/async/interleavedx(action1,action2)")))));
    });
  };
fun unright : forall<a,b> (x : error<either<a,b>>) -> error<b>
  = forall<a,b> fn(x: error<either<a,b>>){
    (match (x) {
      ((std/core/exn/Ok(((std/core/types/Right((r: b)) : either<a,b> ) as @pat@0: either<a,b>)) : error<either<a,b>> ) as @pat: (error<either<a,b>>))
         -> std/core/exn/Ok(r);
      ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@2: string), (@pat@3: exception-info)) : exception ) as exn: exception)) : error<either<a,b>> ) as @pat@1: (error<either<a,b>>))
         -> std/core/exn/Error(exn);
      (@pat@4: (error<either<a,b>>))
         -> std/core/exn/Error((std/core/exn/Exception("invalid right interleaved result", (std/core/exn/ExnInternal("std/async/interleavedx(action1,action2)")))));
    });
  };
// Are there still strands that need to be resumed?

// Call the `fun strands-are-busy` operation of the effect `:strands`
fun strands-are-busy : forall<a> () -> (strands<a>) bool
  = forall<a> fn<(strands<a>)>(){
    val ev@11748 : hnd/ev<strands<_b>>
          = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
    (match (ev@11748) {
      ((@skip std/core/hnd/Ev<e,b>((@pat@0: hnd/htag<strands<_5059>>), (m: hnd/marker<e,b>), (h: (strands<_5059>)<e,b>), (@pat@1: hnd/evv<e>)) : hnd/ev<strands<_c>> ) as @pat: (hnd/ev<strands<_5059>>))
         -> (match (h) {
          ((@skip std/async/async/@Hnd-strands((@pat@0@0: int), (@pat@1@0: hnd/clause2<int,error<_5059>,(),strands<_5059>,e,b>), (@fun-strands-are-busy: hnd/clause0<bool,strands<_5059>,e,b>)) : strands<_c,e,b> ) as @pat@2: (strands<_5059,e,b>))
             -> (match (@fun-strands-are-busy) {
              ((@skip std/core/hnd/Clause0((f: (hnd/marker<e,b>, hnd/ev<strands<_5059>>) -> e bool)) : hnd/clause0<bool,strands<_c>,e,b> ) as @pat@2@0: (hnd/clause0<bool,strands<_5059>,e,b>))
                 -> f(m, ev@11748);
            });
        });
    });
  };
// Call this when a strand is done.

// Call the `fun strand-done` operation of the effect `:strands`
fun strand-done : forall<a> (idx : int, result : error<a>) -> (strands<a>) ()
  = forall<a> fn<(strands<a>)>(idx: int, result: error<a>){
    val evx@11750 : hnd/ev<strands<a>>
          = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
    (match (evx@11750) {
      ((@skip std/core/hnd/Ev<e,b>((@pat@0: hnd/htag<strands<a>>), (m: hnd/marker<e,b>), (h: (strands<a>)<e,b>), (@pat@1: hnd/evv<e>)) : hnd/ev<strands<a>> ) as @pat: (hnd/ev<strands<a>>))
         -> (match (h) {
          ((@skip std/async/async/@Hnd-strands((@pat@0@0: int), (@fun-strand-done: hnd/clause2<int,error<a>,(),strands<a>,e,b>), (@pat@1@0: hnd/clause0<bool,strands<a>,e,b>)) : strands<a,e,b> ) as @pat@2: (strands<a,e,b>))
             -> (match (@fun-strand-done) {
              ((@skip std/core/hnd/Clause2((f: (hnd/marker<e,b>, hnd/ev<strands<a>>, int, error<a>) -> e ())) : hnd/clause2<int,error<a>,(),strands<a>,e,b> ) as @pat@2@0: (hnd/clause2<int,error<a>,(),strands<a>,e,b>))
                 -> f(m, evx@11750, idx, result);
            });
        });
    });
  };
// Insert in order with an accumulating list.
fun insert-acc : forall<a> (xs : list<(int, a)>, idx : int, value : a, acc : list<(int, a)>) -> list<(int, a)>
  = forall<a> fn(xs: list<(int, a)>, idx: int, value: a, acc: list<(int, a)>){
    (match (xs) {
      ((std/core/types/Cons((x: (int, a)), (xx: list<(int, a)>)) : list<(int, a)> ) as @pat: (list<(int, a)>))
         | std/core/int/(<)((match (x) {
            ((@skip std/core/types/Tuple2((@x: int), (@pat@0@0: a)) : (int, a) ) as @pat@0: (int, a))
               -> @x;
          }), idx) -> std/async/async/insert-acc(xx, idx, value, (std/core/types/Cons(x, acc)));
      (@pat@0@1: (list<(int, a)>))
         -> val tl@10096 : list<(int, a)>
                  = std/core/types/Cons((std/core/types/Tuple2(idx, value)), xs);
        (match (acc) {
          ((std/core/types/Nil() : list<(int, a)> ) as @pat@0@2: (list<(int, a)>))
             -> tl@10096;
          (@pat@1: (list<(int, a)>))
             -> std/core/list/@unroll-reverse-acc@10003(tl@10096, acc);
        });
    });
  };
// Insert in order
fun @trmc-insert : forall<a> (xs : list<(int, a)>, idx : int, value : a, n : ? int, @acc : ctx<list<(int, a)>>) -> list<(int, a)>
  = forall<a> fn(xs: list<(int, a)>, idx: int, value: a, n: ? int, @acc: ctx<list<(int, a)>>){
    (match ((std/core/int/(>)((match (n) {
        ((std/core/types/@Optional((@uniq-n@5278: int)) : ? int ) as @pat: ? int)
           -> @uniq-n@5278;
        ((@skip std/core/types/@None() : ? int ) as @pat@0: ? int)
           -> 0;
      }), 100))) {
      ((std/core/types/True() : bool ) as @pat@1: bool)
         -> std/core/types/cctx/((++.))(@acc, (std/async/async/insert-acc(xs, idx, value, std/core/types/Nil)));
      ((@skip std/core/types/False() : bool ) as @pat@2: bool)
         -> (match (xs) {
          ((std/core/types/Cons((x: (int, a)), (xx: list<(int, a)>)) : list<(int, a)> ) as @pat@3: (list<(int, a)>))
             | std/core/int/(<)((match (x) {
                ((@skip std/core/types/Tuple2((@x: int), (@pat@0@0: a)) : (int, a) ) as @pat@4: (int, a))
                   -> @x;
              }), idx) -> val @trmc-x10806 : list<(int, a)>
                            = std/core/types/@cctx-hole-create();
                          val @trmc-x10807 : list<(int, a)>
                            = std/core/types/Cons(x, @trmc-x10806);
            std/async/async/@trmc-insert(xx, idx, value, (std/core/types/@Optional((std/core/int/int-add((match (n) {
                  ((std/core/types/@Optional((@uniq-n@5278@0: int)) : ? int ) as @pat@5: ? int)
                     -> @uniq-n@5278@0;
                  ((@skip std/core/types/@None() : ? int ) as @pat@0@1: ? int)
                     -> 0;
                }), 1)))), (std/core/types/@cctx-extend(@acc, @trmc-x10807, (std/core/types/@field-addr-of(@trmc-x10807, "(\x22std/core/types\x22,\x22\x22,\x22Cons\x22)", "(\x22\x22,\x22\x22,\x22tail\x22)")))));
          (@pat@4@0: (list<(int, a)>))
             -> std/core/types/cctx/((++.))(@acc, (std/core/types/Cons((std/core/types/Tuple2(idx, value)), xs)));
        });
    });
  };
// Insert in order
fun insert : forall<a> (xs : list<(int, a)>, idx : int, value : a, n : ? int) -> list<(int, a)>
  = forall<a> fn(xs@0: list<(int, a)>, idx@0: int, value@0: a, n@0: ? int){
    std/async/async/@trmc-insert(xs@0, idx@0, value@0, n@0, (std/core/types/cctx/empty()));
  };
fun unsafe-no-ndet-div : forall<a,e> (action : () -> <ndet,div|e> a) -> e a
  = forall<a,e> fn<e>(action: () -> <ndet,div|e> a){
    action();
  };
fun unnull : forall<a> (nexn : std/async/null/null<exception>, x : a) -> error<a>
  = forall<a> fn(nexn: std/async/null/null<exception>, x: a){
    (match ((std/async/null/null/maybe(nexn))) {
      ((std/core/types/Nothing() : maybe<exception> ) as @pat: (maybe<exception>))
         -> std/core/exn/Ok(x);
      ((@skip std/core/types/Just(((@skip std/core/exn/Exception((@pat@1: string), (@pat@2: exception-info)) : exception ) as exn: exception)) : maybe<exception> ) as @pat@0: (maybe<exception>))
         -> std/core/exn/Error(exn);
    });
  };
// monadic lift
fun @mlift-await-exn0@11397 : (@y-x10912 : maybe<() -> io-noexn ()>) -> io error<maybe<() -> io-noexn ()>>
  = fn<io>(@y-x10912: maybe<() -> io-noexn ()>){
    std/core/exn/Ok(@y-x10912);
  };
// monadic lift
fun @mlift-await-exn0@11398 : (@y-x10915 : error<()>) -> <async,exn,ndet> ()
  = fn<<async,exn,ndet>>(@y-x10915: error<()>){
    val i@11754 : hnd/ev-index
      = std/core/types/@make-ssize_t(1);
    val w : hnd/evv<<exn,async,ndet>>
      = std/core/hnd/evv-swap-create1(i@11754);
    val y : ()
      = match (@y-x10915) {
        ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@0: string), (@pat@1@0: exception-info)) : exception ) as exn@0: exception)) : error<()> ) as @pat@1: (error<()>))
           -> val ev@11757 : hnd/ev<exn>
                    = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
          (match (ev@11757) {
            ((@skip std/core/hnd/Ev<e,a>((@pat@0@1: hnd/htag<exn>), (m: hnd/marker<e,a>), (h: exn<e,a>), (@pat@1@1: hnd/evv<e>)) : hnd/ev<exn> ) as @pat@2: (hnd/ev<exn>))
               -> (match ((std/core/exn/throw-exn/@select(h))) {
                ((@skip std/core/hnd/Clause1((f@0: (hnd/marker<e,a>, hnd/ev<exn>, exception) -> e ())) : hnd/clause1<exception,(),exn,e,a> ) as @pat@2@0: (hnd/clause1<exception,(),exn,e,a>))
                   -> f@0(m, ev@11757, exn@0);
              });
          });
        ((@skip std/core/exn/Ok((x@1: ())) : error<()> ) as @pat@2@1: (error<()>))
           -> x@1;
      };
    val _ : ()
      = std/core/hnd/evv-set(w);
    match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-cont((forall<a> fn<<exn,async,ndet>>(cont: (a) -> <exn,async,ndet> (), res: a){
          std/core/hnd/open-at1(i@11754, cont, res);
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> y;
    };
  };
// Convenience function for awaiting a NodeJS style callback where the first argument is a possible exception.
pub fun await-exn0 : (setup : (cb : (std/async/null/null<exception>) -> <st<global>,console/console,div,fsys,ndet,net,ui> ()) -> io maybe<() -> io-noexn ()>) -> <async,exn,ndet> ()
  = fn<asyncx>(setup: (cb : (std/async/null/null<exception>) -> io-noexn ()) -> io maybe<() -> io-noexn ()>){
    val i@11763 : hnd/ev-index
      = std/core/types/@make-ssize_t(0);
    val w : hnd/evv<<async,exn,ndet>>
      = std/core/hnd/evv-swap-create1(i@11763);
    val ev@11766 : hnd/ev<async>
      = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
    val y : error<()>
      = match (ev@11766) {
        ((@skip std/core/hnd/Ev<e,a>((@pat@0@1: hnd/htag<async>), (m: hnd/marker<e,a>), (h: async<e,a>), (@pat@1@0: hnd/evv<e>)) : hnd/ev<async> ) as @pat@2: (hnd/ev<async>))
           -> (match (h) {
            ((@skip std/async/async/@Hnd-async((@pat@0: int), (@pat@1: forall<b> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) b,b,async,e,a>), (@pat@2@0: hnd/clause1<scope,(),async,e,a>), (@ctl-do-await: forall<b> hnd/clause1<((await-setup<b> == 4 (cb : (error<b>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>
   )>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<b>,async,e,a>), (@pat@3: (forall<b> hnd/clause1<((await-setup<b> == 4 (cb : (error<b>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<b>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async
   ,e,a>))) : async<e,a> ) as @pat: (async<e,a>))
               -> (match (@ctl-do-await) {
                ((@skip std/core/hnd/Clause1((f@0: (hnd/marker<e,a>, hnd/ev<async>, ((await-setup<()> == 4 (cb : (error<()>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <
   read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool)) -> e error<()>)) : hnd/clause1<((await-setup<()> == 4 (cb : (error<()>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<
   global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<()>,async,e,a> ) as @pat@2@0@0: (hnd/clause1<((await-setup<()> == 4 (cb : (error<()>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet
   ,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<()>,async,e,a>))
                   -> f@0(m, ev@11766, (std/core/types/Tuple3((fn<(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>(cb: (error<()>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()){
                        (match ((std/core/exn/exn/@handle((std/core/exn/@Hnd-exn(0, (forall<b> std/core/hnd/Clause1((fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(m@0: hnd/marker<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>,error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>>, @_wildcard-x653_16: hnd/ev<exn>, x@1: exception){
                              (std/core/hnd/yield-to-final(m@0, (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@_wildcard-x653_45: (hnd/resume-result<b,error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>>) -> <alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>> error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,
   fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>){
                                  (std/core/exn/Error(x@1));
                                })));
                            }))))), (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@res: error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>){
                            @res;
                          }), (fn<<exn,alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(){
                            val x@2@11772 : (maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)
                                  = (setup((fn<(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>(nexn: std/async/null/null<exception>){
                                    val res@0@12520 : (error<()>)
                                          = (match ((std/async/null/null/maybe(nexn))) {
                                            ((std/core/types/Nothing() : maybe<exception> ) as @pat@3@0@0@0: (maybe<exception>))
                                               -> std/core/exn/Ok(std/core/types/Unit);
                                            ((@skip std/core/types/Just(((@skip std/core/exn/Exception((@pat@1@0@0@0: string), (@pat@2@0@0@0@0: exception-info)) : exception ) as exn@1: exception)) : maybe<exception> ) as @pat@0@0@0@0: (maybe<exception>))
                                               -> std/core/exn/Error(exn@1);
                                          });
                                    (cb(res@0@12520, std/core/types/True));
                                  })));
                            (match ((std/core/hnd/yielding())) {
                              ((std/core/types/True() : bool ) as @pat@3@0: bool)
                                 -> std/core/hnd/yield-extend(std/async/async/@mlift-await-exn0@11397);
                              ((@skip std/core/types/False() : bool ) as @pat@0@2: bool)
                                 -> std/core/exn/Ok(x@2@11772);
                            });
                          })))) {
                          ((std/core/exn/Ok((mcleanup: maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)) : error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>> ) as @pat@3@0@0: (error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<
   global>,alloc<global>>)>)>) ()>>))
                             -> mcleanup;
                          ((@skip std/core/exn/Error(((@skip std/core/exn/Exception((@pat@1@0@0: string), (@pat@2@0@0@0: exception-info)) : exception ) as exn: exception)) : error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>> ) as @pat@0@0@0: (error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>))
                             -> val _ : ()
                                      = cb((std/core/exn/Error(exn)), std/core/types/True);
                            std/core/types/Nothing;
                        });
                      }), std/async/async/empty-scope, std/core/types/True)));
              });
          });
      };
    val _ : ()
      = std/core/hnd/evv-set(w);
    val x@11760 : error<()>
      = match ((std/core/hnd/yielding())) {
        ((std/core/types/True() : bool ) as @pat@1@1: bool)
           -> std/core/hnd/yield-cont((forall<a> fn<<async,exn,ndet>>(cont: (a) -> <async,exn,ndet> error<()>, res: a){
            std/core/hnd/open-at1(i@11763, cont, res);
          }));
        ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
           -> y;
      };
    match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat@4: bool)
         -> std/core/hnd/yield-extend(std/async/async/@mlift-await-exn0@11398);
      ((@skip std/core/types/False() : bool ) as @pat@0@3: bool)
         -> val i@0@11774 : (hnd/ev-index == 1 ssize_t)
              = std/core/types/@make-ssize_t(1);
            val w@0 : hnd/evv<<exn,async,ndet>>
              = std/core/hnd/evv-swap-create1(i@0@11774);
            val y@0 : ()
              = (match (x@11760) {
                ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@4: string), (@pat@1@1@0: exception-info)) : exception ) as exn@0: exception)) : error<()> ) as @pat@5: (error<()>))
                   -> val ev@0@11777 : hnd/ev<exn>
                            = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
                  (match (ev@0@11777) {
                    ((@skip std/core/hnd/Ev<e,a>((@pat@0@5: hnd/htag<exn>), (m@1: hnd/marker<e,a>), (h@0: exn<e,a>), (@pat@1@2: hnd/evv<e>)) : hnd/ev<exn> ) as @pat@6: (hnd/ev<exn>))
                       -> (match ((std/core/exn/throw-exn/@select(h@0))) {
                        ((@skip std/core/hnd/Clause1((f@2: (hnd/marker<e,a>, hnd/ev<exn>, exception) -> e ())) : hnd/clause1<exception,(),exn,e,a> ) as @pat@2@1: (hnd/clause1<exception,(),exn,e,a>))
                           -> f@2(m@1, ev@0@11777, exn@0);
                      });
                  });
                ((@skip std/core/exn/Ok((x@5: ())) : error<()> ) as @pat@2@2: (error<()>))
                   -> x@5;
              });
            val _ : ()
              = std/core/hnd/evv-set(w@0);
        (match ((std/core/hnd/yielding())) {
          ((std/core/types/True() : bool ) as @pat@4@0: bool)
             -> std/core/hnd/yield-cont((forall<a> fn<<exn,async,ndet>>(cont@0: (a) -> <exn,async,ndet> (), res@1: a){
              std/core/hnd/open-at1(i@0@11774, cont@0, res@1);
            }));
          ((@skip std/core/types/False() : bool ) as @pat@0@3@0: bool)
             -> y@0;
        });
    };
  };
// monadic lift
fun @mlift-await-exn1@11399 : (@y-x10919 : maybe<() -> io-noexn ()>) -> io error<maybe<() -> io-noexn ()>>
  = fn<io>(@y-x10919: maybe<() -> io-noexn ()>){
    std/core/exn/Ok(@y-x10919);
  };
// monadic lift
fun @mlift-await-exn1@11400 : forall<a> (@y-x10922 : error<a>) -> <async,exn,ndet> a
  = forall<a> fn<<async,exn,ndet>>(@y-x10922: error<a>){
    val i@11780 : hnd/ev-index
      = std/core/types/@make-ssize_t(1);
    val w : hnd/evv<<exn,async,ndet>>
      = std/core/hnd/evv-swap-create1(i@11780);
    val y : a
      = (match (@y-x10922) {
        ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@0: string), (@pat@1@0: exception-info)) : exception ) as exn@0: exception)) : error<a> ) as @pat@1: (error<a>))
           -> val ev@11783 : hnd/ev<exn>
                    = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
          (match (ev@11783) {
            ((@skip std/core/hnd/Ev<e,b>((@pat@0@1: hnd/htag<exn>), (m: hnd/marker<e,b>), (h: exn<e,b>), (@pat@1@1: hnd/evv<e>)) : hnd/ev<exn> ) as @pat@2: (hnd/ev<exn>))
               -> (match ((std/core/exn/throw-exn/@select(h))) {
                ((@skip std/core/hnd/Clause1((f@0: (hnd/marker<e,b>, hnd/ev<exn>, exception) -> e a)) : hnd/clause1<exception,a,exn,e,b> ) as @pat@2@0: (hnd/clause1<exception,a,exn,e,b>))
                   -> f@0(m, ev@11783, exn@0);
              });
          });
        ((@skip std/core/exn/Ok((x@1: a)) : error<a> ) as @pat@2@1: (error<a>))
           -> x@1;
      });
    val _ : ()
      = std/core/hnd/evv-set(w);
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-cont((forall<b> fn<<exn,async,ndet>>(cont: (b) -> <exn,async,ndet> a, res: b){
          std/core/hnd/open-at1(i@11780, cont, res);
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> y;
    });
  };
// Convenience function for awaiting a NodeJS style callback where the first argument is a possible exception
// and the second argument the possible result value.
pub fun await-exn1 : forall<a> (setup : (cb : (std/async/null/null<exception>, a) -> io-noexn ()) -> io maybe<() -> io-noexn ()>) -> asyncx a
  = forall<a> fn<asyncx>(setup: (cb : (std/async/null/null<exception>, a) -> io-noexn ()) -> io maybe<() -> io-noexn ()>){
    val i@11789 : hnd/ev-index
      = std/core/types/@make-ssize_t(0);
    val w : hnd/evv<<async,exn,ndet>>
      = std/core/hnd/evv-swap-create1(i@11789);
    val ev@11792 : hnd/ev<async>
      = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
    val y : error<a>
      = (match (ev@11792) {
        ((@skip std/core/hnd/Ev<e,b>((@pat@0@1: hnd/htag<async>), (m: hnd/marker<e,b>), (h: async<e,b>), (@pat@1@0: hnd/evv<e>)) : hnd/ev<async> ) as @pat@2: (hnd/ev<async>))
           -> (match (h) {
            ((@skip std/async/async/@Hnd-async((@pat@0: int), (@pat@1: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e,b>), (@pat@2@0: hnd/clause1<scope,(),async,e,b>), (@ctl-do-await: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>
   )>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e,b>), (@pat@3: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async
   ,e,b>))) : async<e,b> ) as @pat: (async<e,b>))
               -> (match (@ctl-do-await) {
                ((@skip std/core/hnd/Clause1((f@0: (hnd/marker<e,b>, hnd/ev<async>, ((await-setup<a> == 4 (cb : (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()>), scope, bool)) -> e error<a>)) : hnd/clause1<((await-setup<a> == 4 (cb : (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global>
   == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<a>,async,e,b> ) as @pat@2@0@0: (hnd/clause1<((await-setup<a> == 4 (cb : (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/
   console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<a>,async,e,b>))
                   -> f@0(m, ev@11792, (std/core/types/Tuple3((fn<(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>(cb: (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()){
                        (match ((std/core/exn/exn/@handle((std/core/exn/@Hnd-exn(0, (forall<c> std/core/hnd/Clause1((fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(m@0: hnd/marker<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>,error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>>, @_wildcard-x653_16: hnd/ev<exn>, x@1: exception){
                              (std/core/hnd/yield-to-final(m@0, (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@_wildcard-x653_45: (hnd/resume-result<c,error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>>) -> <alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>> error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,
   fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>){
                                  (std/core/exn/Error(x@1));
                                })));
                            }))))), (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@res: error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>){
                            @res;
                          }), (fn<<exn,alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(){
                            val x@2@11798 : (maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)
                                  = (setup((fn<(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>(nexn: std/async/null/null<exception>, x@0@0: a){
                                    val res@0@12521 : (error<a>)
                                          = (match ((std/async/null/null/maybe(nexn))) {
                                            ((std/core/types/Nothing() : maybe<exception> ) as @pat@3@0@0@0: (maybe<exception>))
                                               -> std/core/exn/Ok(x@0@0);
                                            ((@skip std/core/types/Just(((@skip std/core/exn/Exception((@pat@1@0@0@0: string), (@pat@2@0@0@0@0: exception-info)) : exception ) as exn@1: exception)) : maybe<exception> ) as @pat@0@0@0@0: (maybe<exception>))
                                               -> std/core/exn/Error(exn@1);
                                          });
                                    (cb(res@0@12521, std/core/types/True));
                                  })));
                            (match ((std/core/hnd/yielding())) {
                              ((std/core/types/True() : bool ) as @pat@3@0: bool)
                                 -> std/core/hnd/yield-extend(std/async/async/@mlift-await-exn1@11399);
                              ((@skip std/core/types/False() : bool ) as @pat@0@2: bool)
                                 -> std/core/exn/Ok(x@2@11798);
                            });
                          })))) {
                          ((std/core/exn/Ok((mcleanup: maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)) : error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>> ) as @pat@3@0@0: (error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<
   global>,alloc<global>>)>)>) ()>>))
                             -> mcleanup;
                          ((@skip std/core/exn/Error(((@skip std/core/exn/Exception((@pat@1@0@0: string), (@pat@2@0@0@0: exception-info)) : exception ) as exn: exception)) : error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>> ) as @pat@0@0@0: (error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>))
                             -> val _ : ()
                                      = cb((std/core/exn/Error(exn)), std/core/types/True);
                            std/core/types/Nothing;
                        });
                      }), std/async/async/empty-scope, std/core/types/True)));
              });
          });
      });
    val _ : ()
      = std/core/hnd/evv-set(w);
    val x@11786 : error<a>
      = (match ((std/core/hnd/yielding())) {
        ((std/core/types/True() : bool ) as @pat@1@1: bool)
           -> std/core/hnd/yield-cont((forall<b> fn<<async,exn,ndet>>(cont: (b) -> <async,exn,ndet> error<a>, res: b){
            std/core/hnd/open-at1(i@11789, cont, res);
          }));
        ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
           -> y;
      });
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat@4: bool)
         -> std/core/hnd/yield-extend((fn<<async,exn,ndet>>(@y-x10922: error<a>){
          (std/async/async/@mlift-await-exn1@11400(@y-x10922));
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0@3: bool)
         -> val i@0@11800 : (hnd/ev-index == 1 ssize_t)
              = std/core/types/@make-ssize_t(1);
            val w@0 : hnd/evv<<exn,async,ndet>>
              = std/core/hnd/evv-swap-create1(i@0@11800);
            val y@0 : a
              = (match (x@11786) {
                ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@4: string), (@pat@1@1@0: exception-info)) : exception ) as exn@0: exception)) : error<a> ) as @pat@5: (error<a>))
                   -> val ev@0@11803 : hnd/ev<exn>
                            = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
                  (match (ev@0@11803) {
                    ((@skip std/core/hnd/Ev<e,b>((@pat@0@5: hnd/htag<exn>), (m@1: hnd/marker<e,b>), (h@0: exn<e,b>), (@pat@1@2: hnd/evv<e>)) : hnd/ev<exn> ) as @pat@6: (hnd/ev<exn>))
                       -> (match ((std/core/exn/throw-exn/@select(h@0))) {
                        ((@skip std/core/hnd/Clause1((f@2: (hnd/marker<e,b>, hnd/ev<exn>, exception) -> e a)) : hnd/clause1<exception,a,exn,e,b> ) as @pat@2@1: (hnd/clause1<exception,a,exn,e,b>))
                           -> f@2(m@1, ev@0@11803, exn@0);
                      });
                  });
                ((@skip std/core/exn/Ok((x@5: a)) : error<a> ) as @pat@2@2: (error<a>))
                   -> x@5;
              });
            val _ : ()
              = std/core/hnd/evv-set(w@0);
        (match ((std/core/hnd/yielding())) {
          ((std/core/types/True() : bool ) as @pat@4@0: bool)
             -> std/core/hnd/yield-cont((forall<b> fn<<exn,async,ndet>>(cont@0: (b) -> <exn,async,ndet> a, res@1: b){
              std/core/hnd/open-at1(i@0@11800, cont@0, res@1);
            }));
          ((@skip std/core/types/False() : bool ) as @pat@0@3@0: bool)
             -> y@0;
        });
    });
  };
// monadic lift
fun @mlift-await0@11401 : (@y-x10926 : maybe<() -> io-noexn ()>) -> io error<maybe<() -> io-noexn ()>>
  = fn<io>(@y-x10926: maybe<() -> io-noexn ()>){
    std/core/exn/Ok(@y-x10926);
  };
// monadic lift
fun @mlift-await0@11402 : (wild_@0 : ()) -> io maybe<() -> io-noexn ()>
  = fn<io>(wild_@0: ()){
    std/core/types/Nothing;
  };
// monadic lift
fun @mlift-await0@11403 : (@y-x10929 : error<()>) -> <async,exn,ndet> ()
  = fn<<async,exn,ndet>>(@y-x10929: error<()>){
    val i@11806 : hnd/ev-index
      = std/core/types/@make-ssize_t(1);
    val w : hnd/evv<<exn,async,ndet>>
      = std/core/hnd/evv-swap-create1(i@11806);
    val y : ()
      = match (@y-x10929) {
        ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@0: string), (@pat@1@0: exception-info)) : exception ) as exn@0: exception)) : error<()> ) as @pat@1: (error<()>))
           -> val ev@11809 : hnd/ev<exn>
                    = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
          (match (ev@11809) {
            ((@skip std/core/hnd/Ev<e,a>((@pat@0@1: hnd/htag<exn>), (m: hnd/marker<e,a>), (h: exn<e,a>), (@pat@1@1: hnd/evv<e>)) : hnd/ev<exn> ) as @pat@2: (hnd/ev<exn>))
               -> (match ((std/core/exn/throw-exn/@select(h))) {
                ((@skip std/core/hnd/Clause1((f@0: (hnd/marker<e,a>, hnd/ev<exn>, exception) -> e ())) : hnd/clause1<exception,(),exn,e,a> ) as @pat@2@0: (hnd/clause1<exception,(),exn,e,a>))
                   -> f@0(m, ev@11809, exn@0);
              });
          });
        ((@skip std/core/exn/Ok((x@1: ())) : error<()> ) as @pat@2@1: (error<()>))
           -> x@1;
      };
    val _ : ()
      = std/core/hnd/evv-set(w);
    match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-cont((forall<a> fn<<exn,async,ndet>>(cont: (a) -> <exn,async,ndet> (), res: a){
          std/core/hnd/open-at1(i@11806, cont, res);
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> y;
    };
  };
// Convenience function for awaiting a zero argument callback.
pub fun await0 : (setup : (cb : () -> <st<global>,console/console,div,fsys,ndet,net,ui> ()) -> io ()) -> <async,exn,ndet> ()
  = fn<asyncx>(setup: (cb : () -> io-noexn ()) -> io ()){
    val i@11815 : hnd/ev-index
      = std/core/types/@make-ssize_t(0);
    val w : hnd/evv<<async,exn,ndet>>
      = std/core/hnd/evv-swap-create1(i@11815);
    val ev@11818 : hnd/ev<async>
      = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
    val y : error<()>
      = match (ev@11818) {
        ((@skip std/core/hnd/Ev<e,a>((@pat@0@1: hnd/htag<async>), (m: hnd/marker<e,a>), (h: async<e,a>), (@pat@1@0: hnd/evv<e>)) : hnd/ev<async> ) as @pat@2: (hnd/ev<async>))
           -> (match (h) {
            ((@skip std/async/async/@Hnd-async((@pat@0: int), (@pat@1: forall<b> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) b,b,async,e,a>), (@pat@2@0: hnd/clause1<scope,(),async,e,a>), (@ctl-do-await: forall<b> hnd/clause1<((await-setup<b> == 4 (cb : (error<b>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>
   )>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<b>,async,e,a>), (@pat@3: (forall<b> hnd/clause1<((await-setup<b> == 4 (cb : (error<b>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<b>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async
   ,e,a>))) : async<e,a> ) as @pat: (async<e,a>))
               -> (match (@ctl-do-await) {
                ((@skip std/core/hnd/Clause1((f@0: (hnd/marker<e,a>, hnd/ev<async>, ((await-setup<()> == 4 (cb : (error<()>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <
   read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool)) -> e error<()>)) : hnd/clause1<((await-setup<()> == 4 (cb : (error<()>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<
   global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<()>,async,e,a> ) as @pat@2@0@0: (hnd/clause1<((await-setup<()> == 4 (cb : (error<()>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet
   ,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<()>,async,e,a>))
                   -> f@0(m, ev@11818, (std/core/types/Tuple3((fn<(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>(cb: (error<()>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()){
                        (match ((std/core/exn/exn/@handle((std/core/exn/@Hnd-exn(0, (forall<b> std/core/hnd/Clause1((fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(m@0: hnd/marker<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>,error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>>, @_wildcard-x653_16: hnd/ev<exn>, x@1: exception){
                              (std/core/hnd/yield-to-final(m@0, (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@_wildcard-x653_45: (hnd/resume-result<b,error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>>) -> <alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>> error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,
   fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>){
                                  (std/core/exn/Error(x@1));
                                })));
                            }))))), (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@res: error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>){
                            @res;
                          }), (fn<<exn,alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(){
                            val x@3@11826 : ()
                              = (setup((fn<(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>(){
                                (cb((std/core/exn/Ok(std/core/types/Unit)), std/core/types/True));
                              })));
                            val x@2@11824 : (maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)
                              = (match ((std/core/hnd/yielding())) {
                                ((std/core/types/True() : bool ) as @pat@4: bool)
                                   -> std/core/hnd/yield-extend(std/async/async/@mlift-await0@11402);
                                ((@skip std/core/types/False() : bool ) as @pat@0@3: bool)
                                   -> std/core/types/Nothing;
                              });
                            (match ((std/core/hnd/yielding())) {
                              ((std/core/types/True() : bool ) as @pat@3@0: bool)
                                 -> std/core/hnd/yield-extend(std/async/async/@mlift-await0@11401);
                              ((@skip std/core/types/False() : bool ) as @pat@0@2: bool)
                                 -> std/core/exn/Ok(x@2@11824);
                            });
                          })))) {
                          ((std/core/exn/Ok((mcleanup: maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)) : error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>> ) as @pat@3@0@0: (error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<
   global>,alloc<global>>)>)>) ()>>))
                             -> mcleanup;
                          ((@skip std/core/exn/Error(((@skip std/core/exn/Exception((@pat@1@0@0: string), (@pat@2@0@0@0: exception-info)) : exception ) as exn: exception)) : error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>> ) as @pat@0@0@0: (error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>))
                             -> val _ : ()
                                      = cb((std/core/exn/Error(exn)), std/core/types/True);
                            std/core/types/Nothing;
                        });
                      }), std/async/async/empty-scope, std/core/types/True)));
              });
          });
      };
    val _ : ()
      = std/core/hnd/evv-set(w);
    val x@11812 : error<()>
      = match ((std/core/hnd/yielding())) {
        ((std/core/types/True() : bool ) as @pat@1@1: bool)
           -> std/core/hnd/yield-cont((forall<a> fn<<async,exn,ndet>>(cont: (a) -> <async,exn,ndet> error<()>, res: a){
            std/core/hnd/open-at1(i@11815, cont, res);
          }));
        ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
           -> y;
      };
    match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat@5: bool)
         -> std/core/hnd/yield-extend(std/async/async/@mlift-await0@11403);
      ((@skip std/core/types/False() : bool ) as @pat@0@4: bool)
         -> val i@0@11828 : (hnd/ev-index == 1 ssize_t)
              = std/core/types/@make-ssize_t(1);
            val w@0 : hnd/evv<<exn,async,ndet>>
              = std/core/hnd/evv-swap-create1(i@0@11828);
            val y@0 : ()
              = (match (x@11812) {
                ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@5: string), (@pat@1@1@0: exception-info)) : exception ) as exn@0: exception)) : error<()> ) as @pat@6: (error<()>))
                   -> val ev@0@11831 : hnd/ev<exn>
                            = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
                  (match (ev@0@11831) {
                    ((@skip std/core/hnd/Ev<e,a>((@pat@0@6: hnd/htag<exn>), (m@1: hnd/marker<e,a>), (h@0: exn<e,a>), (@pat@1@2: hnd/evv<e>)) : hnd/ev<exn> ) as @pat@7: (hnd/ev<exn>))
                       -> (match ((std/core/exn/throw-exn/@select(h@0))) {
                        ((@skip std/core/hnd/Clause1((f@2: (hnd/marker<e,a>, hnd/ev<exn>, exception) -> e ())) : hnd/clause1<exception,(),exn,e,a> ) as @pat@2@1: (hnd/clause1<exception,(),exn,e,a>))
                           -> f@2(m@1, ev@0@11831, exn@0);
                      });
                  });
                ((@skip std/core/exn/Ok((x@6: ())) : error<()> ) as @pat@2@2: (error<()>))
                   -> x@6;
              });
            val _ : ()
              = std/core/hnd/evv-set(w@0);
        (match ((std/core/hnd/yielding())) {
          ((std/core/types/True() : bool ) as @pat@5@0: bool)
             -> std/core/hnd/yield-cont((forall<a> fn<<exn,async,ndet>>(cont@0: (a) -> <exn,async,ndet> (), res@1: a){
              std/core/hnd/open-at1(i@0@11828, cont@0, res@1);
            }));
          ((@skip std/core/types/False() : bool ) as @pat@0@4@0: bool)
             -> y@0;
        });
    };
  };
// monadic lift
fun @mlift-await-to-channel@11404 : (@y-x10931 : maybe<() -> io-noexn ()>) -> io error<maybe<() -> io-noexn ()>>
  = fn<io>(@y-x10931: maybe<() -> io-noexn ()>){
    std/core/exn/Ok(@y-x10931);
  };
// monadic lift
fun @mlift-await-to-channel@11405 : forall<a> (ch : channel<a>, wild_@0@0 : ()) -> async channel<a>
  = forall<a> fn<async>(ch: channel<a>, wild_@0@0: ()){
    ch;
  };
// Primitive: Execute `setup` to set up an asynchronous callback with the host platform. Invoke `cb` as the callback: it takes either
// an exception or a result value, together with boolean parameter whether the callback is done.
// The callback `cb` will eventually emit the result into the given channel `ch` after applying the transformation `f` to the result.\
// Note: once you exit the `cancelable` scope where `await-to-channel` was called, the callback is invoked with a `Cancel` exception.
// The channel should always be awaited within the same `cancelable` scope as the `await-to-channel` invokation.
pub fun await-to-channel : forall<a,b> (setup : (cb : (error<a>, bool) -> io-noexn ()) -> io maybe<() -> io-noexn ()>, ch : channel<b>, f : (error<a>) -> b) -> async channel<b>
  = forall<a,b> fn<async>(setup: (cb : (error<a>, bool) -> io-noexn ()) -> io maybe<() -> io-noexn ()>, ch: channel<b>, f: (error<a>) -> b){
    val ev@11837 : hnd/ev<async>
      = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
    val x@11834 : ()
      = (match (ev@11837) {
        ((@skip std/core/hnd/Ev<e,c>((@pat@0@0: hnd/htag<async>), (m: hnd/marker<e,c>), (h: async<e,c>), (@pat@1@0: hnd/evv<e>)) : hnd/ev<async> ) as @pat@1: (hnd/ev<async>))
           -> (match (h) {
            ((@skip std/async/async/@Hnd-async((@pat@0: int), (@pat@1@1: forall<d> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) d,d,async,e,c>), (@pat@2: hnd/clause1<scope,(),async,e,c>), (@pat@3: forall<d> hnd/clause1<((await-setup<d> == 4 (cb : (error<d>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())
   -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<d>,async,e,c>), (@ctl-no-await: (forall<d> hnd/clause1<((await-setup<d> == 4 (cb : (error<d>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<d>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async
   ,e,c>))) : async<e,c> ) as @pat: (async<e,c>))
               -> (match (@ctl-no-await) {
                ((@skip std/core/hnd/Clause1((f@0: (hnd/marker<e,c>, hnd/ev<async>, ((await-setup<a> == 4 (cb : (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<a>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())) -> e ())) : hnd/clause1<((await-setup<a> == 4 (cb : (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global>
   == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<a>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async,e,c> ) as @pat@2@0: (hnd/clause1<((await-setup<a> == 4 (cb : (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console
   /console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<a>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,
   write<global>,alloc<global>>)>)>) ()),(),async,e,c>))
                   -> f@0(m, ev@11837, (std/core/types/Tuple4((fn<(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>(cb: (error<a>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()){
                        (match ((std/core/exn/exn/@handle((std/core/exn/@Hnd-exn(0, (forall<d> std/core/hnd/Clause1((fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(m@0: hnd/marker<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>,error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>>, @_wildcard-x653_16: hnd/ev<exn>, x@0: exception){
                              (std/core/hnd/yield-to-final(m@0, (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@_wildcard-x653_45: (hnd/resume-result<d,error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>>) -> <alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>> error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,
   fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>){
                                  (std/core/exn/Error(x@0));
                                })));
                            }))))), (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@res: error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>){
                            @res;
                          }), (fn<<exn,alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(){
                            val x@1@11844 : (maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)
                                  = (setup(cb));
                            (match ((std/core/hnd/yielding())) {
                              ((std/core/types/True() : bool ) as @pat@3@0: bool)
                                 -> std/core/hnd/yield-extend(std/async/async/@mlift-await-to-channel@11404);
                              ((@skip std/core/types/False() : bool ) as @pat@0@1: bool)
                                 -> std/core/exn/Ok(x@1@11844);
                            });
                          })))) {
                          ((std/core/exn/Ok((mcleanup: maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)) : error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>> ) as @pat@4: (error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>
   ,alloc<global>>)>)>) ()>>))
                             -> mcleanup;
                          ((@skip std/core/exn/Error(((@skip std/core/exn/Exception((@pat@1@1@0: string), (@pat@2@0@0: exception-info)) : exception ) as exn: exception)) : error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>> ) as @pat@0@2: (error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>))
                             -> val _ : ()
                                      = cb((std/core/exn/Error(exn)), std/core/types/True);
                            std/core/types/Nothing;
                        });
                      }), std/async/async/empty-scope, std/core/types/True, (fn<(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>(res: error<a>){
                        val value@10113 : b
                              = (f(res));
                        (match ((std/core/types/ref/(!)((match (ch) {
                            ((@skip std/async/async/Channel((@pat@0@0@0: int), (@x: ref<global,channel-state<b>>)) : channel<b> ) as @pat@3@0@0: (channel<b>))
                               -> @x;
                          }), std/core/types/@Hdiv))) {
                          ((std/async/async/Empty() : channel-state<b> ) as @pat@4@0: (channel-state<b>))
                             -> std/core/types/set((match (ch) {
                                ((@skip std/async/async/Channel((@pat@0@0@0@0: int), (@x@0: ref<global,channel-state<b>>)) : channel<b> ) as @pat@3@0@0@0: (channel<b>))
                                   -> @x@0;
                              }), (std/async/async/Values(value@10113, std/core/types/Nil)));
                          ((std/async/async/Values((v: b), (vs: list<b>)) : channel-state<b> ) as @pat@0@2@0: (channel-state<b>))
                             -> val ys@10120 : list<b>
                                  = std/core/types/Cons(value@10113, std/core/types/Nil);
                                val values@0@10118 : ? (list<b>)
                                  = std/core/types/@Optional((match (vs) {
                                    ((std/core/types/Nil() : list<b> ) as @pat@0@4: (list<b>))
                                       -> ys@10120;
                                    (@pat@7: (list<b>))
                                       -> std/core/list/@unroll-append@10004(vs, ys@10120);
                                  }));
                            std/core/types/set((match (ch) {
                                ((@skip std/async/async/Channel((@pat@0@0@1: int), (@x@1: ref<global,channel-state<b>>)) : channel<b> ) as @pat@3@1: (channel<b>))
                                   -> @x@1;
                              }), (std/async/async/Values(v, (match (values@0@10118) {
                                  ((std/core/types/@Optional((@uniq-values@967@0: list<b>)) : ? (list<b>) ) as @pat@6: ? (list<b>))
                                     -> @uniq-values@967@0;
                                  ((@skip std/core/types/@None() : ? (list<b>) ) as @pat@0@3: ? (list<b>))
                                     -> std/core/types/Nil;
                                }))));
                          ((@skip std/async/async/Waiting((l: (b) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()), (ls: list<(b) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)) : channel-state<b> ) as @pat@1@0@0: (channel-state<b>))
                             -> val _@0 : ()
                                      = std/core/types/set((match (ch) {
                                          ((@skip std/async/async/Channel((@pat@0@0@2: int), (@x@2: ref<global,channel-state<b>>)) : channel<b> ) as @pat@3@2: (channel<b>))
                                             -> @x@2;
                                        }), (match (ls) {
                                          ((std/core/types/Nil() : list<(b) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()> ) as @pat@8: (list<(b) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>))
                                             -> std/async/async/Empty;
                                          ((@skip std/core/types/Cons((l@0: (b) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()), (ls@0: list<(b) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)) : list<(b) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,
   alloc<global>>)>)>) ()> ) as @pat@0@1@0: (list<(b) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>))
                                             -> std/async/async/Waiting(l@0, ls@0);
                                        }));
                            l(value@10113);
                        });
                      }))));
              });
          });
      });
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat@5: bool)
         -> std/core/hnd/yield-extend((fn<async>(wild_@0@0: ()){
          ch;
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0@5: bool)
         -> ch;
    });
  };
fun parent-scope : (cid : int, scope : scope) -> scope
  = fn(cid: int, scope: scope){
    match (scope) {
      ((@skip std/async/async/Scope((cids: list<int>)) : scope ) as @pat: scope)
         -> std/async/async/Scope((std/core/types/Cons(cid, cids)));
    };
  };
// monadic lift
fun @mlift-cancelable@11406 : forall<a,e> (x@0 : a, wild_ : ()) -> <async|e> a
  = forall<a,e> fn<<async|e>>(x@0: a, wild_: ()){
    x@0;
  };
// monadic lift
fun @mlift-cancelable@11407 : forall<a,e> (action : () -> <async|e> a, @y-x10945 : hnd/ev-index) -> <async,async|e> a
  = forall<a,e> fn<<async,async|e>>(action: () -> <async|e> a, @y-x10945: hnd/ev-index){
    val w0 : hnd/evv<hnd/_e2>
      = std/core/hnd/evv-swap-delete(@y-x10945, std/core/types/True);
    val x : a
      = action();
    val _ : ()
      = std/core/hnd/evv-set(w0);
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-cont((forall<b> fn<<async,async|e>>(cont: (b) -> <async,async|e> a, res: b){
          std/core/hnd/mask-at1(@y-x10945, std/core/types/True, cont, res);
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> x;
    });
  };
// monadic lift
fun @mlift-cancelable@11408 : forall<_a,_b,_c,d,e> (action : () -> <async|e> d, cid : int) -> <async|e> d
  = forall<_a,_b,_c,d,e> fn<<async|e>>(action: () -> <async|e> d, cid: int){
    val extend : (scope : scope) -> scope
          = fn(scope: scope){
            (match (scope) {
              ((@skip std/async/async/Scope((cids: list<int>)) : scope ) as @pat: scope)
                 -> std/async/async/Scope((std/core/types/Cons(cid, cids)));
            });
          };
    std/async/async/async/@handle((std/async/async/@Hnd-async(1, (forall<a1> std/core/hnd/clause-tail1((fn<<async|e>>(f: () -> io-noexn a1){
          val i@11851 : hnd/ev-index
            = (std/core/hnd/@evv-index(std/async/async/async/@tag));
          val w : (hnd/evv<<async|e>>)
            = (std/core/hnd/evv-swap-create1(i@11851));
          val ev@11854 : (hnd/ev<async>)
            = (std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0))));
          val y : a1
            = (match (ev@11854) {
              ((@skip std/core/hnd/Ev<e1,b1>((@pat@0@1: hnd/htag<async>), (m: hnd/marker<e1,b1>), (h: async<e1,b1>), (@pat@1@0: hnd/evv<e1>)) : hnd/ev<async> ) as @pat@1: (hnd/ev<async>))
                 -> (match (h) {
                  ((@skip std/async/async/@Hnd-async((@pat@0@0: int), (@ctl-async-iox: forall<c1> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c1,c1,async,e1,b1>), (@pat@1@1: hnd/clause1<scope,(),async,e1,b1>), (@pat@2: forall<c1> hnd/clause1<((await-setup<c1> == 4 (cb : (error<c1>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<
   global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c1>,async,e1,b1>), (@pat@3: (forall<c1> hnd/clause1<((await-setup<c1> == 4 (cb : (error<c1>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,
   ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c1>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc
   <global>>)>)>) ()),(),async,e1,b1>))) : async<e1,b1> ) as @pat@0: (async<e1,b1>))
                     -> (match (@ctl-async-iox) {
                      ((@skip std/core/hnd/Clause1((f@1: (hnd/marker<e1,b1>, hnd/ev<async>, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) a1) -> e1 a1)) : hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) a1,a1,async,e1,b1> ) as @pat@2@0: (hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,
   net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) a1,a1,async,e1,b1>))
                         -> f@1(m, ev@11854, f);
                    });
                });
            });
          val _ : ()
            = (std/core/hnd/evv-set(w));
          (match ((std/core/hnd/yielding())) {
            ((std/core/types/True() : bool ) as @pat@0@2: bool)
               -> std/core/hnd/yield-cont((forall<b1> fn<<async|e>>(cont: (b1) -> <async|e> a1, res: b1){
                std/core/hnd/open-at1(i@11851, cont, res);
              }));
            ((@skip std/core/types/False() : bool ) as @pat@0@0@0: bool)
               -> y;
          });
        }))), (std/core/hnd/clause-tail1((fn<<async|e>>(scope@0@0: scope){
          val @x-x1@1@11300 : scope
            = (std/core/hnd/@open-none1(extend, scope@0@0));
          val i@0@11857 : hnd/ev-index
            = (std/core/hnd/@evv-index(std/async/async/async/@tag));
          val w@0 : (hnd/evv<<async|e>>)
            = (std/core/hnd/evv-swap-create1(i@0@11857));
          val ev@0@11860 : (hnd/ev<async>)
            = (std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0))));
          val y@0 : ()
            = (match (ev@0@11860) {
              ((@skip std/core/hnd/Ev<e1,a1>((@pat@0@3: hnd/htag<async>), (m@0: hnd/marker<e1,a1>), (h@0: async<e1,a1>), (@pat@1@1@0: hnd/evv<e1>)) : hnd/ev<async> ) as @pat@4: (hnd/ev<async>))
                 -> (match (h@0) {
                  ((@skip std/async/async/@Hnd-async((@pat@0@4: int), (@pat@1@2: forall<b1> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) b1,b1,async,e1,a1>), (@ctl-cancel: hnd/clause1<scope,(),async,e1,a1>), (@pat@2@1: forall<b1> hnd/clause1<((await-setup<b1> == 4 (cb : (error<b1>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global
   >,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<b1>,async,e1,a1>), (@pat@3@0: (forall<b1> hnd/clause1<((await-setup<b1> == 4 (cb : (error<b1>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(
   st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<b1>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<
   global>>)>)>) ()),(),async,e1,a1>))) : async<e1,a1> ) as @pat@5: (async<e1,a1>))
                     -> (match (@ctl-cancel) {
                      ((@skip std/core/hnd/Clause1((f@3: (hnd/marker<e1,a1>, hnd/ev<async>, scope) -> e1 ())) : hnd/clause1<scope,(),async,e1,a1> ) as @pat@2@0@0: (hnd/clause1<scope,(),async,e1,a1>))
                         -> f@3(m@0, ev@0@11860, @x-x1@1@11300);
                    });
                });
            });
          val _ : ()
            = (std/core/hnd/evv-set(w@0));
          (match ((std/core/hnd/yielding())) {
            ((std/core/types/True() : bool ) as @pat@3@1: bool)
               -> std/core/hnd/yield-cont((forall<a1> fn<<async|e>>(cont@0: (a1) -> <async|e> (), res@0: a1){
                std/core/hnd/open-at1(i@0@11857, cont@0, res@0);
              }));
            ((@skip std/core/types/False() : bool ) as @pat@0@2@0: bool)
               -> y@0;
          });
        }))), (forall<a1> std/core/hnd/clause-tail3((fn<<async|e>>(setup: await-setup<a1>, scope@1@0: scope, c: bool){
          val @x-x2@11303 : scope
            = (std/core/hnd/@open-none1(extend, scope@1@0));
          val i@1@11863 : hnd/ev-index
            = (std/core/hnd/@evv-index(std/async/async/async/@tag));
          val w@1 : (hnd/evv<<async|e>>)
            = (std/core/hnd/evv-swap-create1(i@1@11863));
          val ev@1@11868 : (hnd/ev<async>)
            = (std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0))));
          val y@1 : (error<a1>)
            = (match (ev@1@11868) {
              ((@skip std/core/hnd/Ev<e1,b1>((@pat@0@5: hnd/htag<async>), (m@1: hnd/marker<e1,b1>), (h@1: async<e1,b1>), (@pat@1@2@0: hnd/evv<e1>)) : hnd/ev<async> ) as @pat@6: (hnd/ev<async>))
                 -> (match (h@1) {
                  ((@skip std/async/async/@Hnd-async((@pat@0@6: int), (@pat@1@3: forall<c1> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c1,c1,async,e1,b1>), (@pat@2@2: hnd/clause1<scope,(),async,e1,b1>), (@ctl-do-await: forall<c1> hnd/clause1<((await-setup<c1> == 4 (cb : (error<c1>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<
   global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c1>,async,e1,b1>), (@pat@3@2: (forall<c1> hnd/clause1<((await-setup<c1> == 4 (cb : (error<c1>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,
   fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c1>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,
   alloc<global>>)>)>) ()),(),async,e1,b1>))) : async<e1,b1> ) as @pat@7: (async<e1,b1>))
                     -> (match (@ctl-do-await) {
                      ((@skip std/core/hnd/Clause1((f@5: (hnd/marker<e1,b1>, hnd/ev<async>, ((await-setup<a1> == 4 (cb : (error<a1>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global>
   == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool)) -> e1 error<a1>)) : hnd/clause1<((await-setup<a1> == 4 (cb : (error<a1>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,
   ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<a1>,async,e1,b1> ) as @pat@2@1@0: (hnd/clause1<((await-setup<a1> == 4 (cb : (error<a1>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total
   == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<a1>,async,e1,b1>))
                         -> f@5(m@1, ev@1@11868, (std/core/types/Tuple3(setup, @x-x2@11303, c)));
                    });
                });
            });
          val _ : ()
            = (std/core/hnd/evv-set(w@1));
          (match ((std/core/hnd/yielding())) {
            ((std/core/types/True() : bool ) as @pat@5@0: bool)
               -> std/core/hnd/yield-cont((forall<b1> fn<<async|e>>(cont@1: (b1) -> <async|e> error<a1>, res@1: b1){
                std/core/hnd/open-at1(i@1@11863, cont@1, res@1);
              }));
            ((@skip std/core/types/False() : bool ) as @pat@0@4@0: bool)
               -> y@1;
          });
        }))), (forall<a1> std/core/hnd/clause-tail4((fn<<async|e>>(setup@0@0: await-setup<a1>, scope@2@0: scope, c@0: bool, f@0@0: (error<a1>) -> io-noexn ()){
          val @x-x2@0@11307 : scope
            = (std/core/hnd/@open-none1(extend, scope@2@0));
          val i@2@11873 : hnd/ev-index
            = (std/core/hnd/@evv-index(std/async/async/async/@tag));
          val w@2 : (hnd/evv<<async|e>>)
            = (std/core/hnd/evv-swap-create1(i@2@11873));
          val ev@2@11879 : (hnd/ev<async>)
            = (std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0))));
          val y@2 : ()
            = (match (ev@2@11879) {
              ((@skip std/core/hnd/Ev<e1,b1>((@pat@0@7: hnd/htag<async>), (m@2: hnd/marker<e1,b1>), (h@2: async<e1,b1>), (@pat@1@3@0: hnd/evv<e1>)) : hnd/ev<async> ) as @pat@8: (hnd/ev<async>))
                 -> (match (h@2) {
                  ((@skip std/async/async/@Hnd-async((@pat@0@8: int), (@pat@1@4: forall<c1> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c1,c1,async,e1,b1>), (@pat@2@3: hnd/clause1<scope,(),async,e1,b1>), (@pat@3@3: forall<c1> hnd/clause1<((await-setup<c1> == 4 (cb : (error<c1>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,
   alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c1>,async,e1,b1>), (@ctl-no-await: (forall<c1> hnd/clause1<((await-setup<c1> == 4 (cb : (error<c1>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,
   ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c1>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc
   <global>>)>)>) ()),(),async,e1,b1>))) : async<e1,b1> ) as @pat@9: (async<e1,b1>))
                     -> (match (@ctl-no-await) {
                      ((@skip std/core/hnd/Clause1((f@7: (hnd/marker<e1,b1>, hnd/ev<async>, ((await-setup<a1> == 4 (cb : (error<a1>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global>
   == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<a1>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())) -> e1 ())) : hnd/clause1<((await-setup<a1> == 4 (cb : (error<a1>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,
   ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<a1>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async,e1,b1> ) as @pat@2@2@0: (hnd/clause1<((await-setup<a1> == 4 (cb : (error<a1>, bool) -> (io-noexn == 3 <div,(
   io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<a1>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<
   global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async,e1,b1>))
                         -> f@7(m@2, ev@2@11879, (std/core/types/Tuple4(setup@0@0, @x-x2@0@11307, c@0, f@0@0)));
                    });
                });
            });
          val _ : ()
            = (std/core/hnd/evv-set(w@2));
          (match ((std/core/hnd/yielding())) {
            ((std/core/types/True() : bool ) as @pat@7@0: bool)
               -> std/core/hnd/yield-cont((forall<b1> fn<<async|e>>(cont@2: (b1) -> <async|e> (), res@2: b1){
                std/core/hnd/open-at1(i@2@11873, cont@2, res@2);
              }));
            ((@skip std/core/types/False() : bool ) as @pat@0@6@0: bool)
               -> y@2;
          });
        }))))), (fn<<async|e>>(x@0@0: d){
        val @x-x1@7@11311 : scope
          = (std/core/hnd/@open-none1(extend, std/async/async/empty-scope));
        val i@3@11887 : hnd/ev-index
          = (std/core/hnd/@evv-index(std/async/async/async/@tag));
        val w@3 : (hnd/evv<<async|e>>)
          = (std/core/hnd/evv-swap-create1(i@3@11887));
        val ev@3@11890 : (hnd/ev<async>)
          = (std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0))));
        val y@3 : ()
          = (match (ev@3@11890) {
            ((@skip std/core/hnd/Ev<e1,a1>((@pat@0@10: hnd/htag<async>), (m@3: hnd/marker<e1,a1>), (h@3: async<e1,a1>), (@pat@1@4@0: hnd/evv<e1>)) : hnd/ev<async> ) as @pat@11: (hnd/ev<async>))
               -> (match (h@3) {
                ((@skip std/async/async/@Hnd-async((@pat@0@9: int), (@pat@1@5: forall<b1> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) b1,b1,async,e1,a1>), (@ctl-cancel@0: hnd/clause1<scope,(),async,e1,a1>), (@pat@2@4: forall<b1> hnd/clause1<((await-setup<b1> == 4 (cb : (error<b1>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global
   >,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<b1>,async,e1,a1>), (@pat@3@4: (forall<b1> hnd/clause1<((await-setup<b1> == 4 (cb : (error<b1>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(
   st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<b1>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<
   global>>)>)>) ()),(),async,e1,a1>))) : async<e1,a1> ) as @pat@10: (async<e1,a1>))
                   -> (match (@ctl-cancel@0) {
                    ((@skip std/core/hnd/Clause1((f@9: (hnd/marker<e1,a1>, hnd/ev<async>, scope) -> e1 ())) : hnd/clause1<scope,(),async,e1,a1> ) as @pat@2@3@0: (hnd/clause1<scope,(),async,e1,a1>))
                       -> f@9(m@3, ev@3@11890, @x-x1@7@11311);
                  });
              });
          });
        val _ : ()
          = (std/core/hnd/evv-set(w@3));
        val x@3@11885 : ()
          = (match ((std/core/hnd/yielding())) {
            ((std/core/types/True() : bool ) as @pat@10@0: bool)
               -> std/core/hnd/yield-cont((forall<a1> fn<<async|e>>(cont@3: (a1) -> <async|e> (), res@3: a1){
                std/core/hnd/open-at1(i@3@11887, cont@3, res@3);
              }));
            ((@skip std/core/types/False() : bool ) as @pat@0@9@0: bool)
               -> y@3;
          });
        (match ((std/core/hnd/yielding())) {
          ((std/core/types/True() : bool ) as @pat@9@0: bool)
             -> std/core/hnd/yield-extend((fn<<async|e>>(wild_: ()){
              x@0@0;
            }));
          ((@skip std/core/types/False() : bool ) as @pat@0@8@0: bool)
             -> x@0@0;
        });
      }), (fn<<async,async|e>>(){
        val x@6@11895 : hnd/ev-index
              = (std/core/hnd/@evv-index(std/async/async/async/@tag));
        (match ((std/core/hnd/yielding())) {
          ((std/core/types/True() : bool ) as @pat@12: bool)
             -> std/core/hnd/yield-extend((fn<<async,async|e>>(@y-x10945: (hnd/ev-index == 1 ssize_t)){
              (std/async/async/@mlift-cancelable@11407(action, @y-x10945));
            }));
          ((@skip std/core/types/False() : bool ) as @pat@0@11: bool)
             -> std/async/async/@mlift-cancelable@11407(action, x@6@11895);
        });
      }));
  };
// Execute `action` in a cancelable scope. If `cancel` is called within `action`,
// any outstanding asynchronous operations started in the cancelable scope are canceled.
// (Outstanding operations outside the cancelable scope are not canceled).
pub fun cancelable : forall<a,e> (action : () -> <async|e> a) -> <async|e> a
  = forall<a,e> fn<<async|e>>(action: () -> <async|e> a){
    val i@11900 : hnd/ev-index
      = std/core/hnd/@evv-index(std/async/async/async/@tag);
    val w : hnd/evv<<async|e>>
      = std/core/hnd/evv-swap-create1(i@11900);
    val ev@11903 : hnd/ev<async>
      = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
    val y : int
      = (match (ev@11903) {
        ((@skip std/core/hnd/Ev<e1,b>((@pat@0@1: hnd/htag<async>), (m: hnd/marker<e1,b>), (h: async<e1,b>), (@pat@1@0: hnd/evv<e1>)) : hnd/ev<async> ) as @pat@2: (hnd/ev<async>))
           -> (match (h) {
            ((@skip std/async/async/@Hnd-async((@pat@0: int), (@ctl-async-iox: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e1,b>), (@pat@1: hnd/clause1<scope,(),async,e1,b>), (@pat@2@0: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>
   >)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e1,b>), (@pat@3: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async
   ,e1,b>))) : async<e1,b> ) as @pat: (async<e1,b>))
               -> (match (@ctl-async-iox) {
                ((@skip std/core/hnd/Clause1((f@0: (hnd/marker<e1,b>, hnd/ev<async>, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) int) -> e1 int)) : hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) int,int,async,e1,b> ) as @pat@2@0@0: (hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,
   net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) int,int,async,e1,b>))
                   -> f@0(m, ev@11903, (fn<ndet>(){
                      val u : int
                        = (std/core/types/ref/(!)(std/core/unique-count, std/core/types/@Hnodiv));
                      val _ : ()
                        = (std/core/types/set(std/core/unique-count, (std/core/int/int-add(u, 1))));
                      u;
                    }));
              });
          });
      });
    val _ : ()
      = std/core/hnd/evv-set(w);
    val x@11897 : int
      = (match ((std/core/hnd/yielding())) {
        ((std/core/types/True() : bool ) as @pat@1@1: bool)
           -> std/core/hnd/yield-cont((forall<b> fn<<async|e>>(cont: (b) -> <async|e> int, res: b){
            std/core/hnd/open-at1(i@11900, cont, res);
          }));
        ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
           -> y;
      });
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat@4: bool)
         -> std/core/hnd/yield-extend((fn<<async|e>>(cid: int){
          (std/async/async/@mlift-cancelable@11408(action, cid));
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0@2: bool)
         -> val extend@0 : (scope : scope) -> scope
                  = fn(scope: scope){
                    (match (scope) {
                      ((@skip std/async/async/Scope((cids: list<int>)) : scope ) as @pat@3@0: scope)
                         -> std/async/async/Scope((std/core/types/Cons(x@11897, cids)));
                    });
                  };
        std/async/async/async/@handle((std/async/async/@Hnd-async(1, (forall<b> std/core/hnd/clause-tail1((fn<<async|e>>(f@1: () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) b){
              val i@0@11906 : (hnd/ev-index == 1 ssize_t)
                = (std/core/hnd/@evv-index(std/async/async/async/@tag));
              val w@0 : (hnd/evv<<async|e>>)
                = (std/core/hnd/evv-swap-create1(i@0@11906));
              val ev@0@11909 : (hnd/ev<async>)
                = (std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0))));
              val y@0 : b
                = (match (ev@0@11909) {
                  ((@skip std/core/hnd/Ev<e1,c>((@pat@0@3: hnd/htag<async>), (m@0: hnd/marker<e1,c>), (h@0: async<e1,c>), (@pat@1@1@0: hnd/evv<e1>)) : hnd/ev<async> ) as @pat@5: (hnd/ev<async>))
                     -> (match (h@0) {
                      ((@skip std/async/async/@Hnd-async((@pat@0@4: int), (@ctl-async-iox@0: forall<d> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) d,d,async,e1,c>), (@pat@1@2: hnd/clause1<scope,(),async,e1,c>), (@pat@2@1: forall<d> hnd/clause1<((await-setup<d> == 4 (cb : (error<d>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<
   global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<d>,async,e1,c>), (@pat@3@1: (forall<d> hnd/clause1<((await-setup<d> == 4 (cb : (error<d>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,
   (st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<d>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<
   global>>)>)>) ()),(),async,e1,c>))) : async<e1,c> ) as @pat@6: (async<e1,c>))
                         -> (match (@ctl-async-iox@0) {
                          ((@skip std/core/hnd/Clause1((f@3: (hnd/marker<e1,c>, hnd/ev<async>, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) b) -> e1 b)) : hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) b,b,async,e1,c> ) as @pat@2@1@0: (hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,
   net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) b,b,async,e1,c>))
                             -> f@3(m@0, ev@0@11909, f@1);
                        });
                    });
                });
              val _ : ()
                = (std/core/hnd/evv-set(w@0));
              (match ((std/core/hnd/yielding())) {
                ((std/core/types/True() : bool ) as @pat@4@0: bool)
                   -> std/core/hnd/yield-cont((forall<c> fn<<async|e>>(cont@0: (c) -> <async|e> b, res@0: c){
                    std/core/hnd/open-at1(i@0@11906, cont@0, res@0);
                  }));
                ((@skip std/core/types/False() : bool ) as @pat@0@2@0: bool)
                   -> y@0;
              });
            }))), (std/core/hnd/clause-tail1((fn<<async|e>>(scope@0@0: scope){
              val @x-x1@1@11300 : scope
                = (std/core/hnd/@open-none1(extend@0, scope@0@0));
              val i@1@11912 : (hnd/ev-index == 1 ssize_t)
                = (std/core/hnd/@evv-index(std/async/async/async/@tag));
              val w@1 : (hnd/evv<<async|e>>)
                = (std/core/hnd/evv-swap-create1(i@1@11912));
              val ev@1@11915 : (hnd/ev<async>)
                = (std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0))));
              val y@1 : ()
                = (match (ev@1@11915) {
                  ((@skip std/core/hnd/Ev<e1,b>((@pat@0@5: hnd/htag<async>), (m@1: hnd/marker<e1,b>), (h@1: async<e1,b>), (@pat@1@2@0: hnd/evv<e1>)) : hnd/ev<async> ) as @pat@7: (hnd/ev<async>))
                     -> (match (h@1) {
                      ((@skip std/async/async/@Hnd-async((@pat@0@6: int), (@pat@1@3: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e1,b>), (@ctl-cancel: hnd/clause1<scope,(),async,e1,b>), (@pat@2@2: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,
   alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e1,b>), (@pat@3@2: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<
   global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>
   >)>)>) ()),(),async,e1,b>))) : async<e1,b> ) as @pat@8: (async<e1,b>))
                         -> (match (@ctl-cancel) {
                          ((@skip std/core/hnd/Clause1((f@5: (hnd/marker<e1,b>, hnd/ev<async>, scope) -> e1 ())) : hnd/clause1<scope,(),async,e1,b> ) as @pat@2@2@0: (hnd/clause1<scope,(),async,e1,b>))
                             -> f@5(m@1, ev@1@11915, @x-x1@1@11300);
                        });
                    });
                });
              val _ : ()
                = (std/core/hnd/evv-set(w@1));
              (match ((std/core/hnd/yielding())) {
                ((std/core/types/True() : bool ) as @pat@6@0: bool)
                   -> std/core/hnd/yield-cont((forall<b> fn<<async|e>>(cont@1: (b) -> <async|e> (), res@1: b){
                    std/core/hnd/open-at1(i@1@11912, cont@1, res@1);
                  }));
                ((@skip std/core/types/False() : bool ) as @pat@0@4@0: bool)
                   -> y@1;
              });
            }))), (forall<b> std/core/hnd/clause-tail3((fn<<async|e>>(setup: (await-setup<b> == 4 (cb : (error<b>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,
   write<global>,alloc<global>>)>)>) ()>), scope@1@0: scope, c: bool){
              val @x-x2@11303 : scope
                = (std/core/hnd/@open-none1(extend@0, scope@1@0));
              val i@2@11918 : (hnd/ev-index == 1 ssize_t)
                = (std/core/hnd/@evv-index(std/async/async/async/@tag));
              val w@2 : (hnd/evv<<async|e>>)
                = (std/core/hnd/evv-swap-create1(i@2@11918));
              val ev@2@11923 : (hnd/ev<async>)
                = (std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0))));
              val y@2 : (error<b>)
                = (match (ev@2@11923) {
                  ((@skip std/core/hnd/Ev<e1,c>((@pat@0@7: hnd/htag<async>), (m@2: hnd/marker<e1,c>), (h@2: async<e1,c>), (@pat@1@3@0: hnd/evv<e1>)) : hnd/ev<async> ) as @pat@9: (hnd/ev<async>))
                     -> (match (h@2) {
                      ((@skip std/async/async/@Hnd-async((@pat@0@8: int), (@pat@1@4: forall<d> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) d,d,async,e1,c>), (@pat@2@3: hnd/clause1<scope,(),async,e1,c>), (@ctl-do-await: forall<d> hnd/clause1<((await-setup<d> == 4 (cb : (error<d>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,
   alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<d>,async,e1,c>), (@pat@3@3: (forall<d> hnd/clause1<((await-setup<d> == 4 (cb : (error<d>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<
   global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<d>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>
   >)>)>) ()),(),async,e1,c>))) : async<e1,c> ) as @pat@10: (async<e1,c>))
                         -> (match (@ctl-do-await) {
                          ((@skip std/core/hnd/Clause1((f@7: (hnd/marker<e1,c>, hnd/ev<async>, ((await-setup<b> == 4 (cb : (error<b>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global>
   == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool)) -> e1 error<b>)) : hnd/clause1<((await-setup<b> == 4 (cb : (error<b>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,
   (st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<b>,async,e1,c> ) as @pat@2@3@0: (hnd/clause1<((await-setup<b> == 4 (cb : (error<b>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <
   ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<b>,async,e1,c>))
                             -> f@7(m@2, ev@2@11923, (std/core/types/Tuple3(setup, @x-x2@11303, c)));
                        });
                    });
                });
              val _ : ()
                = (std/core/hnd/evv-set(w@2));
              (match ((std/core/hnd/yielding())) {
                ((std/core/types/True() : bool ) as @pat@8@0: bool)
                   -> std/core/hnd/yield-cont((forall<c> fn<<async|e>>(cont@2: (c) -> <async|e> error<b>, res@2: c){
                    std/core/hnd/open-at1(i@2@11918, cont@2, res@2);
                  }));
                ((@skip std/core/types/False() : bool ) as @pat@0@6@0: bool)
                   -> y@2;
              });
            }))), (forall<b> std/core/hnd/clause-tail4((fn<<async|e>>(setup@0@0: (await-setup<b> == 4 (cb : (error<b>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()>), scope@2@0: scope, c@0: bool, f@0@0: (error<b>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()){
              val @x-x2@0@11307 : scope
                = (std/core/hnd/@open-none1(extend@0, scope@2@0));
              val i@3@11928 : (hnd/ev-index == 1 ssize_t)
                = (std/core/hnd/@evv-index(std/async/async/async/@tag));
              val w@3 : (hnd/evv<<async|e>>)
                = (std/core/hnd/evv-swap-create1(i@3@11928));
              val ev@3@11934 : (hnd/ev<async>)
                = (std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0))));
              val y@3 : ()
                = (match (ev@3@11934) {
                  ((@skip std/core/hnd/Ev<e1,c>((@pat@0@9: hnd/htag<async>), (m@3: hnd/marker<e1,c>), (h@3: async<e1,c>), (@pat@1@4@0: hnd/evv<e1>)) : hnd/ev<async> ) as @pat@11: (hnd/ev<async>))
                     -> (match (h@3) {
                      ((@skip std/async/async/@Hnd-async((@pat@0@10: int), (@pat@1@5: forall<d> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) d,d,async,e1,c>), (@pat@2@4: hnd/clause1<scope,(),async,e1,c>), (@pat@3@4: forall<d> hnd/clause1<((await-setup<d> == 4 (cb : (error<d>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,
   alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<d>,async,e1,c>), (@ctl-no-await: (forall<d> hnd/clause1<((await-setup<d> == 4 (cb : (error<d>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st
   <global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<d>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global
   >>)>)>) ()),(),async,e1,c>))) : async<e1,c> ) as @pat@12: (async<e1,c>))
                         -> (match (@ctl-no-await) {
                          ((@skip std/core/hnd/Clause1((f@9: (hnd/marker<e1,c>, hnd/ev<async>, ((await-setup<b> == 4 (cb : (error<b>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global>
   == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<b>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())) -> e1 ())) : hnd/clause1<((await-setup<b> == 4 (cb : (error<b>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,
   (st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<b>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async,e1,c> ) as @pat@2@4@0: (hnd/clause1<((await-setup<b> == 4 (cb : (error<b>, bool) -> (io-noexn == 3 <div,(io-total == 
   2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<b>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <
   read<global>,write<global>,alloc<global>>)>)>) ()),(),async,e1,c>))
                             -> f@9(m@3, ev@3@11934, (std/core/types/Tuple4(setup@0@0, @x-x2@0@11307, c@0, f@0@0)));
                        });
                    });
                });
              val _ : ()
                = (std/core/hnd/evv-set(w@3));
              (match ((std/core/hnd/yielding())) {
                ((std/core/types/True() : bool ) as @pat@10@0: bool)
                   -> std/core/hnd/yield-cont((forall<c> fn<<async|e>>(cont@3: (c) -> <async|e> (), res@3: c){
                    std/core/hnd/open-at1(i@3@11928, cont@3, res@3);
                  }));
                ((@skip std/core/types/False() : bool ) as @pat@0@8@0: bool)
                   -> y@3;
              });
            }))))), (fn<<async|e>>(x@0@0: a){
            val @x-x1@7@11311 : scope
              = (std/core/hnd/@open-none1(extend@0, std/async/async/empty-scope));
            val i@4@11942 : (hnd/ev-index == 1 ssize_t)
              = (std/core/hnd/@evv-index(std/async/async/async/@tag));
            val w@4 : (hnd/evv<<async|e>>)
              = (std/core/hnd/evv-swap-create1(i@4@11942));
            val ev@4@11945 : (hnd/ev<async>)
              = (std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0))));
            val y@4 : ()
              = (match (ev@4@11945) {
                ((@skip std/core/hnd/Ev<e1,b>((@pat@0@12: hnd/htag<async>), (m@4: hnd/marker<e1,b>), (h@4: async<e1,b>), (@pat@1@5@0: hnd/evv<e1>)) : hnd/ev<async> ) as @pat@14: (hnd/ev<async>))
                   -> (match (h@4) {
                    ((@skip std/async/async/@Hnd-async((@pat@0@11: int), (@pat@1@6: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e1,b>), (@ctl-cancel@0: hnd/clause1<scope,(),async,e1,b>), (@pat@2@5: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,
   alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e1,b>), (@pat@3@5: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<
   global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>
   >)>)>) ()),(),async,e1,b>))) : async<e1,b> ) as @pat@13: (async<e1,b>))
                       -> (match (@ctl-cancel@0) {
                        ((@skip std/core/hnd/Clause1((f@11: (hnd/marker<e1,b>, hnd/ev<async>, scope) -> e1 ())) : hnd/clause1<scope,(),async,e1,b> ) as @pat@2@5@0: (hnd/clause1<scope,(),async,e1,b>))
                           -> f@11(m@4, ev@4@11945, @x-x1@7@11311);
                      });
                  });
              });
            val _ : ()
              = (std/core/hnd/evv-set(w@4));
            val x@6@11940 : ()
              = (match ((std/core/hnd/yielding())) {
                ((std/core/types/True() : bool ) as @pat@13@0: bool)
                   -> std/core/hnd/yield-cont((forall<b> fn<<async|e>>(cont@4: (b) -> <async|e> (), res@4: b){
                    std/core/hnd/open-at1(i@4@11942, cont@4, res@4);
                  }));
                ((@skip std/core/types/False() : bool ) as @pat@0@11@0: bool)
                   -> y@4;
              });
            (match ((std/core/hnd/yielding())) {
              ((std/core/types/True() : bool ) as @pat@12@0: bool)
                 -> std/core/hnd/yield-extend((fn<<async|e>>(wild_: ()){
                  x@0@0;
                }));
              ((@skip std/core/types/False() : bool ) as @pat@0@10@0: bool)
                 -> x@0@0;
            });
          }), (fn<<async,async|e>>(){
            val x@9@11950 : (hnd/ev-index == 1 ssize_t)
                  = (std/core/hnd/@evv-index(std/async/async/async/@tag));
            (match ((std/core/hnd/yielding())) {
              ((std/core/types/True() : bool ) as @pat@15: bool)
                 -> std/core/hnd/yield-extend((fn<<async,async|e>>(@y-x10945: (hnd/ev-index == 1 ssize_t)){
                  (std/async/async/@mlift-cancelable@11407(action, @y-x10945));
                }));
              ((@skip std/core/types/False() : bool ) as @pat@0@13: bool)
                 -> std/async/async/@mlift-cancelable@11407(action, x@9@11950);
            });
          }));
    });
  };
val @tag-Cancel : string
  = "std/async/async/Cancel";
val @tag-Finalize : string
  = "std/async/async/Finalize";
// Automatically generated. Tests for the `Finalize` constructor of the `:exception-info` type.
fip fun is-finalize : (^ exception-info : exception-info) -> bool
  = fn(exception-info: exception-info){
    match (exception-info) {
      ((std/async/async/Finalize((@pat@0: hnd/yield-info)) : exception-info ) as @pat: exception-info)
         -> std/core/types/True;
      (@pat@1: exception-info)
         -> std/core/types/False;
    };
  };
// Was this a finalization exception?
fun exn/is-finalize : (exn : exception) -> bool
  = fn(exn: exception){
    match (exn) {
      ((@skip std/core/exn/Exception((@pat@0: string), (@x: exception-info)) : exception ) as @pat: exception)
         -> (match (@x) {
          ((std/async/async/Finalize((@pat@0@0: hnd/yield-info)) : exception-info ) as @pat@1: exception-info)
             -> std/core/types/True;
          (@pat@1@0: exception-info)
             -> std/core/types/False;
        });
    };
  };
fun error/is-finalize : forall<a> (t : error<a>) -> bool
  = forall<a> fn(t: error<a>){
    (match (t) {
      ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0: string), (@pat@1: exception-info)) : exception ) as exn: exception)) : error<a> ) as @pat: (error<a>))
         -> (match (exn) {
          ((@skip std/core/exn/Exception((@pat@0@0: string), (@x: exception-info)) : exception ) as @pat@2: exception)
             -> (match (@x) {
              ((std/async/async/Finalize((@pat@0@1: hnd/yield-info)) : exception-info ) as @pat@3: exception-info)
                 -> std/core/types/True;
              (@pat@1@0: exception-info)
                 -> std/core/types/False;
            });
        });
      (@pat@2@0: (error<a>))
         -> std/core/types/False;
    });
  };
// monadic lift
fun @mlift-unsafe-try-all@11409 : forall<a,e> (fin : either<hnd/yield-info,error<a>>) -> e error<a>
  = forall<a,e> fn<e>(fin: either<hnd/yield-info,error<a>>){
    (match (fin) {
      ((std/core/types/Right((t: error<a>)) : either<hnd/yield-info,error<a>> ) as @pat: (either<hnd/yield-info,error<a>>))
         -> t;
      ((@skip std/core/types/Left((yld: hnd/yield-info)) : either<hnd/yield-info,error<a>> ) as @pat@0: (either<hnd/yield-info,error<a>>))
         -> std/core/exn/Error((std/core/exn/Exception("finalize", (std/async/async/Finalize(yld)))));
    });
  };
fun unsafe-try-all : forall<a,e> (action : () -> <exn|e> a) -> e error<a>
  = forall<a,e> fn<e>(action: () -> <exn|e> a){
    val x@11952 : either<hnd/yield-info,error<a>>
          = std/core/hnd/try-finalize-prompt((std/core/exn/error/try(action)));
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-extend((fn<e>(fin: either<hnd/yield-info,error<a>>){
          (match (fin) {
            ((std/core/types/Right((t: error<a>)) : either<hnd/yield-info,error<a>> ) as @pat@1: (either<hnd/yield-info,error<a>>))
               -> t;
            ((@skip std/core/types/Left((yld: hnd/yield-info)) : either<hnd/yield-info,error<a>> ) as @pat@0@0: (either<hnd/yield-info,error<a>>))
               -> std/core/exn/Error((std/core/exn/Exception("finalize", (std/async/async/Finalize(yld)))));
          });
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> (match (x@11952) {
          ((std/core/types/Right((t@0: error<a>)) : either<hnd/yield-info,error<a>> ) as @pat@2: (either<hnd/yield-info,error<a>>))
             -> t@0;
          ((@skip std/core/types/Left((yld@0: hnd/yield-info)) : either<hnd/yield-info,error<a>> ) as @pat@0@1: (either<hnd/yield-info,error<a>>))
             -> std/core/exn/Error((std/core/exn/Exception("finalize", (std/async/async/Finalize(yld@0)))));
        });
    });
  };
// monadic lift
fun @mlift-trmc-lift-interleaved-div@10758@11410 : forall<a,e> (res : error<a>, wild_ : ()) -> <strands<a>,async,div,ndet|e> ()
  = forall<a,e> fn<<strands<a>,async,div,ndet|e>>(res: error<a>, wild_: ()){
    val w : hnd/evv<<async,strands<a>,div,ndet|e>>
      = std/core/hnd/evv-swap-create0();
    val keep : ()
      = std/core/hnd/evv-set(w);
    (match (res) {
      ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@0: string), (@pat@1@0: exception-info)) : exception ) as exn: exception)) : error<a> ) as @pat@1: (error<a>))
         -> (match (exn) {
          ((@skip std/core/exn/Exception((@pat@0@1: string), (@x: exception-info)) : exception ) as @pat@2: exception)
             -> (match (@x) {
              ((std/async/async/Finalize((@pat@0@2: hnd/yield-info)) : exception-info ) as @pat@3: exception-info)
                 -> val i@11959 : (hnd/ev-index == 1 ssize_t)
                      = std/core/hnd/@evv-index(std/async/async/async/@tag);
                    val w@0 : hnd/evv<<async,strands<a>,div,ndet|e>>
                      = std/core/hnd/evv-swap-create1(i@11959);
                    val ev@11961 : hnd/ev<async>
                      = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
                    val y : ()
                      = (match (ev@11961) {
                        ((@skip std/core/hnd/Ev<e1,b>((@pat@0@3: hnd/htag<async>), (m: hnd/marker<e1,b>), (h: async<e1,b>), (@pat@1@2: hnd/evv<e1>)) : hnd/ev<async> ) as @pat@5: (hnd/ev<async>))
                           -> (match (h) {
                            ((@skip std/async/async/@Hnd-async((@pat@0: int), (@pat@1@3: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e1,b>), (@ctl-cancel: hnd/clause1<scope,(),async,e1,b>), (@pat@2@1: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global
   >,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e1,b>), (@pat@3@0: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<
   global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>
   >)>)>) ()),(),async,e1,b>))) : async<e1,b> ) as @pat: (async<e1,b>))
                               -> (match (@ctl-cancel) {
                                ((@skip std/core/hnd/Clause1((f@1: (hnd/marker<e1,b>, hnd/ev<async>, scope) -> e1 ())) : hnd/clause1<scope,(),async,e1,b> ) as @pat@2@1@0: (hnd/clause1<scope,(),async,e1,b>))
                                   -> f@1(m, ev@11961, std/async/async/empty-scope);
                              });
                          });
                      });
                    val _ : ()
                      = std/core/hnd/evv-set(w@0);
                (match ((std/core/hnd/yielding())) {
                  ((std/core/types/True() : bool ) as @pat@6: bool)
                     -> std/core/hnd/yield-cont((forall<b> fn<<async,strands<a>,div,ndet|e>>(cont: (b) -> <async,strands<a>,div,ndet|e> (), res@0: b){
                      std/core/hnd/open-at1(i@11959, cont, res@0);
                    }));
                  ((@skip std/core/types/False() : bool ) as @pat@0@4: bool)
                     -> y;
                });
              (@pat@1@1: exception-info)
                 -> std/core/types/Unit;
            });
        });
      (@pat@2@0: (error<a>))
         -> std/core/types/Unit;
    });
  };
// monadic lift
fun @mlift-trmc-lift-interleaved-div@10758@11411 : forall<a,e> (@uniq-i@10618 : int, fin : either<hnd/yield-info,error<a>>) -> <div,ndet,strands<a>,async|e> ()
  = forall<a,e> fn<<div,ndet,strands<a>,async|e>>(@uniq-i@10618: int, fin: either<hnd/yield-info,error<a>>){
    val res@1 : error<a>
      = (match (fin) {
        ((std/core/types/Right((t: error<a>)) : either<hnd/yield-info,error<a>> ) as @pat@6@0: (either<hnd/yield-info,error<a>>))
           -> t;
        ((@skip std/core/types/Left((yld: hnd/yield-info)) : either<hnd/yield-info,error<a>> ) as @pat@0@4@0: (either<hnd/yield-info,error<a>>))
           -> std/core/exn/Error((std/core/exn/Exception("finalize", (std/async/async/Finalize(yld)))));
      });
    val i@0@11966 : hnd/ev-index
      = std/core/hnd/@evv-index(std/async/async/strands/@tag);
    val w@1 : hnd/evv<<strands<a>,async,div,ndet|e>>
      = std/core/hnd/evv-swap-create1(i@0@11966);
    val evx@11970 : hnd/ev<strands<a>>
      = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
    val y@0 : ()
      = (match (evx@11970) {
        ((@skip std/core/hnd/Ev<e1,b>((@pat@0@7: hnd/htag<strands<a>>), (m@0: hnd/marker<e1,b>), (h@0: (strands<a>)<e1,b>), (@pat@1@3@0: hnd/evv<e1>)) : hnd/ev<strands<a>> ) as @pat@9: (hnd/ev<strands<a>>))
           -> (match (h@0) {
            ((@skip std/async/async/@Hnd-strands((@pat@0@5: int), (@fun-strand-done: hnd/clause2<int,error<a>,(),strands<a>,e1,b>), (@pat@1@4: hnd/clause0<bool,strands<a>,e1,b>)) : strands<a,e1,b> ) as @pat@7: (strands<a,e1,b>))
               -> (match (@fun-strand-done) {
                ((@skip std/core/hnd/Clause2((f@3: (hnd/marker<e1,b>, hnd/ev<strands<a>>, int, error<a>) -> e1 ())) : hnd/clause2<int,error<a>,(),strands<a>,e1,b> ) as @pat@2@2: (hnd/clause2<int,error<a>,(),strands<a>,e1,b>))
                   -> f@3(m@0, evx@11970, @uniq-i@10618, res@1);
              });
          });
      });
    val _ : ()
      = std/core/hnd/evv-set(w@1);
    val x@1@11964 : ()
      = (match ((std/core/hnd/yielding())) {
        ((std/core/types/True() : bool ) as @pat@8: bool)
           -> std/core/hnd/yield-cont((forall<b> fn<<strands<a>,async,div,ndet|e>>(cont@0: (b) -> <strands<a>,async,div,ndet|e> (), res@2: b){
            std/core/hnd/open-at1(i@0@11966, cont@0, res@2);
          }));
        ((@skip std/core/types/False() : bool ) as @pat@0@6: bool)
           -> y@0;
      });
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat@7@0: bool)
         -> std/core/hnd/yield-extend((fn<<strands<a>,async,div,ndet|e>>(wild_@0: ()){
          (std/async/async/@mlift-trmc-lift-interleaved-div@10758@11410(res@1, wild_@0));
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0@5@0: bool)
         -> std/async/async/@mlift-trmc-lift-interleaved-div@10758@11410(res@1, x@1@11964);
    });
  };
// monadic lift
fun @mlift-trmcm-lift-interleaved-div@10758@11412 : forall<a,e> (res : error<a>, wild_ : ()) -> <strands<a>,async,div,ndet|e> ()
  = forall<a,e> fn<<strands<a>,async,div,ndet|e>>(res@3: error<a>, wild_@1: ()){
    val w@2 : hnd/evv<<async,strands<a>,div,ndet|e>>
      = std/core/hnd/evv-swap-create0();
    val keep@0 : ()
      = std/core/hnd/evv-set(w@2);
    (match (res@3) {
      ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@0@0: string), (@pat@1@0@0: exception-info)) : exception ) as exn@0: exception)) : error<a> ) as @pat@1@4@0: (error<a>))
         -> (match (exn@0) {
          ((@skip std/core/exn/Exception((@pat@0@1@0: string), (@x@0: exception-info)) : exception ) as @pat@2@3: exception)
             -> (match (@x@0) {
              ((std/async/async/Finalize((@pat@0@2@0: hnd/yield-info)) : exception-info ) as @pat@3@0@0: exception-info)
                 -> val i@1@11976 : (hnd/ev-index == 1 ssize_t)
                      = std/core/hnd/@evv-index(std/async/async/async/@tag);
                    val w@3 : hnd/evv<<async,strands<a>,div,ndet|e>>
                      = std/core/hnd/evv-swap-create1(i@1@11976);
                    val ev@0@11978 : hnd/ev<async>
                      = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
                    val y@2 : ()
                      = (match (ev@0@11978) {
                        ((@skip std/core/hnd/Ev<e1,b>((@pat@0@9: hnd/htag<async>), (m@1: hnd/marker<e1,b>), (h@1: async<e1,b>), (@pat@1@5: hnd/evv<e1>)) : hnd/ev<async> ) as @pat@11: (hnd/ev<async>))
                           -> (match (h@1) {
                            ((@skip std/async/async/@Hnd-async((@pat@0@8: int), (@pat@1@6: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e1,b>), (@ctl-cancel@0: hnd/clause1<scope,(),async,e1,b>), (@pat@2@4: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<
   global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e1,b>), (@pat@3@1: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,
   (st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<
   global>>)>)>) ()),(),async,e1,b>))) : async<e1,b> ) as @pat@10: (async<e1,b>))
                               -> (match (@ctl-cancel@0) {
                                ((@skip std/core/hnd/Clause1((f@6: (hnd/marker<e1,b>, hnd/ev<async>, scope) -> e1 ())) : hnd/clause1<scope,(),async,e1,b> ) as @pat@2@4@0: (hnd/clause1<scope,(),async,e1,b>))
                                   -> f@6(m@1, ev@0@11978, std/async/async/empty-scope);
                              });
                          });
                      });
                    val _ : ()
                      = std/core/hnd/evv-set(w@3);
                (match ((std/core/hnd/yielding())) {
                  ((std/core/types/True() : bool ) as @pat@10@0: bool)
                     -> std/core/hnd/yield-cont((forall<b> fn<<async,strands<a>,div,ndet|e>>(cont@1: (b) -> <async,strands<a>,div,ndet|e> (), res@4: b){
                      std/core/hnd/open-at1(i@1@11976, cont@1, res@4);
                    }));
                  ((@skip std/core/types/False() : bool ) as @pat@0@8@0: bool)
                     -> y@2;
                });
              (@pat@1@1@0: exception-info)
                 -> std/core/types/Unit;
            });
        });
      (@pat@2@0@0: (error<a>))
         -> std/core/types/Unit;
    });
  };
// monadic lift
fun @mlift-trmcm-lift-interleaved-div@10758@11413 : forall<a,e> (@uniq-i@10618 : int, fin : either<hnd/yield-info,error<a>>) -> <div,ndet,strands<a>,async|e> ()
  = forall<a,e> fn<<div,ndet,strands<a>,async|e>>(@uniq-i@10618@0: int, fin@0: either<hnd/yield-info,error<a>>){
    val res@5 : error<a>
      = (match (fin@0) {
        ((std/core/types/Right((t@1: error<a>)) : either<hnd/yield-info,error<a>> ) as @pat@12: (either<hnd/yield-info,error<a>>))
           -> t@1;
        ((@skip std/core/types/Left((yld@0: hnd/yield-info)) : either<hnd/yield-info,error<a>> ) as @pat@0@10: (either<hnd/yield-info,error<a>>))
           -> std/core/exn/Error((std/core/exn/Exception("finalize", (std/async/async/Finalize(yld@0)))));
      });
    val i@2@11983 : hnd/ev-index
      = std/core/hnd/@evv-index(std/async/async/strands/@tag);
    val w@4 : hnd/evv<<strands<a>,async,div,ndet|e>>
      = std/core/hnd/evv-swap-create1(i@2@11983);
    val evx@0@11987 : hnd/ev<strands<a>>
      = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
    val y@3 : ()
      = (match (evx@0@11987) {
        ((@skip std/core/hnd/Ev<e1,b>((@pat@0@13: hnd/htag<strands<a>>), (m@2: hnd/marker<e1,b>), (h@2: (strands<a>)<e1,b>), (@pat@1@6@0: hnd/evv<e1>)) : hnd/ev<strands<a>> ) as @pat@15: (hnd/ev<strands<a>>))
           -> (match (h@2) {
            ((@skip std/async/async/@Hnd-strands((@pat@0@11: int), (@fun-strand-done@0: hnd/clause2<int,error<a>,(),strands<a>,e1,b>), (@pat@1@7: hnd/clause0<bool,strands<a>,e1,b>)) : strands<a,e1,b> ) as @pat@13: (strands<a,e1,b>))
               -> (match (@fun-strand-done@0) {
                ((@skip std/core/hnd/Clause2((f@8: (hnd/marker<e1,b>, hnd/ev<strands<a>>, int, error<a>) -> e1 ())) : hnd/clause2<int,error<a>,(),strands<a>,e1,b> ) as @pat@2@5: (hnd/clause2<int,error<a>,(),strands<a>,e1,b>))
                   -> f@8(m@2, evx@0@11987, @uniq-i@10618@0, res@5);
              });
          });
      });
    val _ : ()
      = std/core/hnd/evv-set(w@4);
    val x@5@11981 : ()
      = (match ((std/core/hnd/yielding())) {
        ((std/core/types/True() : bool ) as @pat@14: bool)
           -> std/core/hnd/yield-cont((forall<b> fn<<strands<a>,async,div,ndet|e>>(cont@2: (b) -> <strands<a>,async,div,ndet|e> (), res@6: b){
            std/core/hnd/open-at1(i@2@11983, cont@2, res@6);
          }));
        ((@skip std/core/types/False() : bool ) as @pat@0@12: bool)
           -> y@3;
      });
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat@13@0: bool)
         -> std/core/hnd/yield-extend((fn<<strands<a>,async,div,ndet|e>>(wild_@2: ()){
          (std/async/async/@mlift-trmcm-lift-interleaved-div@10758@11412(res@5, wild_@2));
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0@11@0: bool)
         -> std/async/async/@mlift-trmcm-lift-interleaved-div@10758@11412(res@5, x@5@11981);
    });
  };
// lifted local: @lift-interleaved-div@10757, interleaved-div, @spec-x10626
// specialized: std/core/list/@unroll-lift-map-indexed@5731@10011, on parameters @uniq-f@10616, using:
// @uniq-f@10616 = (fn<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>>(i: int, action: () -> <(std/async/async/async-exn :: E)|(6668 :: E)> 6667){
//   fn<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>>(){
//     val action@0@10126 : () -> <(exn :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>,(std/async/async/async :: (E, V) -> V)|(e :: E)> a;
//     val fin : (either :: (V, V) -> V)<hnd/yield-info,(error :: V -> V)<a>>;
//     val res : (error :: V -> V)<a>;
//     val _ : ();
//     match ((std/core/types/@open<(total :: E),<(std/async/async/async :: (E, V) -> V),(std/async/async/strands :: (V, E, V) -> V)<a>,(div :: X),(ndet :: X)|(e :: E)>,(t : (error :: V -> V)<a>) -> bool,(t : (error :: V -> V)<a>) -> <(std/async/async/async :: (E, V) -> V),(std/async/async/strands :: (V, E, V) -> V)<a>,(div :: X),(ndet :: X)|(e :: E)> bool>((fn(t@0: (error :: V -> V)<6667>){
//       (match (t@0) {
//         ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@0: string) : string, (@pat@1@0: exception-info) : exception-info) : exception ) as exn: exception) : exception) : (error :: V -> V)<a> ) as @pat@1: ((error :: V -> V)<6667>))
//            -> (match (exn) {
//             ((@skip std/core/exn/Exception((@pat@0@1: string) : string, (@x: exception-info) : exception-info) : exception ) as @pat@2: exception)
//                -> (match (@x) {
//                 ((std/async/async/Finalize((@pat@0@2: hnd/yield-info) : hnd/yield-info) : exception-info ) as @pat@3: exception-info)
//                    -> std/core/types/True;
//                 (@pat@1@1: exception-info)
//                    -> std/core/types/False;
//               });
//           });
//         (@pat@2@0: ((error :: V -> V)<6667>))
//            -> std/core/types/False;
//       });
//     }))(res))) {
//       ((std/core/types/True() : bool ) as @pat@4: bool)
//          -> std/core/types/@open<(std/async/async/async :: (E, V) -> V),<(std/async/async/async :: (E, V) -> V),(std/async/async/strands :: (V, E, V) -> V)<a>,(div :: X),(ndet :: X)|(e :: E)>,() -> (std/async/async/async :: (E, V) -> V) (),() -> <(std/async/async/async :: (E, V) -> V),(std/async/async/strands :: (V, E, V) -> V)<a>,(div :: X),(ndet :: X)|(e :: E)> ()>((fn<(std/async/async/async :: (E, V) -> V)>(){
//           (std/core/hnd/@perform1<std/async/async/scope,(),(std/async/async/async :: (E, V) -> V),(std/async/async/async :: (E, V) -> V)>((std/core/types/@open<(total :: E),(std/async/async/async :: (E, V) -> V),(i : (hnd/ev-index == 1 ssize_t)) -> (hnd/ev :: ((E, V) -> V) -> V)<(std/async/async/async :: (E, V) -> V)>,(i : (hnd/ev-index == 1 ssize_t)) -> (std/async/async/async :: (E, V) -> V) (hnd/ev :: ((E, V) -> V) -> V)<(std/async/async/async :: (E, V) -> V)>>((std/core/hnd/@evv-at<(std/async/async/async :: (E, V) -> V)>))((std/core/types/@open<(total :: E),(std/async/async/async :: (E, V) -> V),(i : int) -> ssize_t,(i : int) -> (std/async/async/async :: (E, V) -> V) ssize_t>(std/core/types/@make-ssize_t)(0)))), std/async/async/cancel/@select, std/async/async/empty-scope));
//         }))();
//       ((@skip std/core/types/False() : bool ) as @pat@0@3: bool)
//          -> std/core/types/Unit;
//     };
//   };
// },Own)
fun @trmc-lift-interleaved-div@10758 : forall<_a,b,e> (@uniq-ys@10617 : list<() -> <async-exn|e> b>, @uniq-i@10618 : int, @acc : ctx<list<() -> <async,div,ndet,strands<b>|e> ()>>) -> <async,div,ndet,strands<b>|e> list<() -> <async,div,ndet,strands<b>|e> ()>
  = forall<_a,b,e> fn<<async,div,ndet,strands<b>|e>>(@uniq-ys@10617: list<() -> <async-exn|e> b>, @uniq-i@10618@1: int, @acc: ctx<list<() -> <async,div,ndet,strands<b>|e> ()>>){
    (match (@uniq-ys@10617) {
      ((std/core/types/Cons((@uniq-y@10620: () -> <(async-exn == 1 <async,exn>)|e> b), (@uniq-yy@10621: list<() -> <(async-exn == 1 <async,exn>)|e> b>)) : list<() -> <(async-exn == 1 <async,exn>)|e> b> ) as @uniq-pat@10619: (list<() -> <(async-exn == 1 <async,exn>)|e> b>))
         -> val @uniq-i@0@10077@10624 : int
              = std/core/int/int-add(@uniq-i@10618@1, 1);
            val @trmc-x10808 : list<() -> <async,div,ndet,strands<b>|e> ()>
              = std/core/types/@cctx-hole-create();
            val @trmc-x10809 : list<() -> <async,div,ndet,strands<b>|e> ()>
              = std/core/types/Cons((fn<<async,div,ndet,strands<b>|e>>(){
                  val x@7@11991 : (either<hnd/yield-info,error<b>>)
                        = (std/core/hnd/try-finalize-prompt((std/core/exn/error/try(@uniq-y@10620))));
                  (match ((std/core/hnd/yielding())) {
                    ((std/core/types/True() : bool ) as @pat@16: bool)
                       -> std/core/hnd/yield-extend((fn<<div,ndet,strands<b>,async|e>>(fin@1: either<hnd/yield-info,error<b>>){
                        (std/async/async/@mlift-trmc-lift-interleaved-div@10758@11411(@uniq-i@10618@1, fin@1));
                      }));
                    ((@skip std/core/types/False() : bool ) as @pat@0@14: bool)
                       -> std/async/async/@mlift-trmc-lift-interleaved-div@10758@11411(@uniq-i@10618@1, x@7@11991);
                  });
                }), @trmc-x10808);
        std/async/async/@trmc-lift-interleaved-div@10758(@uniq-yy@10621, @uniq-i@0@10077@10624, (std/core/types/@cctx-extend(@acc, @trmc-x10809, (std/core/types/@field-addr-of(@trmc-x10809, "(\x22std/core/types\x22,\x22\x22,\x22Cons\x22)", "(\x22\x22,\x22\x22,\x22tail\x22)")))));
      ((@skip std/core/types/Nil() : list<() -> <(async-exn == 1 <async,exn>)|e> b> ) as @uniq-pat@0@10625: (list<() -> <(async-exn == 1 <async,exn>)|e> b>))
         -> std/core/types/cctx/((++.))(@acc, std/core/types/Nil);
    });
  };
// lifted local: @lift-interleaved-div@10757, interleaved-div, @spec-x10626
// specialized: std/core/list/@unroll-lift-map-indexed@5731@10011, on parameters @uniq-f@10616, using:
// @uniq-f@10616 = (fn<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>>(i: int, action: () -> <(std/async/async/async-exn :: E)|(6668 :: E)> 6667){
//   fn<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>>(){
//     val action@0@10126 : () -> <(exn :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>,(std/async/async/async :: (E, V) -> V)|(e :: E)> a;
//     val fin : (either :: (V, V) -> V)<hnd/yield-info,(error :: V -> V)<a>>;
//     val res : (error :: V -> V)<a>;
//     val _ : ();
//     match ((std/core/types/@open<(total :: E),<(std/async/async/async :: (E, V) -> V),(std/async/async/strands :: (V, E, V) -> V)<a>,(div :: X),(ndet :: X)|(e :: E)>,(t : (error :: V -> V)<a>) -> bool,(t : (error :: V -> V)<a>) -> <(std/async/async/async :: (E, V) -> V),(std/async/async/strands :: (V, E, V) -> V)<a>,(div :: X),(ndet :: X)|(e :: E)> bool>((fn(t@0: (error :: V -> V)<6667>){
//       (match (t@0) {
//         ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@0: string) : string, (@pat@1@0: exception-info) : exception-info) : exception ) as exn: exception) : exception) : (error :: V -> V)<a> ) as @pat@1: ((error :: V -> V)<6667>))
//            -> (match (exn) {
//             ((@skip std/core/exn/Exception((@pat@0@1: string) : string, (@x: exception-info) : exception-info) : exception ) as @pat@2: exception)
//                -> (match (@x) {
//                 ((std/async/async/Finalize((@pat@0@2: hnd/yield-info) : hnd/yield-info) : exception-info ) as @pat@3: exception-info)
//                    -> std/core/types/True;
//                 (@pat@1@1: exception-info)
//                    -> std/core/types/False;
//               });
//           });
//         (@pat@2@0: ((error :: V -> V)<6667>))
//            -> std/core/types/False;
//       });
//     }))(res))) {
//       ((std/core/types/True() : bool ) as @pat@4: bool)
//          -> std/core/types/@open<(std/async/async/async :: (E, V) -> V),<(std/async/async/async :: (E, V) -> V),(std/async/async/strands :: (V, E, V) -> V)<a>,(div :: X),(ndet :: X)|(e :: E)>,() -> (std/async/async/async :: (E, V) -> V) (),() -> <(std/async/async/async :: (E, V) -> V),(std/async/async/strands :: (V, E, V) -> V)<a>,(div :: X),(ndet :: X)|(e :: E)> ()>((fn<(std/async/async/async :: (E, V) -> V)>(){
//           (std/core/hnd/@perform1<std/async/async/scope,(),(std/async/async/async :: (E, V) -> V),(std/async/async/async :: (E, V) -> V)>((std/core/types/@open<(total :: E),(std/async/async/async :: (E, V) -> V),(i : (hnd/ev-index == 1 ssize_t)) -> (hnd/ev :: ((E, V) -> V) -> V)<(std/async/async/async :: (E, V) -> V)>,(i : (hnd/ev-index == 1 ssize_t)) -> (std/async/async/async :: (E, V) -> V) (hnd/ev :: ((E, V) -> V) -> V)<(std/async/async/async :: (E, V) -> V)>>((std/core/hnd/@evv-at<(std/async/async/async :: (E, V) -> V)>))((std/core/types/@open<(total :: E),(std/async/async/async :: (E, V) -> V),(i : int) -> ssize_t,(i : int) -> (std/async/async/async :: (E, V) -> V) ssize_t>(std/core/types/@make-ssize_t)(0)))), std/async/async/cancel/@select, std/async/async/empty-scope));
//         }))();
//       ((@skip std/core/types/False() : bool ) as @pat@0@3: bool)
//          -> std/core/types/Unit;
//     };
//   };
// },Own)
fun @trmcm-lift-interleaved-div@10758 : forall<_a,b,e> (@uniq-ys@10617 : list<() -> <async-exn|e> b>, @uniq-i@10618 : int, @accm : (list<() -> <async,div,ndet,strands<b>|e> ()>) -> list<() -> <async,div,ndet,strands<b>|e> ()>) -> <async,div,ndet,strands<b>|e> list<() -> <async,div,ndet,strands<b>|e> ()>
  = forall<_a,b,e> fn<<async,div,ndet,strands<b>|e>>(@uniq-ys@10617@0: list<() -> <async-exn|e> b>, @uniq-i@10618@2: int, @accm: (list<() -> <async,div,ndet,strands<b>|e> ()>) -> list<() -> <async,div,ndet,strands<b>|e> ()>){
    (match (@uniq-ys@10617@0) {
      ((std/core/types/Cons((@uniq-y@10620@0: () -> <(async-exn == 1 <async,exn>)|e> b), (@uniq-yy@10621@0: list<() -> <(async-exn == 1 <async,exn>)|e> b>)) : list<() -> <(async-exn == 1 <async,exn>)|e> b> ) as @uniq-pat@10619@0: (list<() -> <(async-exn == 1 <async,exn>)|e> b>))
         -> val @uniq-i@0@10077@10624@0 : int
                  = std/core/int/int-add(@uniq-i@10618@2, 1);
        std/async/async/@trmcm-lift-interleaved-div@10758(@uniq-yy@10621@0, @uniq-i@0@10077@10624@0, (fn(@trmc-x10811: list<() -> <async,div,ndet,strands<b>|e> ()>){
            (@accm((std/core/types/Cons((fn<<async,div,ndet,strands<b>|e>>(){
                val x@8@11994 : (either<hnd/yield-info,error<b>>)
                      = (std/core/hnd/try-finalize-prompt((std/core/exn/error/try(@uniq-y@10620@0))));
                (match ((std/core/hnd/yielding())) {
                  ((std/core/types/True() : bool ) as @pat@17: bool)
                     -> std/core/hnd/yield-extend((fn<<div,ndet,strands<b>,async|e>>(fin@2: either<hnd/yield-info,error<b>>){
                      (std/async/async/@mlift-trmcm-lift-interleaved-div@10758@11413(@uniq-i@10618@2, fin@2));
                    }));
                  ((@skip std/core/types/False() : bool ) as @pat@0@15: bool)
                     -> std/async/async/@mlift-trmcm-lift-interleaved-div@10758@11413(@uniq-i@10618@2, x@8@11994);
                });
              }), @trmc-x10811))));
          }));
      ((@skip std/core/types/Nil() : list<() -> <(async-exn == 1 <async,exn>)|e> b> ) as @uniq-pat@0@10625@0: (list<() -> <(async-exn == 1 <async,exn>)|e> b>))
         -> @accm(std/core/types/Nil);
    });
  };
// lifted local: @lift-interleaved-div@10757, interleaved-div, @spec-x10626
// specialized: std/core/list/@unroll-lift-map-indexed@5731@10011, on parameters @uniq-f@10616, using:
// @uniq-f@10616 = (fn<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>>(i: int, action: () -> <(std/async/async/async-exn :: E)|(6668 :: E)> 6667){
//   fn<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>>(){
//     val action@0@10126 : () -> <(exn :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>,(std/async/async/async :: (E, V) -> V)|(e :: E)> a;
//     val fin : (either :: (V, V) -> V)<hnd/yield-info,(error :: V -> V)<a>>;
//     val res : (error :: V -> V)<a>;
//     val _ : ();
//     match ((std/core/types/@open<(total :: E),<(std/async/async/async :: (E, V) -> V),(std/async/async/strands :: (V, E, V) -> V)<a>,(div :: X),(ndet :: X)|(e :: E)>,(t : (error :: V -> V)<a>) -> bool,(t : (error :: V -> V)<a>) -> <(std/async/async/async :: (E, V) -> V),(std/async/async/strands :: (V, E, V) -> V)<a>,(div :: X),(ndet :: X)|(e :: E)> bool>((fn(t@0: (error :: V -> V)<6667>){
//       (match (t@0) {
//         ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@0: string) : string, (@pat@1@0: exception-info) : exception-info) : exception ) as exn: exception) : exception) : (error :: V -> V)<a> ) as @pat@1: ((error :: V -> V)<6667>))
//            -> (match (exn) {
//             ((@skip std/core/exn/Exception((@pat@0@1: string) : string, (@x: exception-info) : exception-info) : exception ) as @pat@2: exception)
//                -> (match (@x) {
//                 ((std/async/async/Finalize((@pat@0@2: hnd/yield-info) : hnd/yield-info) : exception-info ) as @pat@3: exception-info)
//                    -> std/core/types/True;
//                 (@pat@1@1: exception-info)
//                    -> std/core/types/False;
//               });
//           });
//         (@pat@2@0: ((error :: V -> V)<6667>))
//            -> std/core/types/False;
//       });
//     }))(res))) {
//       ((std/core/types/True() : bool ) as @pat@4: bool)
//          -> std/core/types/@open<(std/async/async/async :: (E, V) -> V),<(std/async/async/async :: (E, V) -> V),(std/async/async/strands :: (V, E, V) -> V)<a>,(div :: X),(ndet :: X)|(e :: E)>,() -> (std/async/async/async :: (E, V) -> V) (),() -> <(std/async/async/async :: (E, V) -> V),(std/async/async/strands :: (V, E, V) -> V)<a>,(div :: X),(ndet :: X)|(e :: E)> ()>((fn<(std/async/async/async :: (E, V) -> V)>(){
//           (std/core/hnd/@perform1<std/async/async/scope,(),(std/async/async/async :: (E, V) -> V),(std/async/async/async :: (E, V) -> V)>((std/core/types/@open<(total :: E),(std/async/async/async :: (E, V) -> V),(i : (hnd/ev-index == 1 ssize_t)) -> (hnd/ev :: ((E, V) -> V) -> V)<(std/async/async/async :: (E, V) -> V)>,(i : (hnd/ev-index == 1 ssize_t)) -> (std/async/async/async :: (E, V) -> V) (hnd/ev :: ((E, V) -> V) -> V)<(std/async/async/async :: (E, V) -> V)>>((std/core/hnd/@evv-at<(std/async/async/async :: (E, V) -> V)>))((std/core/types/@open<(total :: E),(std/async/async/async :: (E, V) -> V),(i : int) -> ssize_t,(i : int) -> (std/async/async/async :: (E, V) -> V) ssize_t>(std/core/types/@make-ssize_t)(0)))), std/async/async/cancel/@select, std/async/async/empty-scope));
//         }))();
//       ((@skip std/core/types/False() : bool ) as @pat@0@3: bool)
//          -> std/core/types/Unit;
//     };
//   };
// },Own)
fun @lift-interleaved-div@10758 : forall<_a,b,e> (@uniq-ys@10617 : list<() -> <async-exn|e> b>, @uniq-i@10618 : int) -> <async,div,ndet,strands<b>|e> list<() -> <async,div,ndet,strands<b>|e> ()>
  = forall<_a,b,e> fn<<async,div,ndet,strands<b>|e>>(@uniq-ys@10617@1: list<() -> <async-exn|e> b>, @uniq-i@10618@3: int){
    (match ((std/core/hnd/@evv-is-affine())) {
      ((std/core/types/True() : bool ) as @pat@18: bool)
         -> std/async/async/@trmc-lift-interleaved-div@10758(@uniq-ys@10617@1, @uniq-i@10618@3, (std/core/types/cctx/empty()));
      (@pat@0@16: bool)
         -> std/async/async/@trmcm-lift-interleaved-div@10758(@uniq-ys@10617@1, @uniq-i@10618@3, (fn(@trmc-x10810: list<() -> <async,div,ndet,strands<b>|e> ()>){
            @trmc-x10810;
          }));
    });
  };
// lifted local: interleaved-div, @spec-x10615
// specialized: std/core/list/map-indexed, on parameters @uniq-f@10612, using:
// @uniq-f@10612 = (fn<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>>(i: int, action: () -> <(std/async/async/async-exn :: E)|(6668 :: E)> 6667){
//   fn<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>>(){
//     val action@0@10126 : () -> <(exn :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>,(std/async/async/async :: (E, V) -> V)|(e :: E)> a;
//     val fin : (either :: (V, V) -> V)<hnd/yield-info,(error :: V -> V)<a>>;
//     val res : (error :: V -> V)<a>;
//     val _ : ();
//     match ((std/core/types/@open<(total :: E),<(std/async/async/async :: (E, V) -> V),(std/async/async/strands :: (V, E, V) -> V)<a>,(div :: X),(ndet :: X)|(e :: E)>,(t : (error :: V -> V)<a>) -> bool,(t : (error :: V -> V)<a>) -> <(std/async/async/async :: (E, V) -> V),(std/async/async/strands :: (V, E, V) -> V)<a>,(div :: X),(ndet :: X)|(e :: E)> bool>((fn(t@0: (error :: V -> V)<6667>){
//       (match (t@0) {
//         ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@0: string) : string, (@pat@1@0: exception-info) : exception-info) : exception ) as exn: exception) : exception) : (error :: V -> V)<a> ) as @pat@1: ((error :: V -> V)<6667>))
//            -> (match (exn) {
//             ((@skip std/core/exn/Exception((@pat@0@1: string) : string, (@x: exception-info) : exception-info) : exception ) as @pat@2: exception)
//                -> (match (@x) {
//                 ((std/async/async/Finalize((@pat@0@2: hnd/yield-info) : hnd/yield-info) : exception-info ) as @pat@3: exception-info)
//                    -> std/core/types/True;
//                 (@pat@1@1: exception-info)
//                    -> std/core/types/False;
//               });
//           });
//         (@pat@2@0: ((error :: V -> V)<6667>))
//            -> std/core/types/False;
//       });
//     }))(res))) {
//       ((std/core/types/True() : bool ) as @pat@4: bool)
//          -> std/core/types/@open<(std/async/async/async :: (E, V) -> V),<(std/async/async/async :: (E, V) -> V),(std/async/async/strands :: (V, E, V) -> V)<a>,(div :: X),(ndet :: X)|(e :: E)>,() -> (std/async/async/async :: (E, V) -> V) (),() -> <(std/async/async/async :: (E, V) -> V),(std/async/async/strands :: (V, E, V) -> V)<a>,(div :: X),(ndet :: X)|(e :: E)> ()>((fn<(std/async/async/async :: (E, V) -> V)>(){
//           (std/core/hnd/@perform1<std/async/async/scope,(),(std/async/async/async :: (E, V) -> V),(std/async/async/async :: (E, V) -> V)>((std/core/types/@open<(total :: E),(std/async/async/async :: (E, V) -> V),(i : (hnd/ev-index == 1 ssize_t)) -> (hnd/ev :: ((E, V) -> V) -> V)<(std/async/async/async :: (E, V) -> V)>,(i : (hnd/ev-index == 1 ssize_t)) -> (std/async/async/async :: (E, V) -> V) (hnd/ev :: ((E, V) -> V) -> V)<(std/async/async/async :: (E, V) -> V)>>((std/core/hnd/@evv-at<(std/async/async/async :: (E, V) -> V)>))((std/core/types/@open<(total :: E),(std/async/async/async :: (E, V) -> V),(i : int) -> ssize_t,(i : int) -> (std/async/async/async :: (E, V) -> V) ssize_t>(std/core/types/@make-ssize_t)(0)))), std/async/async/cancel/@select, std/async/async/empty-scope));
//         }))();
//       ((@skip std/core/types/False() : bool ) as @pat@0@3: bool)
//          -> std/core/types/Unit;
//     };
//   };
// },Own)
fun @lift-interleaved-div@10757 : forall<_a,b,e> (@uniq-xs@10611 : list<() -> <async-exn|e> b>) -> <async,div,ndet,strands<b>|e> list<() -> <async,div,ndet,strands<b>|e> ()>
  = forall<_a,b,e> fn<<async,div,ndet,strands<b>|e>>(@uniq-xs@10611: list<() -> <async-exn|e> b>){
    (match (@uniq-xs@10611) {
      ((std/core/types/Nil() : list<() -> <(async-exn == 1 <async,exn>)|e> b> ) as @uniq-pat@0@10613: (list<() -> <(async-exn == 1 <async,exn>)|e> b>))
         -> std/core/types/Nil;
      (@uniq-pat@10614: (list<() -> <(async-exn == 1 <async,exn>)|e> b>))
         -> (match ((std/core/hnd/@evv-is-affine())) {
          ((std/core/types/True() : bool ) as @pat: bool)
             -> std/async/async/@trmc-lift-interleaved-div@10758(@uniq-xs@10611, 0, (std/core/types/cctx/empty()));
          (@pat@0: bool)
             -> std/async/async/@trmcm-lift-interleaved-div@10758(@uniq-xs@10611, 0, (fn(@trmc-x10810: list<() -> <async,div,ndet,strands<b>|e> ()>){
                @trmc-x10810;
              }));
        });
    });
  };
// monadic lift
fun @mlift-lift-interleaved-div@10760@11414 : forall<a,e> (ch : channel<() -> <async,div,ndet,strands<a>|e> ()>, v : () -> <async,div,ndet,strands<a>|e> (), @c-x10981 : list<() -> <async,div,ndet,strands<a>|e> ()>) -> ()
  = forall<a,e> fn(ch: channel<() -> <async,div,ndet,strands<a>|e> ()>, v: () -> <async,div,ndet,strands<a>|e> (), @c-x10981: list<() -> <async,div,ndet,strands<a>|e> ()>){
    std/core/types/set((match (ch) {
        ((@skip std/async/async/Channel((@pat@0@4@1: int), (@x@0@1: ref<global,channel-state<() -> <async,div,ndet,strands<a>|e> ()>>)) : channel<() -> <async,div,ndet,strands<a>|e> ()> ) as @pat@5@1: (channel<() -> <async,div,ndet,strands<a>|e> ()>))
           -> @x@0@1;
      }), (std/async/async/Values(v, @c-x10981)));
  };
// monadic lift
fun @mlift-lift-interleaved-div@10760@11415 : forall<a,e> (ch : channel<() -> <async,div,ndet,strands<a>|e> ()>, v : () -> <async,div,ndet,strands<a>|e> (), @c-x10980 : list<() -> <async,div,ndet,strands<a>|e> ()>) -> ()
  = forall<a,e> fn(ch@0: channel<() -> <async,div,ndet,strands<a>|e> ()>, v@0: () -> <async,div,ndet,strands<a>|e> (), @c-x10980: list<() -> <async,div,ndet,strands<a>|e> ()>){
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-extend((fn(@c-x10981@0: list<() -> <async,div,ndet,strands<a>|e> ()>){
          (std/async/async/@mlift-lift-interleaved-div@10760@11414(ch@0, v@0, @c-x10981@0));
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> std/async/async/@mlift-lift-interleaved-div@10760@11414(ch@0, v@0, @c-x10980);
    });
  };
// monadic lift
fun @mlift-lift-interleaved-div@10760@11416 : forall<a,b,e> (ch : channel<() -> <async,div,ndet,strands<b>|e> ()>, l : (() -> <async,div,ndet,strands<b>|e> ()) -> io-noexn (), rcontext : hnd/resume-context<error<a>,<async,div,ndet,strands<b>|e>,<async,async,div,ndet,strands<b>|e>,()>, res@0 : error<a>, @c-x10982 : channel-state<() -> <async,div,ndet,strands<b>|e> ()>) -> ()
  = forall<a,b,e> fn(ch@1: channel<() -> <async,div,ndet,strands<b>|e> ()>, l: (() -> <async,div,ndet,strands<b>|e> ()) -> io-noexn (), rcontext: hnd/resume-context<error<a>,<async,div,ndet,strands<b>|e>,<async,async,div,ndet,strands<b>|e>,()>, res@0: error<a>, @c-x10982: channel-state<() -> <async,div,ndet,strands<b>|e> ()>){
    val _@0 : ()
          = std/core/types/set((match (ch@1) {
              ((@skip std/async/async/Channel((@pat@0@4@2: int), (@x@0@2: ref<global,channel-state<() -> <async,div,ndet,strands<b>|e> ()>>)) : channel<() -> <async,div,ndet,strands<b>|e> ()> ) as @pat@5@2: (channel<() -> <async,div,ndet,strands<b>|e> ()>))
                 -> @x@0@2;
            }), @c-x10982);
    l((fn<<async,div,ndet,strands<b>|e>>(){
      (match (rcontext) {
        ((@skip std/core/hnd/Resume-context((@x: (hnd/resume-result<error<a>,()>) -> <async,div,ndet,strands<b>|e> ())) : hnd/resume-context<error<a>,<async,div,ndet,strands<b>|e>,<async,async,div,ndet,strands<b>|e>,()> ) as @pat@1: (hnd/resume-context<error<a>,<async,div,ndet,strands<b>|e>,<async,async,div,ndet,strands<b>|e>,()>))
           -> @x((std/core/hnd/Deep(res@0)));
      });
    }));
  };
// monadic lift
fun @mlift-lift-interleaved-div@10760@11417 : forall<a,e> (wild_@0@0 : ()) -> <async,div,ndet,strands<a>|e> ()
  = forall<a,e> fn<<async,div,ndet,strands<a>|e>>(wild_@0@0: ()){
    std/core/types/Unit;
  };
// monadic lift
fun @mlift-lift-interleaved-div@10760@11418 : forall<a,e> (@uniq-x@10637 : () -> <async,div,ndet,strands<a>|e> (), @y-x10988 : hnd/ev-index) -> <async,async,div,ndet,strands<a>|e> ()
  = forall<a,e> fn<<async,async,div,ndet,strands<a>|e>>(@uniq-x@10637: () -> <async,div,ndet,strands<a>|e> (), @y-x10988: hnd/ev-index){
    val w0 : hnd/evv<hnd/_e2>
      = std/core/hnd/evv-swap-delete(@y-x10988, std/core/types/True);
    val x@1 : ()
      = @uniq-x@10637();
    val _ : ()
      = std/core/hnd/evv-set(w0);
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat@2: bool)
         -> std/core/hnd/yield-cont((forall<b> fn<<async,async,div,ndet,strands<a>|e>>(cont: (b) -> <async,async,div,ndet,strands<a>|e> (), res: b){
          std/core/hnd/mask-at1(@y-x10988, std/core/types/True, cont, res);
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
         -> x@1;
    });
  };
// monadic lift
fun @mlift-lift-interleaved-div@10760@11419 : forall<_a,_b,_c,d,e> (@uniq-xx@10638 : list<() -> <async,div,ndet,strands<d>|e> ()>, ch : channel<() -> <async,div,ndet,strands<d>|e> ()>, wild : ()) -> <async,div,ndet,strands<d>|e> ()
  = forall<_a,_b,_c,d,e> fn<<async,div,ndet,strands<d>|e>>(@uniq-xx@10638: list<() -> <async,div,ndet,strands<d>|e> ()>, ch@2: channel<() -> <async,div,ndet,strands<d>|e> ()>, wild: ()){
    std/async/async/@lift-interleaved-div@10760(ch@2, @uniq-xx@10638);
  };
// lifted local: @lift-interleaved-div@10759, interleaved-div, @spec-x10640
// specialized: std/core/list/@unroll-foreach@10016, on parameters @uniq-action@10635, using:
// @uniq-action@10635 = (fn<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>>(strand: () -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()){
//   std/async/async/async/@handle<(),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>,()>((std/async/async/@Hnd-async<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>,()>(3, (forall<a> std/core/types/@open<(total :: E),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>,(op : (() -> (io-noexn :: E) _b) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)> _b) -> (hnd/clause1 :: (V, V, (E, V) -> V, E, V) -> V)<() -> (io-noexn :: E) _b,_b,(std/async/async/async :: (E, V) -> V),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)>,()>,(op : (() -> (io-noexn :: E) _b) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)> _b) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)> (hnd/clause1 :: (V, V, (E, V) -> V, E, V) -> V)<() -> (io-noexn :: E) _b,_b,(std/async/async/async :: (E, V) -> V),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)>,()>>((std/core/hnd/clause-tail1<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>,(),(std/async/async/async :: (E, V) -> V),() -> (io-noexn :: E) _b,_b>))((fn<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>>(f: () -> (io-noexn :: E) a){
//         (std/core/types/@open<(std/async/async/async :: (E, V) -> V),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>,(action : () -> (io-noexn :: E) a) -> (std/async/async/async :: (E, V) -> V) a,(action : () -> (io-noexn :: E) a) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)> a>((fn<(std/async/async/async :: (E, V) -> V)>(action@2: () -> (io-noexn :: E) a){
//           (std/core/hnd/@perform1<() -> (io-noexn :: E) a,a,(std/async/async/async :: (E, V) -> V),(std/async/async/async :: (E, V) -> V)>((std/core/types/@open<(total :: E),(std/async/async/async :: (E, V) -> V),(i : hnd/ev-index) -> (hnd/ev :: ((E, V) -> V) -> V)<(std/async/async/async :: (E, V) -> V)>,(i : hnd/ev-index) -> (std/async/async/async :: (E, V) -> V) (hnd/ev :: ((E, V) -> V) -> V)<(std/async/async/async :: (E, V) -> V)>>((std/core/hnd/@evv-at<(std/async/async/async :: (E, V) -> V)>))((std/core/types/@open<(total :: E),(std/async/async/async :: (E, V) -> V),(i : int) -> ssize_t,(i : int) -> (std/async/async/async :: (E, V) -> V) ssize_t>(std/core/types/@make-ssize_t)(0)))), (forall<(e :: E),b> std/async/async/async-iox/@select<a,(e :: E),b>), action@2));
//         }))(f));
//       }))), (std/core/types/@open<(total :: E),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>,(op : (std/async/async/scope) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)> ()) -> (hnd/clause1 :: (V, V, (E, V) -> V, E, V) -> V)<std/async/async/scope,(),(std/async/async/async :: (E, V) -> V),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>,()>,(op : (std/async/async/scope) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)> ()) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)> (hnd/clause1 :: (V, V, (E, V) -> V, E, V) -> V)<std/async/async/scope,(),(std/async/async/async :: (E, V) -> V),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>,()>>((std/core/hnd/clause-tail1<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>,(),(std/async/async/async :: (E, V) -> V),std/async/async/scope,()>))((fn<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>>(scope@0: std/async/async/scope){
//         (std/core/types/@open<(std/async/async/async :: (E, V) -> V),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>,(scope : std/async/async/scope) -> (std/async/async/async :: (E, V) -> V) (),(scope : std/async/async/scope) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)> ()>((fn<(std/async/async/async :: (E, V) -> V)>(scope@1: std/async/async/scope){
//           (std/core/hnd/@perform1<std/async/async/scope,(),(std/async/async/async :: (E, V) -> V),(std/async/async/async :: (E, V) -> V)>((std/core/types/@open<(total :: E),(std/async/async/async :: (E, V) -> V),(i : hnd/ev-index) -> (hnd/ev :: ((E, V) -> V) -> V)<(std/async/async/async :: (E, V) -> V)>,(i : hnd/ev-index) -> (std/async/async/async :: (E, V) -> V) (hnd/ev :: ((E, V) -> V) -> V)<(std/async/async/async :: (E, V) -> V)>>((std/core/hnd/@evv-at<(std/async/async/async :: (E, V) -> V)>))((std/core/types/@open<(total :: E),(std/async/async/async :: (E, V) -> V),(i : int) -> ssize_t,(i : int) -> (std/async/async/async :: (E, V) -> V) ssize_t>(std/core/types/@make-ssize_t)(0)))), std/async/async/cancel/@select, scope@1));
//         }))(scope@0));
//       }))), (forall<a> std/core/types/@open<(total :: E),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>,(op : (x1 : (std/async/async/await-setup :: V -> V)<_b>, x2 : std/async/async/scope, x3 : bool, r : (hnd/resume-context :: (V, E, E, V) -> V)<(error :: V -> V)<_b>,<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)>,<(std/async/async/async :: (E, V) -> V),(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)>,()>) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)> ()) -> (hnd/clause1 :: (V, V, (E, V) -> V, E, V) -> V)<((std/async/async/await-setup :: V -> V)<_b>, std/async/async/scope, bool),(error :: V -> V)<_b>,(std/async/async/async :: (E, V) -> V),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)>,()>,(op : (x1 : (std/async/async/await-setup :: V -> V)<_b>, x2 : std/async/async/scope, x3 : bool, r : (hnd/resume-context :: (V, E, E, V) -> V)<(error :: V -> V)<_b>,<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)>,<(std/async/async/async :: (E, V) -> V),(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)>,()>) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)> ()) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)> (hnd/clause1 :: (V, V, (E, V) -> V, E, V) -> V)<((std/async/async/await-setup :: V -> V)<_b>, std/async/async/scope, bool),(error :: V -> V)<_b>,(std/async/async/async :: (E, V) -> V),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)>,()>>((std/core/hnd/clause-control-raw3<(std/async/async/await-setup :: V -> V)<_b>,std/async/async/scope,bool,(error :: V -> V)<_b>,<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>,<(std/async/async/async :: (E, V) -> V),(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>,(std/async/async/async :: (E, V) -> V),()>))((fn<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>>(setup: (std/async/async/await-setup :: V -> V)<a>, scope@0@0: std/async/async/scope, c: bool, rcontext: (hnd/resume-context :: (V, E, E, V) -> V)<(error :: V -> V)<a>,<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)>,<(std/async/async/async :: (E, V) -> V),(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)>,()>){
//         val _@0@0 : ()
//               = (std/core/types/@open<(std/async/async/async :: (E, V) -> V),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>,(setup : (std/async/async/await-setup :: V -> V)<a>, scope : std/async/async/scope, cancelable : bool, f : ((error :: V -> V)<a>) -> (io-noexn :: E) ()) -> (std/async/async/async :: (E, V) -> V) (),(setup : (std/async/async/await-setup :: V -> V)<a>, scope : std/async/async/scope, cancelable : bool, f : ((error :: V -> V)<a>) -> (io-noexn :: E) ()) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)> ()>((fn<(std/async/async/async :: (E, V) -> V)>(setup@0: (std/async/async/await-setup :: V -> V)<a>, scope@2: std/async/async/scope, cancelable@0: bool, f@0: ((error :: V -> V)<a>) -> (io-noexn :: E) ()){
//                 (std/core/hnd/@perform4<(std/async/async/await-setup :: V -> V)<a>,std/async/async/scope,bool,((error :: V -> V)<a>) -> (io-noexn :: E) (),(),(std/async/async/async :: (E, V) -> V),(std/async/async/async :: (E, V) -> V)>((std/core/types/@open<(total :: E),(std/async/async/async :: (E, V) -> V),(i : hnd/ev-index) -> (hnd/ev :: ((E, V) -> V) -> V)<(std/async/async/async :: (E, V) -> V)>,(i : hnd/ev-index) -> (std/async/async/async :: (E, V) -> V) (hnd/ev :: ((E, V) -> V) -> V)<(std/async/async/async :: (E, V) -> V)>>((std/core/hnd/@evv-at<(std/async/async/async :: (E, V) -> V)>))((std/core/types/@open<(total :: E),(std/async/async/async :: (E, V) -> V),(i : int) -> ssize_t,(i : int) -> (std/async/async/async :: (E, V) -> V) ssize_t>(std/core/types/@make-ssize_t)(0)))), (forall<(e :: E),b> std/async/async/no-await/@select<a,(e :: E),b>), setup@0, scope@2, cancelable@0, f@0));
//               }))(setup, scope@0@0, c, (fn<(io-noexn :: E)>(res@0: (error :: V -> V)<a>){
//                   (match ((std/core/types/ref/(!)<(std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>,<(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>,(console/console :: X),(div :: X),(fsys :: X),(ndet :: X),(net :: X),(ui :: X)>,(global :: H)>((match (ch) {
//                       ((@skip std/async/async/Channel((@pat@0@4: int) : int, (@x@0: (ref :: (H, V) -> V)<(global :: H),(std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>>) : (ref :: (H, V) -> V)<(global :: H),(std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>>) : (std/async/async/channel :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()> ) as @pat@5: ((std/async/async/channel :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>))
//                          -> @x@0;
//                     }), (std/core/types/@Hdiv<(global :: H),(std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>,<(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>,(console/console :: X),(div :: X),(fsys :: X),(ndet :: X),(net :: X),(ui :: X)>>)))) {
//                     ((std/async/async/Empty() : (std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()> ) as @pat@6: ((std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>))
//                        -> std/core/types/set<(std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>,(global :: H)>((match (ch) {
//                           ((@skip std/async/async/Channel((@pat@0@4: int) : int, (@x@0: (ref :: (H, V) -> V)<(global :: H),(std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>>) : (ref :: (H, V) -> V)<(global :: H),(std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>>) : (std/async/async/channel :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()> ) as @pat@5: ((std/async/async/channel :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>))
//                              -> @x@0;
//                         }), (std/async/async/Values<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>((fn<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>>(){
//                             (std/core/hnd/resume<(error :: V -> V)<a>,<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>,<(std/async/async/async :: (E, V) -> V),(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>,()>(rcontext, res@0));
//                           }), (std/core/types/Nil<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>))));
//                     ((std/async/async/Values((v: () -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()) : () -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> (), (vs: (list :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>) : (list :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>) : (std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()> ) as @pat@0@6: ((std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>))
//                        -> val ys@10139 : (list :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>;
//                           val values@0@10137 : ? ((list :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>);
//                       std/core/types/set<(std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>,(global :: H)>((match (ch) {
//                           ((@skip std/async/async/Channel((@pat@0@4: int) : int, (@x@0: (ref :: (H, V) -> V)<(global :: H),(std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>>) : (ref :: (H, V) -> V)<(global :: H),(std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>>) : (std/async/async/channel :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()> ) as @pat@5: ((std/async/async/channel :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>))
//                              -> @x@0;
//                         }), (std/async/async/Values<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>(v, (match (values@0@10137) {
//                             ((std/core/types/@Optional((@uniq-values@967@0: (list :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>) : (list :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>) : ? ((list :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>) ) as @pat@8: ? ((list :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>))
//                                -> @uniq-values@967@0;
//                             ((@skip std/core/types/@None() : ? ((list :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>) ) as @pat@0@7: ? ((list :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>))
//                                -> std/core/types/Nil<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>;
//                           }))));
//                     ((@skip std/async/async/Waiting((l: (() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()) : (() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) (), (ls: (list :: V -> V)<(() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()>) : (list :: V -> V)<(() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()>) : (std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()> ) as @pat@1@2: ((std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>))
//                        -> val _@0 : ()
//                                 = std/core/types/set<(std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>,(global :: H)>((match (ch) {
//                                     ((@skip std/async/async/Channel((@pat@0@4: int) : int, (@x@0: (ref :: (H, V) -> V)<(global :: H),(std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>>) : (ref :: (H, V) -> V)<(global :: H),(std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>>) : (std/async/async/channel :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()> ) as @pat@5: ((std/async/async/channel :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>))
//                                        -> @x@0;
//                                   }), (match (ls) {
//                                     ((std/core/types/Nil() : (list :: V -> V)<(() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()> ) as @pat@10: ((list :: V -> V)<(() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()>))
//                                        -> std/async/async/Empty<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>;
//                                     ((@skip std/core/types/Cons((l@0: (() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()) : (() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) (), (ls@0: (list :: V -> V)<(() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()>) : (list :: V -> V)<(() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()>) : (list :: V -> V)<(() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()> ) as @pat@0@5: ((list :: V -> V)<(() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()>))
//                                        -> std/async/async/Waiting<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>(l@0, ls@0);
//                                   }));
//                       l((fn<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>>(){
//                         (std/core/hnd/resume<(error :: V -> V)<a>,<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>,<(std/async/async/async :: (E, V) -> V),(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>,()>(rcontext, res@0));
//                       }));
//                   });
//                 })));
//         std/core/types/Unit;
//       }))), (forall<a> std/core/types/@open<(total :: E),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>,(op : ((std/async/async/await-setup :: V -> V)<_b>, std/async/async/scope, bool, ((error :: V -> V)<_b>) -> (io-noexn :: E) ()) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)> ()) -> (hnd/clause1 :: (V, V, (E, V) -> V, E, V) -> V)<((std/async/async/await-setup :: V -> V)<_b>, std/async/async/scope, bool, ((error :: V -> V)<_b>) -> (io-noexn :: E) ()),(),(std/async/async/async :: (E, V) -> V),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)>,()>,(op : ((std/async/async/await-setup :: V -> V)<_b>, std/async/async/scope, bool, ((error :: V -> V)<_b>) -> (io-noexn :: E) ()) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)> ()) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)> (hnd/clause1 :: (V, V, (E, V) -> V, E, V) -> V)<((std/async/async/await-setup :: V -> V)<_b>, std/async/async/scope, bool, ((error :: V -> V)<_b>) -> (io-noexn :: E) ()),(),(std/async/async/async :: (E, V) -> V),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)>,()>>((std/core/hnd/clause-tail4<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>,(),(std/async/async/async :: (E, V) -> V),(std/async/async/await-setup :: V -> V)<_b>,std/async/async/scope,bool,((error :: V -> V)<_b>) -> (io-noexn :: E) (),()>))((fn<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>>(setup@0@0: (std/async/async/await-setup :: V -> V)<a>, scope@1@0: std/async/async/scope, c@0: bool, f@0@0: ((error :: V -> V)<a>) -> (io-noexn :: E) ()){
//         (std/core/types/@open<(std/async/async/async :: (E, V) -> V),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>,(setup : (std/async/async/await-setup :: V -> V)<a>, scope : std/async/async/scope, cancelable : bool, f : ((error :: V -> V)<a>) -> (io-noexn :: E) ()) -> (std/async/async/async :: (E, V) -> V) (),(setup : (std/async/async/await-setup :: V -> V)<a>, scope : std/async/async/scope, cancelable : bool, f : ((error :: V -> V)<a>) -> (io-noexn :: E) ()) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)> ()>((fn<(std/async/async/async :: (E, V) -> V)>(setup@1: (std/async/async/await-setup :: V -> V)<a>, scope@3: std/async/async/scope, cancelable@0@0: bool, f@1: ((error :: V -> V)<a>) -> (io-noexn :: E) ()){
//           (std/core/hnd/@perform4<(std/async/async/await-setup :: V -> V)<a>,std/async/async/scope,bool,((error :: V -> V)<a>) -> (io-noexn :: E) (),(),(std/async/async/async :: (E, V) -> V),(std/async/async/async :: (E, V) -> V)>((std/core/types/@open<(total :: E),(std/async/async/async :: (E, V) -> V),(i : hnd/ev-index) -> (hnd/ev :: ((E, V) -> V) -> V)<(std/async/async/async :: (E, V) -> V)>,(i : hnd/ev-index) -> (std/async/async/async :: (E, V) -> V) (hnd/ev :: ((E, V) -> V) -> V)<(std/async/async/async :: (E, V) -> V)>>((std/core/hnd/@evv-at<(std/async/async/async :: (E, V) -> V)>))((std/core/types/@open<(total :: E),(std/async/async/async :: (E, V) -> V),(i : int) -> ssize_t,(i : int) -> (std/async/async/async :: (E, V) -> V) ssize_t>(std/core/types/@make-ssize_t)(0)))), (forall<(e :: E),b> std/async/async/no-await/@select<a,(e :: E),b>), setup@1, scope@3, cancelable@0@0, f@1));
//         }))(setup@0@0, scope@1@0, c@0, f@0@0));
//       }))))), (fn<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>>(@res: ()){
//       @res;
//     }), (fn<<(std/async/async/async :: (E, V) -> V),(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>>(){
//       (std/core/hnd/@mask-at<(),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>,<(std/async/async/async :: (E, V) -> V),(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>>((std/core/hnd/@evv-index<<(std/async/async/async :: (E, V) -> V),(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>>(std/async/async/async/@tag)), std/core/types/True, strand));
//     }));
// },Own)
fun @lift-interleaved-div@10760 : forall<_a,_b,_c,d,e> (ch : channel<() -> <async,div,ndet,strands<d>|e> ()>, @uniq-xs@10634 : list<() -> <async,div,ndet,strands<d>|e> ()>) -> <async,div,ndet,strands<d>|e> ()
  = forall<_a,_b,_c,d,e> fn<<async,div,ndet,strands<d>|e>>(ch@3: channel<() -> <async,div,ndet,strands<d>|e> ()>, @uniq-xs@10634: list<() -> <async,div,ndet,strands<d>|e> ()>){
    (match (@uniq-xs@10634) {
      ((std/core/types/Cons((@uniq-x@10637@0: () -> <async,div,ndet,strands<d>|e> ()), (@uniq-xx@10638@0: list<() -> <async,div,ndet,strands<d>|e> ()>)) : list<() -> <async,div,ndet,strands<d>|e> ()> ) as @uniq-pat@10636: (list<() -> <async,div,ndet,strands<d>|e> ()>))
         -> val x@2@12006 : ()
                  = std/async/async/async/@handle((std/async/async/@Hnd-async(3, (forall<a1> std/core/hnd/clause-tail1((fn<<async,div,ndet,strands<d>|e>>(f: () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) a1){
                        val i@0@12009 : (hnd/ev-index == 1 ssize_t)
                          = (std/core/hnd/@evv-index(std/async/async/async/@tag));
                        val w : (hnd/evv<<async,div,ndet,strands<d>|e>>)
                          = (std/core/hnd/evv-swap-create1(i@0@12009));
                        val ev@12012 : (hnd/ev<async>)
                          = (std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0))));
                        val y : a1
                          = (match (ev@12012) {
                            ((@skip std/core/hnd/Ev<e1,b1>((@pat@0@3: hnd/htag<async>), (m: hnd/marker<e1,b1>), (h: async<e1,b1>), (@pat@1@0: hnd/evv<e1>)) : hnd/ev<async> ) as @pat@5: (hnd/ev<async>))
                               -> (match (h) {
                                ((@skip std/async/async/@Hnd-async((@pat@0@1: int), (@ctl-async-iox: forall<c1> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c1,c1,async,e1,b1>), (@pat@1@1: hnd/clause1<scope,(),async,e1,b1>), (@pat@2@0: forall<c1> hnd/clause1<((await-setup<c1> == 4 (cb : (error<c1>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c1>,async,e1,b1>), (@pat@3@0: (forall<c1> hnd/clause1<((await-setup<c1> == 4 (cb : (error<c1>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/
   console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c1>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,
   write<global>,alloc<global>>)>)>) ()),(),async,e1,b1>))) : async<e1,b1> ) as @pat@3: (async<e1,b1>))
                                   -> (match (@ctl-async-iox) {
                                    ((@skip std/core/hnd/Clause1((f@1: (hnd/marker<e1,b1>, hnd/ev<async>, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) a1) -> e1 a1)) : hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) a1,a1,async,e1,b1> ) as @pat@2@0@0: (hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,
   console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) a1,a1,async,e1,b1>))
                                       -> f@1(m, ev@12012, f);
                                  });
                              });
                          });
                        val _ : ()
                          = (std/core/hnd/evv-set(w));
                        (match ((std/core/hnd/yielding())) {
                          ((std/core/types/True() : bool ) as @pat@4: bool)
                             -> std/core/hnd/yield-cont((forall<b1> fn<<async,div,ndet,strands<d>|e>>(cont@0: (b1) -> <async,div,ndet,strands<d>|e> a1, res@1: b1){
                              std/core/hnd/open-at1(i@0@12009, cont@0, res@1);
                            }));
                          ((@skip std/core/types/False() : bool ) as @pat@0@2: bool)
                             -> y;
                        });
                      }))), (std/core/hnd/clause-tail1((fn<<async,div,ndet,strands<d>|e>>(scope@0: scope){
                        val i@1@12015 : (hnd/ev-index == 1 ssize_t)
                          = (std/core/hnd/@evv-index(std/async/async/async/@tag));
                        val w@0 : (hnd/evv<<async,div,ndet,strands<d>|e>>)
                          = (std/core/hnd/evv-swap-create1(i@1@12015));
                        val ev@0@12018 : (hnd/ev<async>)
                          = (std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0))));
                        val y@0 : ()
                          = (match (ev@0@12018) {
                            ((@skip std/core/hnd/Ev<e1,a1>((@pat@0@5: hnd/htag<async>), (m@0: hnd/marker<e1,a1>), (h@0: async<e1,a1>), (@pat@1@1@0: hnd/evv<e1>)) : hnd/ev<async> ) as @pat@7: (hnd/ev<async>))
                               -> (match (h@0) {
                                ((@skip std/async/async/@Hnd-async((@pat@0@4: int), (@pat@1@2: forall<b1> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) b1,b1,async,e1,a1>), (@ctl-cancel: hnd/clause1<scope,(),async,e1,a1>), (@pat@2@1: forall<b1> hnd/clause1<((await-setup<b1> == 4 (cb : (error<b1>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global
   >,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<b1>,async,e1,a1>), (@pat@3@1: (forall<b1> hnd/clause1<((await-setup<b1> == 4 (cb : (error<b1>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console
   ,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<b1>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<
   global>,alloc<global>>)>)>) ()),(),async,e1,a1>))) : async<e1,a1> ) as @pat@6: (async<e1,a1>))
                                   -> (match (@ctl-cancel) {
                                    ((@skip std/core/hnd/Clause1((f@3: (hnd/marker<e1,a1>, hnd/ev<async>, scope) -> e1 ())) : hnd/clause1<scope,(),async,e1,a1> ) as @pat@2@1@0: (hnd/clause1<scope,(),async,e1,a1>))
                                       -> f@3(m@0, ev@0@12018, scope@0);
                                  });
                              });
                          });
                        val _ : ()
                          = (std/core/hnd/evv-set(w@0));
                        (match ((std/core/hnd/yielding())) {
                          ((std/core/types/True() : bool ) as @pat@6@0: bool)
                             -> std/core/hnd/yield-cont((forall<a1> fn<<async,div,ndet,strands<d>|e>>(cont@1: (a1) -> <async,div,ndet,strands<d>|e> (), res@2: a1){
                              std/core/hnd/open-at1(i@1@12015, cont@1, res@2);
                            }));
                          ((@skip std/core/types/False() : bool ) as @pat@0@4@0: bool)
                             -> y@0;
                        });
                      }))), (forall<a1> std/core/hnd/Clause1((fn<<async,div,ndet,strands<d>|e>>(m@1: hnd/marker<<async,div,ndet,strands<d>|e>,()>, @_wildcard-x597_16: hnd/ev<async>, x@7: ((await-setup<_b> == 4 (cb : (error<_b>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)
   maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool)){
                        (std/core/hnd/yield-to(m@1, (fn<<async,div,ndet,strands<d>|e>>(k: (hnd/resume-result<error<_b>,()>) -> <async,div,ndet,strands<d>|e> ()){
                            (match (x@7) {
                              ((@skip std/core/types/Tuple3((x1: (await-setup<_b> == 4 (cb : (error<_b>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<
   global>,alloc<global>>)>)>) ()>)), (x2: scope), (x3: bool)) : ((await-setup<_b> == 4 (cb : (error<_b>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<
   global>,alloc<global>>)>)>) ()>), scope, bool) ) as @pat@8: ((await-setup<_b> == 4 (cb : (error<_b>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<
   global>,alloc<global>>)>)>) ()>), scope, bool))
                                 -> val rcontext@0@12460 : hnd/resume-context<error<a1>,<async,div,ndet,strands<d>|e>,<async,async,div,ndet,strands<d>|e>,()>
                                      = std/core/hnd/Resume-context(k);
                                    val i@2@12024 : (hnd/ev-index == 1 ssize_t)
                                      = std/core/hnd/@evv-index(std/async/async/async/@tag);
                                    val w@1 : hnd/evv<<async,div,ndet,strands<d>|e>>
                                      = std/core/hnd/evv-swap-create1(i@2@12024);
                                    val ev@1@12030 : hnd/ev<async>
                                      = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
                                    val y@1 : ()
                                      = (match (ev@1@12030) {
                                        ((@skip std/core/hnd/Ev<e1,b1>((@pat@0@8: hnd/htag<async>), (m@2: hnd/marker<e1,b1>), (h@1: async<e1,b1>), (@pat@1@2@0: hnd/evv<e1>)) : hnd/ev<async> ) as @pat@11: (hnd/ev<async>))
                                           -> (match (h@1) {
                                            ((@skip std/async/async/@Hnd-async((@pat@0@6: int), (@pat@1@3: forall<c1> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c1,c1,async,e1,b1>), (@pat@2@2: hnd/clause1<scope,(),async,e1,b1>), (@pat@3@2: forall<c1> hnd/clause1<((await-setup<c1> == 4 (cb : (error<c1>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <
   read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c1>,async,e1,b1>), (@ctl-no-await: (forall<c1> hnd/clause1<((await-setup<c1> == 4 (cb : (error<c1>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet
   ,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c1>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()),(),async,e1,b1>))) : async<e1,b1> ) as @pat@9: (async<e1,b1>))
                                               -> (match (@ctl-no-await) {
                                                ((@skip std/core/hnd/Clause1((f@5: (hnd/marker<e1,b1>, hnd/ev<async>, ((await-setup<a1> == 4 (cb : (error<a1>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console
   ,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<a1>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())) -> e1 ())) : hnd/clause1<((await-setup<a1> == 4 (cb : (error<a1>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,
   console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<a1>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async,e1,b1> ) as @pat@2@2@0: (hnd/clause1<((await-setup<a1> == 4 (cb : (error<a1>, bool) -> (
   io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<a1>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/
   console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async,e1,b1>))
                                                   -> f@5(m@2, ev@1@12030, (std/core/types/Tuple4(x1, x2, x3, (fn<(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>(res@0@0: error<a1>){
                                                        (match ((std/core/types/ref/(!)((match (ch@3) {
                                                            ((@skip std/async/async/Channel((@pat@0@4@0@0: int), (@x@0: ref<global,channel-state<() -> <async,div,ndet,strands<d>|e> ()>>)) : channel<() -> <async,div,ndet,strands<d>|e> ()> ) as @pat@5@0: (channel<() -> <async,div,ndet,strands<d>|e> ()>))
                                                               -> @x@0;
                                                          }), std/core/types/@Hdiv))) {
                                                          ((std/async/async/Empty() : channel-state<() -> <async,div,ndet,strands<d>|e> ()> ) as @pat@6@0@0: (channel-state<() -> <async,div,ndet,strands<d>|e> ()>))
                                                             -> std/core/types/set((match (ch@3) {
                                                                ((@skip std/async/async/Channel((@pat@0@4@0@0@0: int), (@x@0@0: ref<global,channel-state<() -> <async,div,ndet,strands<d>|e> ()>>)) : channel<() -> <async,div,ndet,strands<d>|e> ()> ) as @pat@5@0@0: (channel<() -> <async,div,ndet,strands<d>|e> ()>))
                                                                   -> @x@0@0;
                                                              }), (std/async/async/Values((fn<<async,div,ndet,strands<d>|e>>(){
                                                                  (match (rcontext@0@12460) {
                                                                    ((@skip std/core/hnd/Resume-context((@x@1: (hnd/resume-result<error<a1>,()>) -> <async,div,ndet,strands<d>|e> ())) : hnd/resume-context<error<a1>,<async,div,ndet,strands<d>|e>,<async,async,div,ndet,strands<d>|e>,()> ) as @pat@12: (hnd/resume-context<error<a1>,<async,div,ndet,strands<d>|e>,<async,async,div,ndet,strands<d>|e>,()>))
                                                                       -> @x@1((std/core/hnd/Deep(res@0@0)));
                                                                  });
                                                                }), std/core/types/Nil)));
                                                          ((std/async/async/Values((v@1: () -> <async,div,ndet,strands<d>|e> ()), (vs: list<() -> <async,div,ndet,strands<d>|e> ()>)) : channel-state<() -> <async,div,ndet,strands<d>|e> ()> ) as @pat@0@6@0: (channel-state<() -> <async,div,ndet,strands<d>|e> ()>))
                                                             -> val ys@10139 : list<() -> <async,div,ndet,strands<d>|e> ()>
                                                                  = std/core/types/Cons((fn<<async,div,ndet,strands<d>|e>>(){
                                                                      (match (rcontext@0@12460) {
                                                                        ((@skip std/core/hnd/Resume-context((@x@2: (hnd/resume-result<error<a1>,()>) -> <async,div,ndet,strands<d>|e> ())) : hnd/resume-context<error<a1>,<async,div,ndet,strands<d>|e>,<async,async,div,ndet,strands<d>|e>,()> ) as @pat@13: (hnd/resume-context<error<a1>,<async,div,ndet,strands<d>|e>,<async,async,div,ndet,strands<d>|e>,()>))
                                                                           -> @x@2((std/core/hnd/Deep(res@0@0)));
                                                                      });
                                                                    }), std/core/types/Nil);
                                                                val x@11@12040 : list<() -> <async,div,ndet,strands<d>|e> ()>
                                                                  = (match (vs) {
                                                                    ((std/core/types/Nil() : list<() -> <async,div,ndet,strands<d>|e> ()> ) as @pat@0@8@0: (list<() -> <async,div,ndet,strands<d>|e> ()>))
                                                                       -> ys@10139;
                                                                    (@pat@9@0: (list<() -> <async,div,ndet,strands<d>|e> ()>))
                                                                       -> std/core/list/@unroll-append@10004(vs, ys@10139);
                                                                  });
                                                            (match ((std/core/hnd/yielding())) {
                                                              ((std/core/types/True() : bool ) as @pat@14: bool)
                                                                 -> std/core/hnd/yield-extend((fn(@c-x10980@0: list<() -> <async,div,ndet,strands<d>|e> ()>){
                                                                  (std/async/async/@mlift-lift-interleaved-div@10760@11415(ch@3, v@1, @c-x10980@0));
                                                                }));
                                                              ((@skip std/core/types/False() : bool ) as @pat@0@9: bool)
                                                                 -> std/async/async/@mlift-lift-interleaved-div@10760@11415(ch@3, v@1, x@11@12040);
                                                            });
                                                          ((@skip std/async/async/Waiting((l@0: (() -> <async,div,ndet,strands<d>|e> ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()), (ls: list<(() -> <async,div,ndet,strands<d>|e> ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)) : channel-state<() -> <async,div,ndet,
   strands<d>|e> ()> ) as @pat@1@2@0@0: (channel-state<() -> <async,div,ndet,strands<d>|e> ()>))
                                                             -> (match ((std/core/hnd/yielding())) {
                                                              ((std/core/types/True() : bool ) as @pat@15: bool)
                                                                 -> std/core/hnd/yield-extend((fn(@c-x10982@0: channel-state<() -> <async,div,ndet,strands<d>|e> ()>){
                                                                  (std/async/async/@mlift-lift-interleaved-div@10760@11416(ch@3, l@0, rcontext@0@12460, res@0@0, @c-x10982@0));
                                                                }));
                                                              ((@skip std/core/types/False() : bool ) as @pat@0@10: bool)
                                                                 -> std/async/async/@mlift-lift-interleaved-div@10760@11416(ch@3, l@0, rcontext@0@12460, res@0@0, (match (ls) {
                                                                    ((std/core/types/Nil() : list<(() -> <async,div,ndet,strands<d>|e> ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()> ) as @pat@10@0: (list<(() -> <async,div,ndet,strands<d>|e> ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>))
                                                                       -> std/async/async/Empty;
                                                                    ((@skip std/core/types/Cons((l@0@0: (() -> <async,div,ndet,strands<d>|e> ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()), (ls@0: list<(() -> <async,div,ndet,strands<d>|e> ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)) : list<(() -> <async,div,
   ndet,strands<d>|e> ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()> ) as @pat@0@5@0: (list<(() -> <async,div,ndet,strands<d>|e> ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>))
                                                                       -> std/async/async/Waiting(l@0@0, ls@0);
                                                                  }));
                                                            });
                                                        });
                                                      }))));
                                              });
                                          });
                                      });
                                    val _ : ()
                                      = std/core/hnd/evv-set(w@1);
                                    val x@8@12022 : ()
                                      = (match ((std/core/hnd/yielding())) {
                                        ((std/core/types/True() : bool ) as @pat@10: bool)
                                           -> std/core/hnd/yield-cont((forall<b1> fn<<async,div,ndet,strands<d>|e>>(cont@2: (b1) -> <async,div,ndet,strands<d>|e> (), res@3: b1){
                                            std/core/hnd/open-at1(i@2@12024, cont@2, res@3);
                                          }));
                                        ((@skip std/core/types/False() : bool ) as @pat@0@7: bool)
                                           -> y@1;
                                      });
                                (match ((std/core/hnd/yielding())) {
                                  ((std/core/types/True() : bool ) as @pat@9@1: bool)
                                     -> std/core/hnd/yield-extend((fn<<async,div,ndet,strands<d>|e>>(wild_@0@0@0: ()){
                                      (std/async/async/@mlift-lift-interleaved-div@10760@11417(wild_@0@0@0));
                                    }));
                                  ((@skip std/core/types/False() : bool ) as @pat@0@6@1: bool)
                                     -> std/async/async/@mlift-lift-interleaved-div@10760@11417(x@8@12022);
                                });
                            });
                          })));
                      }))), (forall<a1> std/core/hnd/clause-tail4((fn<<async,div,ndet,strands<d>|e>>(setup@0@0: (await-setup<a1> == 4 (cb : (error<a1>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,
   fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope@1@0: scope, c@0: bool, f@0@0@0: (error<a1>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()){
                        val i@3@12044 : (hnd/ev-index == 1 ssize_t)
                          = (std/core/hnd/@evv-index(std/async/async/async/@tag));
                        val w@2 : (hnd/evv<<async,div,ndet,strands<d>|e>>)
                          = (std/core/hnd/evv-swap-create1(i@3@12044));
                        val ev@2@12050 : (hnd/ev<async>)
                          = (std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0))));
                        val y@2 : ()
                          = (match (ev@2@12050) {
                            ((@skip std/core/hnd/Ev<e1,b1>((@pat@0@12: hnd/htag<async>), (m@3: hnd/marker<e1,b1>), (h@2: async<e1,b1>), (@pat@1@3@0: hnd/evv<e1>)) : hnd/ev<async> ) as @pat@17: (hnd/ev<async>))
                               -> (match (h@2) {
                                ((@skip std/async/async/@Hnd-async((@pat@0@11: int), (@pat@1@4: forall<c1> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c1,c1,async,e1,b1>), (@pat@2@3: hnd/clause1<scope,(),async,e1,b1>), (@pat@3@3: forall<c1> hnd/clause1<((await-setup<c1> == 4 (cb : (error<c1>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,
   write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c1>,async,e1,b1>), (@ctl-no-await@0: (forall<c1> hnd/clause1<((await-setup<c1> == 4 (cb : (error<c1>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/
   console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c1>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,
   write<global>,alloc<global>>)>)>) ()),(),async,e1,b1>))) : async<e1,b1> ) as @pat@16: (async<e1,b1>))
                                   -> (match (@ctl-no-await@0) {
                                    ((@skip std/core/hnd/Clause1((f@7: (hnd/marker<e1,b1>, hnd/ev<async>, ((await-setup<a1> == 4 (cb : (error<a1>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui
   ,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<a1>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ())) -> e1 ())) : hnd/clause1<((await-setup<a1> == 4 (cb : (error<a1>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/
   console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<a1>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async,e1,b1> ) as @pat@2@3@0: (hnd/clause1<((await-setup<a1> == 4 (cb : (error<a1>, bool) -> (io-noexn
   == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<a1>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,
   fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async,e1,b1>))
                                       -> f@7(m@3, ev@2@12050, (std/core/types/Tuple4(setup@0@0, scope@1@0, c@0, f@0@0@0)));
                                  });
                              });
                          });
                        val _ : ()
                          = (std/core/hnd/evv-set(w@2));
                        (match ((std/core/hnd/yielding())) {
                          ((std/core/types/True() : bool ) as @pat@16@0: bool)
                             -> std/core/hnd/yield-cont((forall<b1> fn<<async,div,ndet,strands<d>|e>>(cont@3: (b1) -> <async,div,ndet,strands<d>|e> (), res@4: b1){
                              std/core/hnd/open-at1(i@3@12044, cont@3, res@4);
                            }));
                          ((@skip std/core/types/False() : bool ) as @pat@0@11@0: bool)
                             -> y@2;
                        });
                      }))))), (fn<<async,div,ndet,strands<d>|e>>(@res: ()){
                      @res;
                    }), (fn<<async,async,div,ndet,strands<d>|e>>(){
                      val x@13@12056 : (hnd/ev-index == 1 ssize_t)
                            = (std/core/hnd/@evv-index(std/async/async/async/@tag));
                      (match ((std/core/hnd/yielding())) {
                        ((std/core/types/True() : bool ) as @pat@18: bool)
                           -> std/core/hnd/yield-extend((fn<<async,async,div,ndet,strands<d>|e>>(@y-x10988@0: (hnd/ev-index == 1 ssize_t)){
                            (std/async/async/@mlift-lift-interleaved-div@10760@11418(@uniq-x@10637@0, @y-x10988@0));
                          }));
                        ((@skip std/core/types/False() : bool ) as @pat@0@13: bool)
                           -> std/async/async/@mlift-lift-interleaved-div@10760@11418(@uniq-x@10637@0, x@13@12056);
                      });
                    }));
        (match ((std/core/hnd/yielding())) {
          ((std/core/types/True() : bool ) as @pat@3@4: bool)
             -> std/core/hnd/yield-extend((fn<<async,div,ndet,strands<d>|e>>(wild@0: ()){
              (std/async/async/@mlift-lift-interleaved-div@10760@11419(@uniq-xx@10638@0, ch@3, wild@0));
            }));
          ((@skip std/core/types/False() : bool ) as @pat@0@1@0: bool)
             -> std/async/async/@lift-interleaved-div@10760(ch@3, @uniq-xx@10638@0);
        });
      ((@skip std/core/types/Nil() : list<() -> <async,div,ndet,strands<d>|e> ()> ) as @uniq-pat@0@10639: (list<() -> <async,div,ndet,strands<d>|e> ()>))
         -> std/core/types/Unit;
    });
  };
// lifted local: interleaved-div, @spec-x10633
// specialized: std/core/list/foreach, on parameters @uniq-action@10630, using:
// @uniq-action@10630 = (fn<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>>(strand: () -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()){
//   std/async/async/async/@handle<(),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>,()>((std/async/async/@Hnd-async<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>,()>(3, (forall<a> std/core/types/@open<(total :: E),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>,(op : (() -> (io-noexn :: E) _b) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)> _b) -> (hnd/clause1 :: (V, V, (E, V) -> V, E, V) -> V)<() -> (io-noexn :: E) _b,_b,(std/async/async/async :: (E, V) -> V),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)>,()>,(op : (() -> (io-noexn :: E) _b) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)> _b) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)> (hnd/clause1 :: (V, V, (E, V) -> V, E, V) -> V)<() -> (io-noexn :: E) _b,_b,(std/async/async/async :: (E, V) -> V),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)>,()>>((std/core/hnd/clause-tail1<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>,(),(std/async/async/async :: (E, V) -> V),() -> (io-noexn :: E) _b,_b>))((fn<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>>(f: () -> (io-noexn :: E) a){
//         (std/core/types/@open<(std/async/async/async :: (E, V) -> V),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>,(action : () -> (io-noexn :: E) a) -> (std/async/async/async :: (E, V) -> V) a,(action : () -> (io-noexn :: E) a) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)> a>((fn<(std/async/async/async :: (E, V) -> V)>(action@2: () -> (io-noexn :: E) a){
//           (std/core/hnd/@perform1<() -> (io-noexn :: E) a,a,(std/async/async/async :: (E, V) -> V),(std/async/async/async :: (E, V) -> V)>((std/core/types/@open<(total :: E),(std/async/async/async :: (E, V) -> V),(i : hnd/ev-index) -> (hnd/ev :: ((E, V) -> V) -> V)<(std/async/async/async :: (E, V) -> V)>,(i : hnd/ev-index) -> (std/async/async/async :: (E, V) -> V) (hnd/ev :: ((E, V) -> V) -> V)<(std/async/async/async :: (E, V) -> V)>>((std/core/hnd/@evv-at<(std/async/async/async :: (E, V) -> V)>))((std/core/types/@open<(total :: E),(std/async/async/async :: (E, V) -> V),(i : int) -> ssize_t,(i : int) -> (std/async/async/async :: (E, V) -> V) ssize_t>(std/core/types/@make-ssize_t)(0)))), (forall<(e :: E),b> std/async/async/async-iox/@select<a,(e :: E),b>), action@2));
//         }))(f));
//       }))), (std/core/types/@open<(total :: E),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>,(op : (std/async/async/scope) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)> ()) -> (hnd/clause1 :: (V, V, (E, V) -> V, E, V) -> V)<std/async/async/scope,(),(std/async/async/async :: (E, V) -> V),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>,()>,(op : (std/async/async/scope) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)> ()) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)> (hnd/clause1 :: (V, V, (E, V) -> V, E, V) -> V)<std/async/async/scope,(),(std/async/async/async :: (E, V) -> V),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>,()>>((std/core/hnd/clause-tail1<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>,(),(std/async/async/async :: (E, V) -> V),std/async/async/scope,()>))((fn<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>>(scope@0: std/async/async/scope){
//         (std/core/types/@open<(std/async/async/async :: (E, V) -> V),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>,(scope : std/async/async/scope) -> (std/async/async/async :: (E, V) -> V) (),(scope : std/async/async/scope) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)> ()>((fn<(std/async/async/async :: (E, V) -> V)>(scope@1: std/async/async/scope){
//           (std/core/hnd/@perform1<std/async/async/scope,(),(std/async/async/async :: (E, V) -> V),(std/async/async/async :: (E, V) -> V)>((std/core/types/@open<(total :: E),(std/async/async/async :: (E, V) -> V),(i : hnd/ev-index) -> (hnd/ev :: ((E, V) -> V) -> V)<(std/async/async/async :: (E, V) -> V)>,(i : hnd/ev-index) -> (std/async/async/async :: (E, V) -> V) (hnd/ev :: ((E, V) -> V) -> V)<(std/async/async/async :: (E, V) -> V)>>((std/core/hnd/@evv-at<(std/async/async/async :: (E, V) -> V)>))((std/core/types/@open<(total :: E),(std/async/async/async :: (E, V) -> V),(i : int) -> ssize_t,(i : int) -> (std/async/async/async :: (E, V) -> V) ssize_t>(std/core/types/@make-ssize_t)(0)))), std/async/async/cancel/@select, scope@1));
//         }))(scope@0));
//       }))), (forall<a> std/core/types/@open<(total :: E),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>,(op : (x1 : (std/async/async/await-setup :: V -> V)<_b>, x2 : std/async/async/scope, x3 : bool, r : (hnd/resume-context :: (V, E, E, V) -> V)<(error :: V -> V)<_b>,<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)>,<(std/async/async/async :: (E, V) -> V),(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)>,()>) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)> ()) -> (hnd/clause1 :: (V, V, (E, V) -> V, E, V) -> V)<((std/async/async/await-setup :: V -> V)<_b>, std/async/async/scope, bool),(error :: V -> V)<_b>,(std/async/async/async :: (E, V) -> V),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)>,()>,(op : (x1 : (std/async/async/await-setup :: V -> V)<_b>, x2 : std/async/async/scope, x3 : bool, r : (hnd/resume-context :: (V, E, E, V) -> V)<(error :: V -> V)<_b>,<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)>,<(std/async/async/async :: (E, V) -> V),(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)>,()>) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)> ()) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)> (hnd/clause1 :: (V, V, (E, V) -> V, E, V) -> V)<((std/async/async/await-setup :: V -> V)<_b>, std/async/async/scope, bool),(error :: V -> V)<_b>,(std/async/async/async :: (E, V) -> V),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)>,()>>((std/core/hnd/clause-control-raw3<(std/async/async/await-setup :: V -> V)<_b>,std/async/async/scope,bool,(error :: V -> V)<_b>,<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>,<(std/async/async/async :: (E, V) -> V),(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>,(std/async/async/async :: (E, V) -> V),()>))((fn<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>>(setup: (std/async/async/await-setup :: V -> V)<a>, scope@0@0: std/async/async/scope, c: bool, rcontext: (hnd/resume-context :: (V, E, E, V) -> V)<(error :: V -> V)<a>,<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)>,<(std/async/async/async :: (E, V) -> V),(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)>,()>){
//         val _@0@0 : ()
//               = (std/core/types/@open<(std/async/async/async :: (E, V) -> V),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>,(setup : (std/async/async/await-setup :: V -> V)<a>, scope : std/async/async/scope, cancelable : bool, f : ((error :: V -> V)<a>) -> (io-noexn :: E) ()) -> (std/async/async/async :: (E, V) -> V) (),(setup : (std/async/async/await-setup :: V -> V)<a>, scope : std/async/async/scope, cancelable : bool, f : ((error :: V -> V)<a>) -> (io-noexn :: E) ()) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)> ()>((fn<(std/async/async/async :: (E, V) -> V)>(setup@0: (std/async/async/await-setup :: V -> V)<a>, scope@2: std/async/async/scope, cancelable@0: bool, f@0: ((error :: V -> V)<a>) -> (io-noexn :: E) ()){
//                 (std/core/hnd/@perform4<(std/async/async/await-setup :: V -> V)<a>,std/async/async/scope,bool,((error :: V -> V)<a>) -> (io-noexn :: E) (),(),(std/async/async/async :: (E, V) -> V),(std/async/async/async :: (E, V) -> V)>((std/core/types/@open<(total :: E),(std/async/async/async :: (E, V) -> V),(i : hnd/ev-index) -> (hnd/ev :: ((E, V) -> V) -> V)<(std/async/async/async :: (E, V) -> V)>,(i : hnd/ev-index) -> (std/async/async/async :: (E, V) -> V) (hnd/ev :: ((E, V) -> V) -> V)<(std/async/async/async :: (E, V) -> V)>>((std/core/hnd/@evv-at<(std/async/async/async :: (E, V) -> V)>))((std/core/types/@open<(total :: E),(std/async/async/async :: (E, V) -> V),(i : int) -> ssize_t,(i : int) -> (std/async/async/async :: (E, V) -> V) ssize_t>(std/core/types/@make-ssize_t)(0)))), (forall<(e :: E),b> std/async/async/no-await/@select<a,(e :: E),b>), setup@0, scope@2, cancelable@0, f@0));
//               }))(setup, scope@0@0, c, (fn<(io-noexn :: E)>(res@0: (error :: V -> V)<a>){
//                   (match ((std/core/types/ref/(!)<(std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>,<(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>,(console/console :: X),(div :: X),(fsys :: X),(ndet :: X),(net :: X),(ui :: X)>,(global :: H)>((match (ch) {
//                       ((@skip std/async/async/Channel((@pat@0@4: int) : int, (@x@0: (ref :: (H, V) -> V)<(global :: H),(std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>>) : (ref :: (H, V) -> V)<(global :: H),(std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>>) : (std/async/async/channel :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()> ) as @pat@5: ((std/async/async/channel :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>))
//                          -> @x@0;
//                     }), (std/core/types/@Hdiv<(global :: H),(std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>,<(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>,(console/console :: X),(div :: X),(fsys :: X),(ndet :: X),(net :: X),(ui :: X)>>)))) {
//                     ((std/async/async/Empty() : (std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()> ) as @pat@6: ((std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>))
//                        -> std/core/types/set<(std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>,(global :: H)>((match (ch) {
//                           ((@skip std/async/async/Channel((@pat@0@4: int) : int, (@x@0: (ref :: (H, V) -> V)<(global :: H),(std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>>) : (ref :: (H, V) -> V)<(global :: H),(std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>>) : (std/async/async/channel :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()> ) as @pat@5: ((std/async/async/channel :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>))
//                              -> @x@0;
//                         }), (std/async/async/Values<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>((fn<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>>(){
//                             (std/core/hnd/resume<(error :: V -> V)<a>,<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>,<(std/async/async/async :: (E, V) -> V),(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>,()>(rcontext, res@0));
//                           }), (std/core/types/Nil<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>))));
//                     ((std/async/async/Values((v: () -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()) : () -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> (), (vs: (list :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>) : (list :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>) : (std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()> ) as @pat@0@6: ((std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>))
//                        -> val ys@10139 : (list :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>;
//                           val values@0@10137 : ? ((list :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>);
//                       std/core/types/set<(std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>,(global :: H)>((match (ch) {
//                           ((@skip std/async/async/Channel((@pat@0@4: int) : int, (@x@0: (ref :: (H, V) -> V)<(global :: H),(std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>>) : (ref :: (H, V) -> V)<(global :: H),(std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>>) : (std/async/async/channel :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()> ) as @pat@5: ((std/async/async/channel :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>))
//                              -> @x@0;
//                         }), (std/async/async/Values<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>(v, (match (values@0@10137) {
//                             ((std/core/types/@Optional((@uniq-values@967@0: (list :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>) : (list :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>) : ? ((list :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>) ) as @pat@8: ? ((list :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>))
//                                -> @uniq-values@967@0;
//                             ((@skip std/core/types/@None() : ? ((list :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>) ) as @pat@0@7: ? ((list :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>))
//                                -> std/core/types/Nil<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>;
//                           }))));
//                     ((@skip std/async/async/Waiting((l: (() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()) : (() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) (), (ls: (list :: V -> V)<(() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()>) : (list :: V -> V)<(() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()>) : (std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()> ) as @pat@1@2: ((std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>))
//                        -> val _@0 : ()
//                                 = std/core/types/set<(std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>,(global :: H)>((match (ch) {
//                                     ((@skip std/async/async/Channel((@pat@0@4: int) : int, (@x@0: (ref :: (H, V) -> V)<(global :: H),(std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>>) : (ref :: (H, V) -> V)<(global :: H),(std/async/async/channel-state :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>>) : (std/async/async/channel :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()> ) as @pat@5: ((std/async/async/channel :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>))
//                                        -> @x@0;
//                                   }), (match (ls) {
//                                     ((std/core/types/Nil() : (list :: V -> V)<(() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()> ) as @pat@10: ((list :: V -> V)<(() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()>))
//                                        -> std/async/async/Empty<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>;
//                                     ((@skip std/core/types/Cons((l@0: (() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()) : (() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) (), (ls@0: (list :: V -> V)<(() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()>) : (list :: V -> V)<(() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()>) : (list :: V -> V)<(() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()> ) as @pat@0@5: ((list :: V -> V)<(() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()) -> ((io-noexn :: E) == 3 <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)>) ()>))
//                                        -> std/async/async/Waiting<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)> ()>(l@0, ls@0);
//                                   }));
//                       l((fn<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>>(){
//                         (std/core/hnd/resume<(error :: V -> V)<a>,<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>,<(std/async/async/async :: (E, V) -> V),(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>,()>(rcontext, res@0));
//                       }));
//                   });
//                 })));
//         std/core/types/Unit;
//       }))), (forall<a> std/core/types/@open<(total :: E),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>,(op : ((std/async/async/await-setup :: V -> V)<_b>, std/async/async/scope, bool, ((error :: V -> V)<_b>) -> (io-noexn :: E) ()) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)> ()) -> (hnd/clause1 :: (V, V, (E, V) -> V, E, V) -> V)<((std/async/async/await-setup :: V -> V)<_b>, std/async/async/scope, bool, ((error :: V -> V)<_b>) -> (io-noexn :: E) ()),(),(std/async/async/async :: (E, V) -> V),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)>,()>,(op : ((std/async/async/await-setup :: V -> V)<_b>, std/async/async/scope, bool, ((error :: V -> V)<_b>) -> (io-noexn :: E) ()) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)> ()) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)> (hnd/clause1 :: (V, V, (E, V) -> V, E, V) -> V)<((std/async/async/await-setup :: V -> V)<_b>, std/async/async/scope, bool, ((error :: V -> V)<_b>) -> (io-noexn :: E) ()),(),(std/async/async/async :: (E, V) -> V),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)>,()>>((std/core/hnd/clause-tail4<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>,(),(std/async/async/async :: (E, V) -> V),(std/async/async/await-setup :: V -> V)<_b>,std/async/async/scope,bool,((error :: V -> V)<_b>) -> (io-noexn :: E) (),()>))((fn<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>>(setup@0@0: (std/async/async/await-setup :: V -> V)<a>, scope@1@0: std/async/async/scope, c@0: bool, f@0@0: ((error :: V -> V)<a>) -> (io-noexn :: E) ()){
//         (std/core/types/@open<(std/async/async/async :: (E, V) -> V),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<b>|(e :: E)>,(setup : (std/async/async/await-setup :: V -> V)<a>, scope : std/async/async/scope, cancelable : bool, f : ((error :: V -> V)<a>) -> (io-noexn :: E) ()) -> (std/async/async/async :: (E, V) -> V) (),(setup : (std/async/async/await-setup :: V -> V)<a>, scope : std/async/async/scope, cancelable : bool, f : ((error :: V -> V)<a>) -> (io-noexn :: E) ()) -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<c>|(e :: E)> ()>((fn<(std/async/async/async :: (E, V) -> V)>(setup@1: (std/async/async/await-setup :: V -> V)<a>, scope@3: std/async/async/scope, cancelable@0@0: bool, f@1: ((error :: V -> V)<a>) -> (io-noexn :: E) ()){
//           (std/core/hnd/@perform4<(std/async/async/await-setup :: V -> V)<a>,std/async/async/scope,bool,((error :: V -> V)<a>) -> (io-noexn :: E) (),(),(std/async/async/async :: (E, V) -> V),(std/async/async/async :: (E, V) -> V)>((std/core/types/@open<(total :: E),(std/async/async/async :: (E, V) -> V),(i : hnd/ev-index) -> (hnd/ev :: ((E, V) -> V) -> V)<(std/async/async/async :: (E, V) -> V)>,(i : hnd/ev-index) -> (std/async/async/async :: (E, V) -> V) (hnd/ev :: ((E, V) -> V) -> V)<(std/async/async/async :: (E, V) -> V)>>((std/core/hnd/@evv-at<(std/async/async/async :: (E, V) -> V)>))((std/core/types/@open<(total :: E),(std/async/async/async :: (E, V) -> V),(i : int) -> ssize_t,(i : int) -> (std/async/async/async :: (E, V) -> V) ssize_t>(std/core/types/@make-ssize_t)(0)))), (forall<(e :: E),b> std/async/async/no-await/@select<a,(e :: E),b>), setup@1, scope@3, cancelable@0@0, f@1));
//         }))(setup@0@0, scope@1@0, c@0, f@0@0));
//       }))))), (fn<<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>>(@res: ()){
//       @res;
//     }), (fn<<(std/async/async/async :: (E, V) -> V),(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>>(){
//       (std/core/hnd/@mask-at<(),<(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>,<(std/async/async/async :: (E, V) -> V),(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>>((std/core/hnd/@evv-index<<(std/async/async/async :: (E, V) -> V),(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>>(std/async/async/async/@tag)), std/core/types/True, strand));
//     }));
// },Own)
fun @lift-interleaved-div@10759 : forall<_a,_b,_c,d,e> (ch : channel<() -> <async,div,ndet,strands<d>|e> ()>, @uniq-xs@10629 : list<() -> <async,div,ndet,strands<d>|e> ()>) -> <async,div,ndet,strands<d>|e> ()
  = forall<_a,_b,_c,d,e> fn<<async,div,ndet,strands<d>|e>>(ch: channel<() -> <async,div,ndet,strands<d>|e> ()>, @uniq-xs@10629: list<() -> <async,div,ndet,strands<d>|e> ()>){
    (match (@uniq-xs@10629) {
      ((std/core/types/Nil() : list<() -> <async,div,ndet,strands<d>|e> ()> ) as @uniq-pat@0@10631: (list<() -> <async,div,ndet,strands<d>|e> ()>))
         -> std/core/types/Unit;
      (@uniq-pat@10632: (list<() -> <async,div,ndet,strands<d>|e> ()>))
         -> std/async/async/@lift-interleaved-div@10760(ch, @uniq-xs@10629);
    });
  };
// monadic lift
fun @mlift-lift-interleaved-div@10761@11420 : forall<_a,b,e> (ch : channel<() -> <async,div,ndet,strands<b>|e> ()>, @c-x10999 : ()) -> ()
  = forall<_a,b,e> fn(ch: channel<() -> <async,div,ndet,strands<b>|e> ()>, @c-x10999: ()){
    std/async/async/@lift-interleaved-div@10761(ch);
  };
// monadic lift
fun @mlift-lift-interleaved-div@10761@11421 : forall<_a,b,e> (ch : channel<() -> <async,div,ndet,strands<b>|e> ()>, @y-x10997 : error<() -> <async,div,ndet,strands<b>|e> ()>) -> <async,ndet,div,strands<b>|e> ()
  = forall<_a,b,e> fn<<async,ndet,div,strands<b>|e>>(ch@0: channel<() -> <async,div,ndet,strands<b>|e> ()>, @y-x10997: error<() -> <async,div,ndet,strands<b>|e> ()>){
    val x@12058 : ()
          = (match (@y-x10997) {
            ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@3@0: string), (@pat@4@0: exception-info)) : exception ) as @pat@2@1: exception)) : error<() -> <async,div,ndet,strands<b>|e> ()> ) as @pat@1@3@0: (error<() -> <async,div,ndet,strands<b>|e> ()>))
               -> std/core/types/Unit;
            ((@skip std/core/exn/Ok((strand-resume: () -> <async,div,ndet,strands<b>|e> ())) : error<() -> <async,div,ndet,strands<b>|e> ()> ) as @pat@5@0@0: (error<() -> <async,div,ndet,strands<b>|e> ()>))
               -> strand-resume();
          });
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-extend((fn(@c-x10999@0: ()){
          (std/async/async/@mlift-lift-interleaved-div@10761@11420(ch@0, @c-x10999@0));
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> std/async/async/@mlift-lift-interleaved-div@10761@11420(ch@0, x@12058);
    });
  };
// monadic lift
fun @mlift-lift-interleaved-div@10761@11422 : forall<_a,b,e> (ch : channel<() -> <async,div,ndet,strands<b>|e> ()>, @y-x10996 : bool) -> <strands<b>,div,async,ndet|e> ()
  = forall<_a,b,e> fn<<strands<b>,div,async,ndet|e>>(ch@1: channel<() -> <async,div,ndet,strands<b>|e> ()>, @y-x10996: bool){
    (match (@y-x10996) {
      ((std/core/types/True() : bool ) as @uniq-pat@10644: bool)
         -> val i@12062 : (hnd/ev-index == 1 ssize_t)
              = std/core/hnd/@evv-index(std/async/async/async/@tag);
            val w : hnd/evv<<async,ndet,div,strands<b>|e>>
              = std/core/hnd/evv-swap-create1(i@12062);
            val y : error<() -> <async,div,ndet,strands<b>|e> ()>
              = std/async/async/receivex(ch@1, (std/core/types/@Optional(std/core/types/False)));
            val _ : ()
              = std/core/hnd/evv-set(w);
            val x@0@12060 : error<() -> <async,div,ndet,strands<b>|e> ()>
              = (match ((std/core/hnd/yielding())) {
                ((std/core/types/True() : bool ) as @pat@2: bool)
                   -> std/core/hnd/yield-cont((forall<c> fn<<async,ndet,div,strands<b>|e>>(cont: (c) -> <async,ndet,div,strands<b>|e> error<() -> <async,div,ndet,strands<b>|e> ()>, res: c){
                    std/core/hnd/open-at1(i@12062, cont, res);
                  }));
                ((@skip std/core/types/False() : bool ) as @pat@0@1: bool)
                   -> y;
              });
        (match ((std/core/hnd/yielding())) {
          ((std/core/types/True() : bool ) as @pat@1: bool)
             -> std/core/hnd/yield-extend((fn<<async,ndet,div,strands<b>|e>>(@y-x10997@0: error<() -> <async,div,ndet,strands<b>|e> ()>){
              (std/async/async/@mlift-lift-interleaved-div@10761@11421(ch@1, @y-x10997@0));
            }));
          ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
             -> std/async/async/@mlift-lift-interleaved-div@10761@11421(ch@1, x@0@12060);
        });
      ((@skip std/core/types/False() : bool ) as @uniq-pat@0@10645: bool)
         -> std/core/types/Unit;
    });
  };
// lifted local: interleaved-div, @spec-x10646
// specialized: std/core/while, on parameters @uniq-predicate@10642, @uniq-action@10643, using:
// @uniq-predicate@10642 = (fn<<(div :: X),(std/async/async/strands :: (V, E, V) -> V)<a>,(std/async/async/async :: (E, V) -> V),(ndet :: X)|(e :: E)>>(){
//   std/core/types/@open<((std/async/async/strands :: (V, E, V) -> V)<a>),<(std/async/async/strands :: (V, E, V) -> V)<a>,(div :: X),(std/async/async/async :: (E, V) -> V),(ndet :: X)|(e :: E)>,() -> ((std/async/async/strands :: (V, E, V) -> V)<a>) bool,() -> <(std/async/async/strands :: (V, E, V) -> V)<a>,(div :: X),(std/async/async/async :: (E, V) -> V),(ndet :: X)|(e :: E)> bool>((fn<((std/async/async/strands :: (V, E, V) -> V)<a>)>(){
//     (std/core/hnd/@perform0<bool,((std/async/async/strands :: (V, E, V) -> V)<a>),(std/async/async/strands :: (V, E, V) -> V)<_a>>((std/core/types/@open<(total :: E),((std/async/async/strands :: (V, E, V) -> V)<a>),(i : hnd/ev-index) -> (hnd/ev :: ((E, V) -> V) -> V)<(std/async/async/strands :: (V, E, V) -> V)<_a>>,(i : hnd/ev-index) -> ((std/async/async/strands :: (V, E, V) -> V)<b>) (hnd/ev :: ((E, V) -> V) -> V)<(std/async/async/strands :: (V, E, V) -> V)<_a>>>((std/core/hnd/@evv-at<(std/async/async/strands :: (V, E, V) -> V)<_a>>))((std/core/types/@open<(total :: E),((std/async/async/strands :: (V, E, V) -> V)<a>),(i : int) -> ssize_t,(i : int) -> ((std/async/async/strands :: (V, E, V) -> V)<a>) ssize_t>(std/core/types/@make-ssize_t)(0)))), (forall<(e :: E),a> std/async/async/strands-are-busy/@select<_b,(e :: E),a>)));
//   }))();
// },Own)
// @uniq-action@10643 = (fn<<(div :: X),(std/async/async/strands :: (V, E, V) -> V)<a>,(std/async/async/async :: (E, V) -> V),(ndet :: X)|(e :: E)>>(){
//   match ((std/core/types/@open<<(std/async/async/async :: (E, V) -> V),(ndet :: X)>,<(std/async/async/async :: (E, V) -> V),(ndet :: X),(div :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)>,(ch : (std/async/async/channel :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)> ()>, cancelable : ? bool) -> <(std/async/async/async :: (E, V) -> V),(ndet :: X)> (error :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)> ()>,(ch : (std/async/async/channel :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)> ()>, cancelable : ? bool) -> <(std/async/async/async :: (E, V) -> V),(ndet :: X),(div :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)> (error :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)> ()>>((std/async/async/receivex<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)> ()>))(ch, (std/core/types/@Optional<bool>(std/core/types/False))))) {
//     ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@3@0: string) : string, (@pat@4@0: exception-info) : exception-info) : exception ) as @pat@2@1: exception) : exception) : (error :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)> ()> ) as @pat@1@3@0: ((error :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>))
//        -> std/core/types/Unit;
//     ((@skip std/core/exn/Ok((strand-resume: () -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()) : () -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)> ()) : (error :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<a>|(e :: E)> ()> ) as @pat@5@0: ((error :: V -> V)<() -> <(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X),(std/async/async/strands :: (V, E, V) -> V)<6667>|(6668 :: E)> ()>))
//        -> strand-resume();
//   };
// },Own)
fun @lift-interleaved-div@10761 : forall<_a,b,e> (ch : channel<() -> <async,div,ndet,strands<b>|e> ()>) -> <div,strands<b>,async,ndet|e> ()
  = forall<_a,b,e> fn<<div,strands<b>,async,ndet|e>>(ch@2: channel<() -> <async,div,ndet,strands<b>|e> ()>){
    val i@0@12069 : hnd/ev-index
      = std/core/hnd/@evv-index(std/async/async/strands/@tag);
    val w@0 : hnd/evv<<strands<b>,div,async,ndet|e>>
      = std/core/hnd/evv-swap-create1(i@0@12069);
    val ev@12071 : hnd/ev<strands<_a>>
      = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
    val y@0 : bool
      = (match (ev@12071) {
        ((@skip std/core/hnd/Ev<e1,c>((@pat@0@4: hnd/htag<strands<_a>>), (m: hnd/marker<e1,c>), (h: (strands<_a>)<e1,c>), (@pat@1@0: hnd/evv<e1>)) : hnd/ev<strands<_a>> ) as @pat@5: (hnd/ev<strands<_a>>))
           -> (match (h) {
            ((@skip std/async/async/@Hnd-strands((@pat@0@2: int), (@pat@1@1: hnd/clause2<int,error<_a>,(),strands<_a>,e1,c>), (@fun-strands-are-busy: hnd/clause0<bool,strands<_a>,e1,c>)) : strands<_a,e1,c> ) as @pat@3: (strands<_a,e1,c>))
               -> (match (@fun-strands-are-busy) {
                ((@skip std/core/hnd/Clause0((f@1: (hnd/marker<e1,c>, hnd/ev<strands<_a>>) -> e1 bool)) : hnd/clause0<bool,strands<_a>,e1,c> ) as @pat@2@0: (hnd/clause0<bool,strands<_a>,e1,c>))
                   -> f@1(m, ev@12071);
              });
          });
      });
    val _ : ()
      = std/core/hnd/evv-set(w@0);
    val x@1@12066 : bool
      = (match ((std/core/hnd/yielding())) {
        ((std/core/types/True() : bool ) as @pat@4: bool)
           -> std/core/hnd/yield-cont((forall<c> fn<<strands<b>,div,async,ndet|e>>(cont@0: (c) -> <strands<b>,div,async,ndet|e> bool, res@0: c){
            std/core/hnd/open-at1(i@0@12069, cont@0, res@0);
          }));
        ((@skip std/core/types/False() : bool ) as @pat@0@3: bool)
           -> y@0;
      });
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat@3@1: bool)
         -> std/core/hnd/yield-extend((fn<<strands<b>,div,async,ndet|e>>(@y-x10996@0: bool){
          (std/async/async/@mlift-lift-interleaved-div@10761@11422(ch@2, @y-x10996@0));
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0@2@0: bool)
         -> (match (x@1@12066) {
          ((std/core/types/True() : bool ) as @uniq-pat@10644@0: bool)
             -> val i@1@12076 : (hnd/ev-index == 1 ssize_t)
                  = std/core/hnd/@evv-index(std/async/async/async/@tag);
                val w@1 : hnd/evv<<async,ndet,div,strands<b>|e>>
                  = std/core/hnd/evv-swap-create1(i@1@12076);
                val y@1 : error<() -> <async,div,ndet,strands<b>|e> ()>
                  = std/async/async/receivex(ch@2, (std/core/types/@Optional(std/core/types/False)));
                val _ : ()
                  = std/core/hnd/evv-set(w@1);
                val x@2@12073 : error<() -> <async,div,ndet,strands<b>|e> ()>
                  = (match ((std/core/hnd/yielding())) {
                    ((std/core/types/True() : bool ) as @pat@7: bool)
                       -> std/core/hnd/yield-cont((forall<c> fn<<async,ndet,div,strands<b>|e>>(cont@1: (c) -> <async,ndet,div,strands<b>|e> error<() -> <async,div,ndet,strands<b>|e> ()>, res@1: c){
                        std/core/hnd/open-at1(i@1@12076, cont@1, res@1);
                      }));
                    ((@skip std/core/types/False() : bool ) as @pat@0@6: bool)
                       -> y@1;
                  });
            (match ((std/core/hnd/yielding())) {
              ((std/core/types/True() : bool ) as @pat@6: bool)
                 -> std/core/hnd/yield-extend((fn<<async,ndet,div,strands<b>|e>>(@y-x10997@1: error<() -> <async,div,ndet,strands<b>|e> ()>){
                  (std/async/async/@mlift-lift-interleaved-div@10761@11421(ch@2, @y-x10997@1));
                }));
              ((@skip std/core/types/False() : bool ) as @pat@0@5: bool)
                 -> val x@3@12080 : ()
                          = (match (x@2@12073) {
                            ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@3@0@0: string), (@pat@4@0@0: exception-info)) : exception ) as @pat@2@1@0: exception)) : error<() -> <async,div,ndet,strands<b>|e> ()> ) as @pat@1@3@0@0: (error<() -> <async,div,ndet,strands<b>|e> ()>))
                               -> std/core/types/Unit;
                            ((@skip std/core/exn/Ok((strand-resume@0: () -> <async,div,ndet,strands<b>|e> ())) : error<() -> <async,div,ndet,strands<b>|e> ()> ) as @pat@5@0@0@0: (error<() -> <async,div,ndet,strands<b>|e> ()>))
                               -> strand-resume@0();
                          });
                (match ((std/core/hnd/yielding())) {
                  ((std/core/types/True() : bool ) as @pat@8: bool)
                     -> std/core/hnd/yield-extend((fn(@c-x10999@1: ()){
                      (std/async/async/@mlift-lift-interleaved-div@10761@11420(ch@2, @c-x10999@1));
                    }));
                  ((@skip std/core/types/False() : bool ) as @pat@0@7: bool)
                     -> std/async/async/@lift-interleaved-div@10761(ch@2);
                });
            });
          ((@skip std/core/types/False() : bool ) as @uniq-pat@0@10645@0: bool)
             -> std/core/types/Unit;
        });
    });
  };
// monadic lift
fun @mlift-interleaved-div@11423 : forall<a,e> (wild_@2 : ()) -> <div,strands<a>,async,ndet|e> ()
  = forall<a,e> fn<<div,strands<a>,async,ndet|e>>(wild_@2: ()){
    std/core/types/Unit;
  };
// monadic lift
fun @mlift-interleaved-div@11424 : forall<_a,b,e> (ch : channel<() -> <async,div,ndet,strands<b>|e> ()>, wild_@1 : ()) -> <async,div,ndet,strands<b>|e> ()
  = forall<_a,b,e> fn<<async,div,ndet,strands<b>|e>>(ch: channel<() -> <async,div,ndet,strands<b>|e> ()>, wild_@1: ()){
    val x@12083 : ()
          = std/async/async/@lift-interleaved-div@10761(ch);
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-extend((fn<<div,strands<b>,async,ndet|e>>(wild_@2: ()){
          std/core/types/Unit;
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> std/core/types/Unit;
    });
  };
// monadic lift
fun @mlift-interleaved-div@11425 : forall<_a,_b,_c,_d,a1,e> (strands : list<() -> <async,div,ndet,strands<a1>|e> ()>, ch : channel<() -> <async,div,ndet,strands<a1>|e> ()>) -> <async,div,ndet,strands<a1>|e> ()
  = forall<_a,_b,_c,_d,a1,e> fn<<async,div,ndet,strands<a1>|e>>(strands: list<() -> <async,div,ndet,strands<a1>|e> ()>, ch: channel<() -> <async,div,ndet,strands<a1>|e> ()>){
    val x@12086 : ()
          = std/async/async/@lift-interleaved-div@10759(ch, strands);
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-extend((fn<<async,div,ndet,strands<a1>|e>>(wild_@1: ()){
          (std/async/async/@mlift-interleaved-div@11424(ch, wild_@1));
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> std/async/async/@mlift-interleaved-div@11424(ch, x@12086);
    });
  };
// monadic lift
fun @mlift-interleaved-div@11426 : forall<_a,_b,_c,_d,a1,e> (strands : list<() -> <async,div,ndet,strands<a1>|e> ()>) -> <async,div,ndet,strands<a1>|e> ()
  = forall<_a,_b,_c,_d,a1,e> fn<<async,div,ndet,strands<a1>|e>>(strands: list<() -> <async,div,ndet,strands<a1>|e> ()>){
    val i@12090 : hnd/ev-index
      = std/core/hnd/@evv-index(std/async/async/async/@tag);
    val w : hnd/evv<<async,div,ndet,strands<a1>|e>>
      = std/core/hnd/evv-swap-create1(i@12090);
    val ev@12092 : hnd/ev<async>
      = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
    val y : channel<() -> <async,div,ndet,strands<a1>|e> ()>
      = (match (ev@12092) {
        ((@skip std/core/hnd/Ev<e1,b1>((@pat@0@1: hnd/htag<async>), (m: hnd/marker<e1,b1>), (h: async<e1,b1>), (@pat@1@0: hnd/evv<e1>)) : hnd/ev<async> ) as @pat@2: (hnd/ev<async>))
           -> (match (h) {
            ((@skip std/async/async/@Hnd-async((@pat@0: int), (@ctl-async-iox: forall<c1> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c1,c1,async,e1,b1>), (@pat@1: hnd/clause1<scope,(),async,e1,b1>), (@pat@2@0: forall<c1> hnd/clause1<((await-setup<c1> == 4 (cb : (error<c1>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc
   <global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c1>,async,e1,b1>), (@pat@3: (forall<c1> hnd/clause1<((await-setup<c1> == 4 (cb : (error<c1>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global
   > == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c1>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>
   ) ()),(),async,e1,b1>))) : async<e1,b1> ) as @pat: (async<e1,b1>))
               -> (match (@ctl-async-iox) {
                ((@skip std/core/hnd/Clause1((f@0: (hnd/marker<e1,b1>, hnd/ev<async>, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) channel<() -> <async,div,ndet,strands<a1>|e> ()>) -> e1 channel<() -> <async,div,ndet,strands<a1>|e> ()>)) : hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) channel<() -> <async,div
   ,ndet,strands<a1>|e> ()>,channel<() -> <async,div,ndet,strands<a1>|e> ()>,async,e1,b1> ) as @pat@2@0@0: (hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) channel<() -> <async,div,ndet,strands<a1>|e> ()>,channel<() -> <async,div,ndet,strands<a1>|e> ()>,async,e1,b1>))
                   -> f@0(m, ev@12092, (fn<(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>(){
                      val u : int
                        = (std/core/types/ref/(!)(std/core/unique-count, std/core/types/@Hnodiv));
                      val _ : ()
                        = (std/core/types/set(std/core/unique-count, (std/core/int/int-add(u, 1))));
                      (std/async/async/Channel(u, (std/core/types/ref(std/async/async/Empty))));
                    }));
              });
          });
      });
    val _ : ()
      = std/core/hnd/evv-set(w);
    val x@12088 : channel<() -> <async,div,ndet,strands<a1>|e> ()>
      = (match ((std/core/hnd/yielding())) {
        ((std/core/types/True() : bool ) as @pat@1@1: bool)
           -> std/core/hnd/yield-cont((forall<b1> fn<<async,div,ndet,strands<a1>|e>>(cont: (b1) -> <async,div,ndet,strands<a1>|e> channel<() -> <async,div,ndet,strands<a1>|e> ()>, res: b1){
            std/core/hnd/open-at1(i@12090, cont, res);
          }));
        ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
           -> y;
      });
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat@4: bool)
         -> std/core/hnd/yield-extend((fn<<async,div,ndet,strands<a1>|e>>(ch: channel<() -> <async,div,ndet,strands<a1>|e> ()>){
          (std/async/async/@mlift-interleaved-div@11425(strands, ch));
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0@2: bool)
         -> std/async/async/@mlift-interleaved-div@11425(strands, x@12088);
    });
  };
fun interleaved-div : forall<a,e> (xs : list<() -> <async-exn|e> a>) -> <async,ndet,div,strands<a>|e> ()
  = forall<a,e> fn<<async,ndet,div,strands<a>|e>>(xs: list<() -> <async-exn|e> a>){
    val x@12095 : list<() -> <async,div,ndet,strands<a>|e> ()>
          = std/async/async/@lift-interleaved-div@10757(xs);
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-extend((fn<<async,div,ndet,strands<a>|e>>(strands: list<() -> <async,div,ndet,strands<a>|e> ()>){
          (std/async/async/@mlift-interleaved-div@11426(strands));
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> val i@12101 : (hnd/ev-index == 1 ssize_t)
              = std/core/hnd/@evv-index(std/async/async/async/@tag);
            val w : hnd/evv<<async,div,ndet,strands<a>|e>>
              = std/core/hnd/evv-swap-create1(i@12101);
            val ev@12103 : hnd/ev<async>
              = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
            val y : channel<() -> <async,div,ndet,strands<a>|e> ()>
              = (match (ev@12103) {
                ((@skip std/core/hnd/Ev<e1,b>((@pat@0@2: hnd/htag<async>), (m: hnd/marker<e1,b>), (h: async<e1,b>), (@pat@1@0: hnd/evv<e1>)) : hnd/ev<async> ) as @pat@3: (hnd/ev<async>))
                   -> (match (h) {
                    ((@skip std/async/async/@Hnd-async((@pat@0@0: int), (@ctl-async-iox: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e1,b>), (@pat@1@1: hnd/clause1<scope,(),async,e1,b>), (@pat@2: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,
   alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e1,b>), (@pat@3@0: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<
   global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>
   >)>)>) ()),(),async,e1,b>))) : async<e1,b> ) as @pat@1: (async<e1,b>))
                       -> (match (@ctl-async-iox) {
                        ((@skip std/core/hnd/Clause1((f@0: (hnd/marker<e1,b>, hnd/ev<async>, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) channel<() -> <async,div,ndet,strands<a>|e> ()>) -> e1 channel<() -> <async,div,ndet,strands<a>|e> ()>)) : hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) channel<() -> <
   async,div,ndet,strands<a>|e> ()>,channel<() -> <async,div,ndet,strands<a>|e> ()>,async,e1,b> ) as @pat@2@0: (hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) channel<() -> <async,div,ndet,strands<a>|e> ()>,channel<() -> <async,div,ndet,strands<a>|e> ()>,async,e1,b>))
                           -> f@0(m, ev@12103, (fn<(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>(){
                              val u : int
                                = (std/core/types/ref/(!)(std/core/unique-count, std/core/types/@Hnodiv));
                              val _ : ()
                                = (std/core/types/set(std/core/unique-count, (std/core/int/int-add(u, 1))));
                              (std/async/async/Channel(u, (std/core/types/ref(std/async/async/Empty))));
                            }));
                      });
                  });
              });
            val _ : ()
              = std/core/hnd/evv-set(w);
            val x@0@12098 : channel<() -> <async,div,ndet,strands<a>|e> ()>
              = (match ((std/core/hnd/yielding())) {
                ((std/core/types/True() : bool ) as @pat@2@1: bool)
                   -> std/core/hnd/yield-cont((forall<b> fn<<async,div,ndet,strands<a>|e>>(cont: (b) -> <async,div,ndet,strands<a>|e> channel<() -> <async,div,ndet,strands<a>|e> ()>, res: b){
                    std/core/hnd/open-at1(i@12101, cont, res);
                  }));
                ((@skip std/core/types/False() : bool ) as @pat@0@1: bool)
                   -> y;
              });
        (match ((std/core/hnd/yielding())) {
          ((std/core/types/True() : bool ) as @pat@1@2: bool)
             -> std/core/hnd/yield-extend((fn<<async,div,ndet,strands<a>|e>>(ch: channel<() -> <async,div,ndet,strands<a>|e> ()>){
              (std/async/async/@mlift-interleaved-div@11425(x@12095, ch));
            }));
          ((@skip std/core/types/False() : bool ) as @pat@0@0@0: bool)
             -> val x@2@12106 : ()
                      = std/async/async/@lift-interleaved-div@10759(x@0@12098, x@12095);
            (match ((std/core/hnd/yielding())) {
              ((std/core/types/True() : bool ) as @pat@4: bool)
                 -> std/core/hnd/yield-extend((fn<<async,div,ndet,strands<a>|e>>(wild_@1: ()){
                  (std/async/async/@mlift-interleaved-div@11424(x@0@12098, wild_@1));
                }));
              ((@skip std/core/types/False() : bool ) as @pat@0@3: bool)
                 -> val x@3@12109 : ()
                          = std/async/async/@lift-interleaved-div@10761(x@0@12098);
                (match ((std/core/hnd/yielding())) {
                  ((std/core/types/True() : bool ) as @pat@5: bool)
                     -> std/core/hnd/yield-extend((fn<<div,strands<a>,async,ndet|e>>(wild_@2: ()){
                      std/core/types/Unit;
                    }));
                  ((@skip std/core/types/False() : bool ) as @pat@0@4: bool)
                     -> std/core/types/Unit;
                });
            });
        });
    });
  };
// lifted local: interleavedn, @spec-x10651
// specialized: std/core/list/map, on parameters @uniq-f@10648, using:
// @uniq-f@10648 = (std/core/types/@open<(total :: E),<(local :: H -> X)<(h :: H)>,(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X)|(e :: E)>,(tuple2 : (int, (error :: V -> V)<a>)) -> (error :: V -> V)<a>,(tuple2 : (int, (error :: V -> V)<a>)) -> <(local :: H -> X)<(h :: H)>,(std/async/async/async :: (E, V) -> V),(div :: X),(ndet :: X)|(e :: E)> (error :: V -> V)<a>>((std/core/types/tuple2/snd<int,(error :: V -> V)<a>>)),Own)
fun @lift-interleavedn@10762 : forall<h,a,e> (@uniq-xs@10647 : list<(int, error<a>)>) -> <local<h>,async,div,ndet|e> list<error<a>>
  = forall<h,a,e> fn<<local<h>,async,div,ndet|e>>(@uniq-xs@10647: list<(int, error<a>)>){
    (match (@uniq-xs@10647) {
      ((std/core/types/Nil() : list<(int, error<a>)> ) as @uniq-pat@0@10649: (list<(int, error<a>)>))
         -> std/core/types/Nil;
      (@uniq-pat@10650: (list<(int, error<a>)>))
         -> std/core/list/@unroll-map@10010(@uniq-xs@10647, std/core/types/tuple2/snd);
    });
  };
// monadic lift
fun @mlift-interleavedn@11427 : forall<h,a,e> (@y-x11009 : (int, list<(int, error<a>)>), cr : local-var<h,(int, list<(int, error<a>)>)>, idx : int, res : error<a>, @y-x11010 : (int, list<(int, error<a>)>)) -> <local<h>,async,div,ndet|e> ()
  = forall<h,a,e> fn<<local<h>,async,div,ndet|e>>(@y-x11009: (int, list<(int, error<a>)>), cr: local-var<h,(int, list<(int, error<a>)>)>, idx: int, res: error<a>, @y-x11010: (int, list<(int, error<a>)>)){
    val w : hnd/evv<<local<h>,async,div,ndet|e>>
      = std/core/hnd/evv-swap-create0();
    val keep : ()
      = std/core/hnd/evv-set(w);
    val w@0 : hnd/evv<<local<h>,async,div,ndet|e>>
      = std/core/hnd/evv-swap-create0();
    val keep@0 : ()
      = std/core/hnd/evv-set(w@0);
    val w@1 : hnd/evv<<local<h>,async,div,ndet|e>>
      = std/core/hnd/evv-swap-create0();
    val x@1 : list<(int, error<a>)>
      = std/async/async/insert((match (@y-x11010) {
          ((@skip std/core/types/Tuple2((@pat@0@0: int), (@x@0: list<(int, error<a>)>)) : (int, list<(int, error<a>)>) ) as @pat@1: (int, list<(int, error<a>)>))
             -> @x@0;
        }), idx, res, std/core/types/@None);
    val keep@1 : ()
      = std/core/hnd/evv-set(w@1);
    std/core/types/local-set(cr, (std/core/types/Tuple2((std/core/int/int-sub((match (@y-x11009) {
            ((@skip std/core/types/Tuple2((@x: int), (@pat@0: list<(int, error<a>)>)) : (int, list<(int, error<a>)>) ) as @pat: (int, list<(int, error<a>)>))
               -> @x;
          }), 1)), x@1)));
  };
// monadic lift
fun @mlift-interleavedn@11428 : forall<h,a,e> (cr : local-var<h,(int, list<(int, error<a>)>)>, idx : int, res : error<a>, @y-x11009 : (int, list<(int, error<a>)>)) -> <local<h>,async,div,ndet|e> ()
  = forall<h,a,e> fn<<local<h>,async,div,ndet|e>>(cr: local-var<h,(int, list<(int, error<a>)>)>, idx: int, res: error<a>, @y-x11009: (int, list<(int, error<a>)>)){
    val x@12122 : (int, list<(int, error<a>)>)
          = std/core/types/local-get(cr, std/core/types/@Hnodiv);
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-extend((fn<<local<h>,async,div,ndet|e>>(@y-x11010: (int, list<(int, error<a>)>)){
          (std/async/async/@mlift-interleavedn@11427(@y-x11009, cr, idx, res, @y-x11010));
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> std/async/async/@mlift-interleavedn@11427(@y-x11009, cr, idx, res, x@12122);
    });
  };
// monadic lift
fun @mlift-interleavedn@11429 : forall<h,a,e> (@y-x11012 : (int, list<(int, error<a>)>)) -> <local<h>,async,div,ndet|e> bool
  = forall<h,a,e> fn<<local<h>,async,div,ndet|e>>(@y-x11012: (int, list<(int, error<a>)>)){
    val w : hnd/evv<<local<h>,async,div,ndet|e>>
      = std/core/hnd/evv-swap-create0();
    val keep : ()
      = std/core/hnd/evv-set(w);
    std/core/int/(>)((match (@y-x11012) {
        ((@skip std/core/types/Tuple2((@x@1: int), (@pat@0@1: list<(int, error<a>)>)) : (int, list<(int, error<a>)>) ) as @pat@2: (int, list<(int, error<a>)>))
           -> @x@1;
      }), 0);
  };
// monadic lift
fun @mlift-interleavedn@11430 : forall<h,a,e> (@y-x11013 : (int, list<(int, error<a>)>)) -> <local<h>,async,div,ndet|e> list<error<a>>
  = forall<h,a,e> fn<<local<h>,async,div,ndet|e>>(@y-x11013: (int, list<(int, error<a>)>)){
    val w : hnd/evv<<local<h>,async,div,ndet|e>>
      = std/core/hnd/evv-swap-create0();
    val keep : ()
      = std/core/hnd/evv-set(w);
    std/async/async/@lift-interleavedn@10762((match (@y-x11013) {
      ((@skip std/core/types/Tuple2((@pat@0@2: int), (@x@2: list<(int, error<a>)>)) : (int, list<(int, error<a>)>) ) as @pat@3: (int, list<(int, error<a>)>))
         -> @x@2;
    }));
  };
fun interleavedn : forall<a,e> (n : int, xs : list<() -> <async-exn|e> a>) -> <async|e> list<error<a>>
  = forall<a,e> fn<<async|e>>(n: int, xs: list<() -> <async-exn|e> a>){
    (forall<h> fn<<local<h>,async,div,ndet|e>>(){
      val loc : local-var<h,(int, list<(int, error<a>)>)>
        = std/core/types/local-new((std/core/types/Tuple2(n, std/core/types/Nil)));
      val res : list<error<a>>
        = std/async/async/strands/@handle((std/async/async/@Hnd-strands(1, (std/core/hnd/Clause2((fn<<local<h>,async,div,ndet|e>>(m: hnd/marker<<local<h>,async,div,ndet|e>,list<error<a>>>, ev: hnd/ev<strands<a>>, x1: int, x2: error<a>){
              (std/core/hnd/under2(ev, (fn<<local<h>,async,div,ndet|e>>(idx: int, res@0: error<a>){
                  val x@12131 : (int, list<(int, error<a>)>)
                        = (std/core/types/local-get(loc, std/core/types/@Hnodiv));
                  (match ((std/core/hnd/yielding())) {
                    ((std/core/types/True() : bool ) as @pat: bool)
                       -> std/core/hnd/yield-extend((fn<<local<h>,async,div,ndet|e>>(@y-x11009: (int, list<(int, error<a>)>)){
                        (std/async/async/@mlift-interleavedn@11428(loc, idx, res@0, @y-x11009));
                      }));
                    ((@skip std/core/types/False() : bool ) as @pat@0: bool)
                       -> std/async/async/@mlift-interleavedn@11428(loc, idx, res@0, x@12131);
                  });
                }), x1, x2));
            }))), (std/core/hnd/clause-tail0((fn<<local<h>,async,div,ndet|e>>(){
              val x@0@12133 : (int, list<(int, error<a>)>)
                    = (std/core/types/local-get(loc, std/core/types/@Hnodiv));
              (match ((std/core/hnd/yielding())) {
                ((std/core/types/True() : bool ) as @pat@1: bool)
                   -> std/core/hnd/yield-extend((fn<<local<h>,async,div,ndet|e>>(@y-x11012: (int, list<(int, error<a>)>)){
                    (std/async/async/@mlift-interleavedn@11429(@y-x11012));
                  }));
                ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
                   -> std/async/async/@mlift-interleavedn@11429(x@0@12133);
              });
            }))))), (fn<<local<h>,async,div,ndet|e>>(x@0@0: ()){
            val x@1@12135 : (int, list<(int, error<a>)>)
                  = (std/core/types/local-get(loc, std/core/types/@Hnodiv));
            (match ((std/core/hnd/yielding())) {
              ((std/core/types/True() : bool ) as @pat@2: bool)
                 -> std/core/hnd/yield-extend((fn<<local<h>,async,div,ndet|e>>(@y-x11013: (int, list<(int, error<a>)>)){
                  (std/async/async/@mlift-interleavedn@11430(@y-x11013));
                }));
              ((@skip std/core/types/False() : bool ) as @pat@0@1: bool)
                 -> std/async/async/@mlift-interleavedn@11430(x@1@12135);
            });
          }), (fn<<strands<a>,local<h>,async,div,ndet|e>>(){
            (std/async/async/interleaved-div(xs));
          }));
      std/core/hnd/prompt-local-var(loc, res);
    })();
  };
// monadic lift
fun list/@mlift-trmc-lift-interleavedx@10764@11431 : forall<a,e> (@acc : ctx<list<error<a>>>, @uniq-xx@10661 : list<() -> <async-exn|e> a>, @trmc-x10812 : error<a>) -> <async|e> list<error<a>>
  = forall<a,e> fn<<async|e>>(@acc: ctx<list<error<a>>>, @uniq-xx@10661: list<() -> <async-exn|e> a>, @trmc-x10812: error<a>){
    val @trmc-x10813 : list<error<a>>
      = std/core/types/@cctx-hole-create();
    val @trmc-x10814 : list<error<a>>
      = std/core/types/Cons(@trmc-x10812, @trmc-x10813);
    std/async/async/list/@trmc-lift-interleavedx@10764(@uniq-xx@10661, (std/core/types/@cctx-extend(@acc, @trmc-x10814, (std/core/types/@field-addr-of(@trmc-x10814, "(\x22std/core/types\x22,\x22\x22,\x22Cons\x22)", "(\x22\x22,\x22\x22,\x22tail\x22)")))));
  };
// monadic lift
fun list/@mlift-trmcm-lift-interleavedx@10764@11432 : forall<a,e> (@accm : (list<error<a>>) -> list<error<a>>, @uniq-xx@10661 : list<() -> <async-exn|e> a>, @trmc-x10817 : error<a>) -> <async|e> list<error<a>>
  = forall<a,e> fn<<async|e>>(@accm: (list<error<a>>) -> list<error<a>>, @uniq-xx@10661@0: list<() -> <async-exn|e> a>, @trmc-x10817: error<a>){
    std/async/async/list/@trmcm-lift-interleavedx@10764(@uniq-xx@10661@0, (fn(@trmc-x10816: list<error<a>>){
        (@accm((std/core/types/Cons(@trmc-x10817, @trmc-x10816))));
      }));
  };
// lifted local: list/@lift-interleavedx@10763, list/interleavedx, @spec-x10663
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10658, using:
// @uniq-f@10658 = (std/async/async/unsafe-try-all<a,<(std/async/async/async :: (E, V) -> V)|(e :: E)>>,Own)
fun list/@trmc-lift-interleavedx@10764 : forall<a,e> (@uniq-xs@10657 : list<() -> <async-exn|e> a>, @acc : ctx<list<error<a>>>) -> <async|e> list<error<a>>
  = forall<a,e> fn<<async|e>>(@uniq-xs@10657: list<() -> <async-exn|e> a>, @acc@0: ctx<list<error<a>>>){
    (match (@uniq-xs@10657) {
      ((std/core/types/Cons((@uniq-x@10660: () -> <(async-exn == 1 <async,exn>)|e> a), (@uniq-xx@10661@1: list<() -> <(async-exn == 1 <async,exn>)|e> a>)) : list<() -> <(async-exn == 1 <async,exn>)|e> a> ) as @uniq-pat@10659: (list<() -> <(async-exn == 1 <async,exn>)|e> a>))
         -> val x@12138 : error<a>
                  = std/async/async/unsafe-try-all(@uniq-x@10660);
        (match ((std/core/hnd/yielding())) {
          ((std/core/types/True() : bool ) as @pat: bool)
             -> std/core/hnd/yield-extend((fn<<async|e>>(@trmc-x10812@0: error<a>){
              (std/async/async/list/@mlift-trmc-lift-interleavedx@10764@11431(@acc@0, @uniq-xx@10661@1, @trmc-x10812@0));
            }));
          ((@skip std/core/types/False() : bool ) as @pat@0: bool)
             -> val @trmc-x10813@0 : list<error<a>>
                  = std/core/types/@cctx-hole-create();
                val @trmc-x10814@0 : list<error<a>>
                  = std/core/types/Cons(x@12138, @trmc-x10813@0);
            std/async/async/list/@trmc-lift-interleavedx@10764(@uniq-xx@10661@1, (std/core/types/@cctx-extend(@acc@0, @trmc-x10814@0, (std/core/types/@field-addr-of(@trmc-x10814@0, "(\x22std/core/types\x22,\x22\x22,\x22Cons\x22)", "(\x22\x22,\x22\x22,\x22tail\x22)")))));
        });
      ((@skip std/core/types/Nil() : list<() -> <(async-exn == 1 <async,exn>)|e> a> ) as @uniq-pat@0@10662: (list<() -> <(async-exn == 1 <async,exn>)|e> a>))
         -> std/core/types/cctx/((++.))(@acc@0, std/core/types/Nil);
    });
  };
// lifted local: list/@lift-interleavedx@10763, list/interleavedx, @spec-x10663
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10658, using:
// @uniq-f@10658 = (std/async/async/unsafe-try-all<a,<(std/async/async/async :: (E, V) -> V)|(e :: E)>>,Own)
fun list/@trmcm-lift-interleavedx@10764 : forall<a,e> (@uniq-xs@10657 : list<() -> <async-exn|e> a>, @accm : (list<error<a>>) -> list<error<a>>) -> <async|e> list<error<a>>
  = forall<a,e> fn<<async|e>>(@uniq-xs@10657@0: list<() -> <async-exn|e> a>, @accm@0: (list<error<a>>) -> list<error<a>>){
    (match (@uniq-xs@10657@0) {
      ((std/core/types/Cons((@uniq-x@10660@0: () -> <(async-exn == 1 <async,exn>)|e> a), (@uniq-xx@10661@2: list<() -> <(async-exn == 1 <async,exn>)|e> a>)) : list<() -> <(async-exn == 1 <async,exn>)|e> a> ) as @uniq-pat@10659@0: (list<() -> <(async-exn == 1 <async,exn>)|e> a>))
         -> val x@0@12141 : error<a>
                  = std/async/async/unsafe-try-all(@uniq-x@10660@0);
        (match ((std/core/hnd/yielding())) {
          ((std/core/types/True() : bool ) as @pat@1: bool)
             -> std/core/hnd/yield-extend((fn<<async|e>>(@trmc-x10817@0: error<a>){
              (std/async/async/list/@mlift-trmcm-lift-interleavedx@10764@11432(@accm@0, @uniq-xx@10661@2, @trmc-x10817@0));
            }));
          ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
             -> std/async/async/list/@trmcm-lift-interleavedx@10764(@uniq-xx@10661@2, (fn(@trmc-x10816@0: list<error<a>>){
                (@accm@0((std/core/types/Cons(x@0@12141, @trmc-x10816@0))));
              }));
        });
      ((@skip std/core/types/Nil() : list<() -> <(async-exn == 1 <async,exn>)|e> a> ) as @uniq-pat@0@10662@0: (list<() -> <(async-exn == 1 <async,exn>)|e> a>))
         -> @accm@0(std/core/types/Nil);
    });
  };
// lifted local: list/@lift-interleavedx@10763, list/interleavedx, @spec-x10663
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10658, using:
// @uniq-f@10658 = (std/async/async/unsafe-try-all<a,<(std/async/async/async :: (E, V) -> V)|(e :: E)>>,Own)
fun list/@lift-interleavedx@10764 : forall<a,e> (@uniq-xs@10657 : list<() -> <async-exn|e> a>) -> <async|e> list<error<a>>
  = forall<a,e> fn<<async|e>>(@uniq-xs@10657@1: list<() -> <async-exn|e> a>){
    (match ((std/core/hnd/@evv-is-affine())) {
      ((std/core/types/True() : bool ) as @pat@2: bool)
         -> std/async/async/list/@trmc-lift-interleavedx@10764(@uniq-xs@10657@1, (std/core/types/cctx/empty()));
      (@pat@0@1: bool)
         -> std/async/async/list/@trmcm-lift-interleavedx@10764(@uniq-xs@10657@1, (fn(@trmc-x10815: list<error<a>>){
            @trmc-x10815;
          }));
    });
  };
// lifted local: list/interleavedx, @spec-x10656
// specialized: std/core/list/map, on parameters @uniq-f@10653, using:
// @uniq-f@10653 = (std/async/async/unsafe-try-all<a,<(std/async/async/async :: (E, V) -> V)|(e :: E)>>,Own)
fun list/@lift-interleavedx@10763 : forall<a,e> (@uniq-xs@10652 : list<() -> <async-exn|e> a>) -> <async|e> list<error<a>>
  = forall<a,e> fn<<async|e>>(@uniq-xs@10652: list<() -> <async-exn|e> a>){
    (match (@uniq-xs@10652) {
      ((std/core/types/Nil() : list<() -> <(async-exn == 1 <async,exn>)|e> a> ) as @uniq-pat@0@10654: (list<() -> <(async-exn == 1 <async,exn>)|e> a>))
         -> std/core/types/Nil;
      (@uniq-pat@10655: (list<() -> <(async-exn == 1 <async,exn>)|e> a>))
         -> std/async/async/list/@lift-interleavedx@10764(@uniq-xs@10652);
    });
  };
// Interleave a list actions around their asynchronous operations and explicitly returning either
// either their result or their exception.
pub fun list/interleavedx : forall<a,e> (xs : list<() -> <async-exn|e> a>) -> <async|e> list<error<a>>
  = forall<a,e> fn<<async|e>>(xs: list<() -> <async-exn|e> a>){
    val w : hnd/evv<<async|e>>
      = std/core/hnd/evv-swap-create0();
    val x : int
      = (match (xs) {
        ((std/core/types/Nil() : list<() -> <(async-exn == 1 <async,exn>)|e> a> ) as @pat@1: (list<() -> <(async-exn == 1 <async,exn>)|e> a>))
           -> 0;
        (@pat: (list<() -> <(async-exn == 1 <async,exn>)|e> a>))
           -> std/core/list/@unroll-lift-length@5730@10000(xs, 0);
      });
    val keep : ()
      = std/core/hnd/evv-set(w);
    (match ((std/core/int/(==)(x, 0))) {
      ((std/core/types/True() : bool ) as @pat@0: bool)
         -> std/core/types/Nil;
      ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
         -> (match ((std/core/int/(==)(x, 1))) {
          ((std/core/types/True() : bool ) as @pat@1@0: bool)
             -> std/async/async/list/@lift-interleavedx@10763(xs);
          ((@skip std/core/types/False() : bool ) as @pat@2: bool)
             -> std/async/async/interleavedn(x, xs);
        });
    });
  };
// monadic lift
fun @mlift-trmc-lift-interleavedx@10766@11433 : forall<a,b,e> (@acc : ctx<list<error<either<a,b>>>>, @uniq-xx@10673 : list<() -> <async-exn|e> either<a,b>>, @trmc-x10818 : error<either<a,b>>) -> <async|e> list<error<either<a,b>>>
  = forall<a,b,e> fn<<async|e>>(@acc: ctx<list<error<either<a,b>>>>, @uniq-xx@10673: list<() -> <async-exn|e> either<a,b>>, @trmc-x10818: error<either<a,b>>){
    val @trmc-x10819 : list<error<either<a,b>>>
      = std/core/types/@cctx-hole-create();
    val @trmc-x10820 : list<error<either<a,b>>>
      = std/core/types/Cons(@trmc-x10818, @trmc-x10819);
    std/async/async/@trmc-lift-interleavedx@10766(@uniq-xx@10673, (std/core/types/@cctx-extend(@acc, @trmc-x10820, (std/core/types/@field-addr-of(@trmc-x10820, "(\x22std/core/types\x22,\x22\x22,\x22Cons\x22)", "(\x22\x22,\x22\x22,\x22tail\x22)")))));
  };
// monadic lift
fun @mlift-trmcm-lift-interleavedx@10766@11434 : forall<a,b,e> (@accm : (list<error<either<a,b>>>) -> list<error<either<a,b>>>, @uniq-xx@10673 : list<() -> <async-exn|e> either<a,b>>, @trmc-x10823 : error<either<a,b>>) -> <async|e> list<error<either<a,b>>>
  = forall<a,b,e> fn<<async|e>>(@accm: (list<error<either<a,b>>>) -> list<error<either<a,b>>>, @uniq-xx@10673@0: list<() -> <async-exn|e> either<a,b>>, @trmc-x10823: error<either<a,b>>){
    std/async/async/@trmcm-lift-interleavedx@10766(@uniq-xx@10673@0, (fn(@trmc-x10822: list<error<either<a,b>>>){
        (@accm((std/core/types/Cons(@trmc-x10823, @trmc-x10822))));
      }));
  };
// lifted local: @lift-interleavedx@10765, interleavedx, @spec-x10675
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10670, using:
// @uniq-f@10670 = (std/async/async/unsafe-try-all<(either :: (V, V) -> V)<a,b>,<(std/async/async/async :: (E, V) -> V)|(e :: E)>>,Own)
fun @trmc-lift-interleavedx@10766 : forall<a,b,e> (@uniq-xs@10669 : list<() -> <async-exn|e> either<a,b>>, @acc : ctx<list<error<either<a,b>>>>) -> <async|e> list<error<either<a,b>>>
  = forall<a,b,e> fn<<async|e>>(@uniq-xs@10669: list<() -> <async-exn|e> either<a,b>>, @acc@0: ctx<list<error<either<a,b>>>>){
    (match (@uniq-xs@10669) {
      ((std/core/types/Cons((@uniq-x@10672: () -> <(async-exn == 1 <async,exn>)|e> either<a,b>), (@uniq-xx@10673@1: list<() -> <(async-exn == 1 <async,exn>)|e> either<a,b>>)) : list<() -> <(async-exn == 1 <async,exn>)|e> either<a,b>> ) as @uniq-pat@10671: (list<() -> <(async-exn == 1 <async,exn>)|e> either<a,b>>))
         -> val x@12146 : error<either<a,b>>
                  = std/async/async/unsafe-try-all(@uniq-x@10672);
        (match ((std/core/hnd/yielding())) {
          ((std/core/types/True() : bool ) as @pat: bool)
             -> std/core/hnd/yield-extend((fn<<async|e>>(@trmc-x10818@0: error<either<a,b>>){
              (std/async/async/@mlift-trmc-lift-interleavedx@10766@11433(@acc@0, @uniq-xx@10673@1, @trmc-x10818@0));
            }));
          ((@skip std/core/types/False() : bool ) as @pat@0: bool)
             -> val @trmc-x10819@0 : list<error<either<a,b>>>
                  = std/core/types/@cctx-hole-create();
                val @trmc-x10820@0 : list<error<either<a,b>>>
                  = std/core/types/Cons(x@12146, @trmc-x10819@0);
            std/async/async/@trmc-lift-interleavedx@10766(@uniq-xx@10673@1, (std/core/types/@cctx-extend(@acc@0, @trmc-x10820@0, (std/core/types/@field-addr-of(@trmc-x10820@0, "(\x22std/core/types\x22,\x22\x22,\x22Cons\x22)", "(\x22\x22,\x22\x22,\x22tail\x22)")))));
        });
      ((@skip std/core/types/Nil() : list<() -> <(async-exn == 1 <async,exn>)|e> either<a,b>> ) as @uniq-pat@0@10674: (list<() -> <(async-exn == 1 <async,exn>)|e> either<a,b>>))
         -> std/core/types/cctx/((++.))(@acc@0, std/core/types/Nil);
    });
  };
// lifted local: @lift-interleavedx@10765, interleavedx, @spec-x10675
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10670, using:
// @uniq-f@10670 = (std/async/async/unsafe-try-all<(either :: (V, V) -> V)<a,b>,<(std/async/async/async :: (E, V) -> V)|(e :: E)>>,Own)
fun @trmcm-lift-interleavedx@10766 : forall<a,b,e> (@uniq-xs@10669 : list<() -> <async-exn|e> either<a,b>>, @accm : (list<error<either<a,b>>>) -> list<error<either<a,b>>>) -> <async|e> list<error<either<a,b>>>
  = forall<a,b,e> fn<<async|e>>(@uniq-xs@10669@0: list<() -> <async-exn|e> either<a,b>>, @accm@0: (list<error<either<a,b>>>) -> list<error<either<a,b>>>){
    (match (@uniq-xs@10669@0) {
      ((std/core/types/Cons((@uniq-x@10672@0: () -> <(async-exn == 1 <async,exn>)|e> either<a,b>), (@uniq-xx@10673@2: list<() -> <(async-exn == 1 <async,exn>)|e> either<a,b>>)) : list<() -> <(async-exn == 1 <async,exn>)|e> either<a,b>> ) as @uniq-pat@10671@0: (list<() -> <(async-exn == 1 <async,exn>)|e> either<a,b>>))
         -> val x@0@12149 : error<either<a,b>>
                  = std/async/async/unsafe-try-all(@uniq-x@10672@0);
        (match ((std/core/hnd/yielding())) {
          ((std/core/types/True() : bool ) as @pat@1: bool)
             -> std/core/hnd/yield-extend((fn<<async|e>>(@trmc-x10823@0: error<either<a,b>>){
              (std/async/async/@mlift-trmcm-lift-interleavedx@10766@11434(@accm@0, @uniq-xx@10673@2, @trmc-x10823@0));
            }));
          ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
             -> std/async/async/@trmcm-lift-interleavedx@10766(@uniq-xx@10673@2, (fn(@trmc-x10822@0: list<error<either<a,b>>>){
                (@accm@0((std/core/types/Cons(x@0@12149, @trmc-x10822@0))));
              }));
        });
      ((@skip std/core/types/Nil() : list<() -> <(async-exn == 1 <async,exn>)|e> either<a,b>> ) as @uniq-pat@0@10674@0: (list<() -> <(async-exn == 1 <async,exn>)|e> either<a,b>>))
         -> @accm@0(std/core/types/Nil);
    });
  };
// lifted local: @lift-interleavedx@10765, interleavedx, @spec-x10675
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10670, using:
// @uniq-f@10670 = (std/async/async/unsafe-try-all<(either :: (V, V) -> V)<a,b>,<(std/async/async/async :: (E, V) -> V)|(e :: E)>>,Own)
fun @lift-interleavedx@10766 : forall<a,b,e> (@uniq-xs@10669 : list<() -> <async-exn|e> either<a,b>>) -> <async|e> list<error<either<a,b>>>
  = forall<a,b,e> fn<<async|e>>(@uniq-xs@10669@1: list<() -> <async-exn|e> either<a,b>>){
    (match ((std/core/hnd/@evv-is-affine())) {
      ((std/core/types/True() : bool ) as @pat@2: bool)
         -> std/async/async/@trmc-lift-interleavedx@10766(@uniq-xs@10669@1, (std/core/types/cctx/empty()));
      (@pat@0@1: bool)
         -> std/async/async/@trmcm-lift-interleavedx@10766(@uniq-xs@10669@1, (fn(@trmc-x10821: list<error<either<a,b>>>){
            @trmc-x10821;
          }));
    });
  };
// lifted local: interleavedx, @spec-x10668
// specialized: std/core/list/map, on parameters @uniq-f@10665, using:
// @uniq-f@10665 = (std/async/async/unsafe-try-all<(either :: (V, V) -> V)<a,b>,<(std/async/async/async :: (E, V) -> V)|(e :: E)>>,Own)
fun @lift-interleavedx@10765 : forall<a,b,e> (@uniq-xs@10664 : list<() -> <async-exn|e> either<a,b>>) -> <async|e> list<error<either<a,b>>>
  = forall<a,b,e> fn<<async|e>>(@uniq-xs@10664: list<() -> <async-exn|e> either<a,b>>){
    (match (@uniq-xs@10664) {
      ((std/core/types/Nil() : list<() -> <(async-exn == 1 <async,exn>)|e> either<a,b>> ) as @uniq-pat@0@10666: (list<() -> <(async-exn == 1 <async,exn>)|e> either<a,b>>))
         -> std/core/types/Nil;
      (@uniq-pat@10667: (list<() -> <(async-exn == 1 <async,exn>)|e> either<a,b>>))
         -> std/async/async/@lift-interleavedx@10766(@uniq-xs@10664);
    });
  };
// monadic lift
fun @mlift-interleavedx@11435 : forall<a,b,e> (@y-x11048 : a) -> <async-exn|e> either<a,b>
  = forall<a,b,e> fn<<async-exn|e>>(@y-x11048: a){
    std/core/types/Left(@y-x11048);
  };
// monadic lift
fun @mlift-interleavedx@11436 : forall<a,b,e> (@y-x11049 : b) -> <async-exn|e> either<a,b>
  = forall<a,b,e> fn<<async-exn|e>>(@y-x11049: b){
    std/core/types/Right(@y-x11049);
  };
// monadic lift
fun @mlift-interleavedx@11437 : forall<a,b,e> (@c-x11054 : list<error<either<a,b>>>) -> (error<a>, error<b>)
  = forall<a,b,e> fn(@c-x11054: list<error<either<a,b>>>){
    (match (@c-x11054) {
      ((std/core/types/Cons((x: error<either<a,b>>), ((std/core/types/Cons((y: error<either<a,b>>), (@pat@1@1: list<error<either<a,b>>>)) : list<error<either<a,b>>> ) as @pat@0@1: list<error<either<a,b>>>)) : list<error<either<a,b>>> ) as @pat@3: (list<error<either<a,b>>>))
         -> val w : hnd/evv<<async|e>>
              = std/core/hnd/evv-swap-create0();
            val x@0 : error<a>
              = std/async/async/unleft(x);
            val keep : ()
              = std/core/hnd/evv-set(w);
            val w@0 : hnd/evv<<async|e>>
              = std/core/hnd/evv-swap-create0();
            val x@1 : error<b>
              = std/async/async/unright(y);
            val keep@0 : ()
              = std/core/hnd/evv-set(w@0);
        std/core/types/Tuple2(x@0, x@1);
      (@pat@2@0: (list<error<either<a,b>>>))
         -> val exn : exception
                  = std/core/exn/Exception("invalid interleaved result", (std/core/exn/ExnInternal("std/async/interleavedx(action1,action2)")));
        std/core/types/Tuple2((std/core/exn/Error(exn)), (std/core/exn/Error(exn)));
    });
  };
// Interleave two actions around their asynchronous operations and explicitly returning either
// their result or their exception.
pub fun interleavedx : forall<a,b,e> (action1 : () -> <async-exn|e> a, action2 : () -> <async-exn|e> b) -> <async|e> (error<a>, error<b>)
  = forall<a,b,e> fn<<async|e>>(action1: () -> <async-exn|e> a, action2: () -> <async-exn|e> b){
    val xs@10142 : list<() -> <async-exn|e> either<a,b>>
      = std/core/types/Cons((fn<<async,exn|e>>(){
          val x@12156 : a
                = (action1());
          (match ((std/core/hnd/yielding())) {
            ((std/core/types/True() : bool ) as @pat: bool)
               -> std/core/hnd/yield-extend((fn<<(async-exn == 1 <async,exn>)|e>>(@y-x11048: a){
                (std/core/types/Left(@y-x11048));
              }));
            ((@skip std/core/types/False() : bool ) as @pat@0: bool)
               -> std/core/types/Left(x@12156);
          });
        }), (std/core/types/Cons((fn<<async,exn|e>>(){
            val x@0@12159 : b
                  = (action2());
            (match ((std/core/hnd/yielding())) {
              ((std/core/types/True() : bool ) as @pat@1: bool)
                 -> std/core/hnd/yield-extend((fn<<(async-exn == 1 <async,exn>)|e>>(@y-x11049: b){
                  (std/core/types/Right(@y-x11049));
                }));
              ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
                 -> std/core/types/Right(x@0@12159);
            });
          }), std/core/types/Nil)));
    val w : hnd/evv<<async|e>>
      = std/core/hnd/evv-swap-create0();
    val x@1 : int
      = (match (xs@10142) {
        ((std/core/types/Nil() : list<() -> <(async-exn == 1 <async,exn>)|e> either<a,b>> ) as @pat@1@0: (list<() -> <(async-exn == 1 <async,exn>)|e> either<a,b>>))
           -> 0;
        (@pat@2: (list<() -> <(async-exn == 1 <async,exn>)|e> either<a,b>>))
           -> std/core/list/@unroll-lift-length@5730@10000(xs@10142, 0);
      });
    val keep : ()
      = std/core/hnd/evv-set(w);
    val x@2@12164 : list<error<either<a,b>>>
      = (match ((std/core/int/(==)(x@1, 0))) {
        ((std/core/types/True() : bool ) as @pat@0@2: bool)
           -> std/core/types/Nil;
        ((@skip std/core/types/False() : bool ) as @pat@0@0@0: bool)
           -> (match ((std/core/int/(==)(x@1, 1))) {
            ((std/core/types/True() : bool ) as @pat@1@0@0: bool)
               -> std/async/async/@lift-interleavedx@10765(xs@10142);
            ((@skip std/core/types/False() : bool ) as @pat@2@0: bool)
               -> std/async/async/interleavedn(x@1, xs@10142);
          });
      });
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat@3: bool)
         -> std/core/hnd/yield-extend((fn(@c-x11054: list<error<either<a,b>>>){
          (std/async/async/@mlift-interleavedx@11437(@c-x11054));
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0@1: bool)
         -> (match (x@2@12164) {
          ((std/core/types/Cons((x@3: error<either<a,b>>), ((std/core/types/Cons((y: error<either<a,b>>), (@pat@1@1: list<error<either<a,b>>>)) : list<error<either<a,b>>> ) as @pat@0@1@0: list<error<either<a,b>>>)) : list<error<either<a,b>>> ) as @pat@3@0: (list<error<either<a,b>>>))
             -> val w@0 : hnd/evv<<async|e>>
                  = std/core/hnd/evv-swap-create0();
                val x@4 : error<a>
                  = std/async/async/unleft(x@3);
                val keep@0 : ()
                  = std/core/hnd/evv-set(w@0);
                val w@1 : hnd/evv<<async|e>>
                  = std/core/hnd/evv-swap-create0();
                val x@5 : error<b>
                  = std/async/async/unright(y);
                val keep@1 : ()
                  = std/core/hnd/evv-set(w@1);
            std/core/types/Tuple2(x@4, x@5);
          (@pat@2@0@0: (list<error<either<a,b>>>))
             -> val exn : exception
                      = std/core/exn/Exception("invalid interleaved result", (std/core/exn/ExnInternal("std/async/interleavedx(action1,action2)")));
            std/core/types/Tuple2((std/core/exn/Error(exn)), (std/core/exn/Error(exn)));
        });
    });
  };
// Automatically generated. Tests for the `Cancel` constructor of the `:exception-info` type.
fip fun is-cancel : (^ exception-info : exception-info) -> bool
  = fn(exception-info: exception-info){
    match (exception-info) {
      ((std/async/async/Cancel() : exception-info ) as @pat: exception-info)
         -> std/core/types/True;
      (@pat@0: exception-info)
         -> std/core/types/False;
    };
  };
// Was this a cancelation exception?
fun exn/is-cancel : (exn : exception) -> bool
  = fn(exn: exception){
    match (exn) {
      ((@skip std/core/exn/Exception((@pat@0: string), (@x: exception-info)) : exception ) as @pat: exception)
         -> (match (@x) {
          ((std/async/async/Cancel() : exception-info ) as @pat@1: exception-info)
             -> std/core/types/True;
          (@pat@0@0: exception-info)
             -> std/core/types/False;
        });
    };
  };
fun error/is-cancel : forall<a> (t : error<a>) -> bool
  = forall<a> fn(t: error<a>){
    (match (t) {
      ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0: string), (@pat@1: exception-info)) : exception ) as exn: exception)) : error<a> ) as @pat: (error<a>))
         -> (match (exn) {
          ((@skip std/core/exn/Exception((@pat@0@0: string), (@x: exception-info)) : exception ) as @pat@2: exception)
             -> (match (@x) {
              ((std/async/async/Cancel() : exception-info ) as @pat@3: exception-info)
                 -> std/core/types/True;
              (@pat@0@1: exception-info)
                 -> std/core/types/False;
            });
        });
      (@pat@2@0: (error<a>))
         -> std/core/types/False;
    });
  };
// monadic lift
fun @mlift-firstof@11438 : forall<a,e> (x : a, wild_ : ()) -> <async,exn,exn|e> a
  = forall<a,e> fn<<async,exn,exn|e>>(x: a, wild_: ()){
    x;
  };
// monadic lift
fun @mlift-firstof@11439 : forall<a,e> (x : a) -> <exn,exn,async|e> a
  = forall<a,e> fn<<exn,exn,async|e>>(x: a){
    val i@12173 : hnd/ev-index
      = std/core/hnd/@evv-index(std/async/async/async/@tag);
    val w : hnd/evv<<async,exn,exn|e>>
      = std/core/hnd/evv-swap-create1(i@12173);
    val ev@12175 : hnd/ev<async>
      = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
    val y : ()
      = (match (ev@12175) {
        ((@skip std/core/hnd/Ev<e1,b>((@pat@0@1: hnd/htag<async>), (m: hnd/marker<e1,b>), (h: async<e1,b>), (@pat@1@0: hnd/evv<e1>)) : hnd/ev<async> ) as @pat@2: (hnd/ev<async>))
           -> (match (h) {
            ((@skip std/async/async/@Hnd-async((@pat@0: int), (@pat@1: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e1,b>), (@ctl-cancel: hnd/clause1<scope,(),async,e1,b>), (@pat@2@0: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>
   )>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e1,b>), (@pat@3: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async
   ,e1,b>))) : async<e1,b> ) as @pat: (async<e1,b>))
               -> (match (@ctl-cancel) {
                ((@skip std/core/hnd/Clause1((f@0: (hnd/marker<e1,b>, hnd/ev<async>, scope) -> e1 ())) : hnd/clause1<scope,(),async,e1,b> ) as @pat@2@0@0: (hnd/clause1<scope,(),async,e1,b>))
                   -> f@0(m, ev@12175, std/async/async/empty-scope);
              });
          });
      });
    val _ : ()
      = std/core/hnd/evv-set(w);
    val x@0@12171 : ()
      = (match ((std/core/hnd/yielding())) {
        ((std/core/types/True() : bool ) as @pat@1@1: bool)
           -> std/core/hnd/yield-cont((forall<b> fn<<async,exn,exn|e>>(cont: (b) -> <async,exn,exn|e> (), res: b){
            std/core/hnd/open-at1(i@12173, cont, res);
          }));
        ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
           -> y;
      });
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat@4: bool)
         -> std/core/hnd/yield-extend((fn<<async,exn,exn|e>>(wild_: ()){
          x;
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0@2: bool)
         -> x;
    });
  };
// monadic lift
fun @mlift-firstof@11440 : forall<a,e> (a : () -> <async-exn|e> a, @y-x11056 : hnd/ev-index) -> <exn,exn,async|e> a
  = forall<a,e> fn<<exn,exn,async|e>>(a: () -> <async-exn|e> a, @y-x11056: hnd/ev-index){
    val w0 : hnd/evv<hnd/_e2>
      = std/core/hnd/evv-swap-delete(@y-x11056, std/core/types/True);
    val x@0 : a
      = a();
    val _ : ()
      = std/core/hnd/evv-set(w0);
    val x@12180 : a
      = (match ((std/core/hnd/yielding())) {
        ((std/core/types/True() : bool ) as @pat@1: bool)
           -> std/core/hnd/yield-cont((forall<b> fn<<exn,exn,async|e>>(cont: (b) -> <exn,exn,async|e> a, res: b){
            std/core/hnd/mask-at1(@y-x11056, std/core/types/True, cont, res);
          }));
        ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
           -> x@0;
      });
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-extend((fn<<exn,exn,async|e>>(x@1: a){
          (std/async/async/@mlift-firstof@11439(x@1));
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> std/async/async/@mlift-firstof@11439(x@12180);
    });
  };
// monadic lift
fun @mlift-firstof@11441 : forall<a,e> (x@0 : a, wild_@0 : ()) -> <async,exn,exn|e> a
  = forall<a,e> fn<<async,exn,exn|e>>(x@0: a, wild_@0: ()){
    x@0;
  };
// monadic lift
fun @mlift-firstof@11442 : forall<a,e> (x@0 : a) -> <exn,exn,async|e> a
  = forall<a,e> fn<<exn,exn,async|e>>(x@0: a){
    val i@12187 : hnd/ev-index
      = std/core/hnd/@evv-index(std/async/async/async/@tag);
    val w : hnd/evv<<async,exn,exn|e>>
      = std/core/hnd/evv-swap-create1(i@12187);
    val ev@12189 : hnd/ev<async>
      = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
    val y : ()
      = (match (ev@12189) {
        ((@skip std/core/hnd/Ev<e1,b>((@pat@0@1: hnd/htag<async>), (m: hnd/marker<e1,b>), (h: async<e1,b>), (@pat@1@0: hnd/evv<e1>)) : hnd/ev<async> ) as @pat@2: (hnd/ev<async>))
           -> (match (h) {
            ((@skip std/async/async/@Hnd-async((@pat@0: int), (@pat@1: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e1,b>), (@ctl-cancel: hnd/clause1<scope,(),async,e1,b>), (@pat@2@0: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>
   )>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e1,b>), (@pat@3: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async
   ,e1,b>))) : async<e1,b> ) as @pat: (async<e1,b>))
               -> (match (@ctl-cancel) {
                ((@skip std/core/hnd/Clause1((f@0: (hnd/marker<e1,b>, hnd/ev<async>, scope) -> e1 ())) : hnd/clause1<scope,(),async,e1,b> ) as @pat@2@0@0: (hnd/clause1<scope,(),async,e1,b>))
                   -> f@0(m, ev@12189, std/async/async/empty-scope);
              });
          });
      });
    val _ : ()
      = std/core/hnd/evv-set(w);
    val x@12185 : ()
      = (match ((std/core/hnd/yielding())) {
        ((std/core/types/True() : bool ) as @pat@1@1: bool)
           -> std/core/hnd/yield-cont((forall<b> fn<<async,exn,exn|e>>(cont: (b) -> <async,exn,exn|e> (), res: b){
            std/core/hnd/open-at1(i@12187, cont, res);
          }));
        ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
           -> y;
      });
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat@4: bool)
         -> std/core/hnd/yield-extend((fn<<async,exn,exn|e>>(wild_@0: ()){
          x@0;
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0@2: bool)
         -> x@0;
    });
  };
// monadic lift
fun @mlift-firstof@11443 : forall<a,e> (b : () -> <async-exn|e> a, @y-x11060 : hnd/ev-index) -> <exn,exn,async|e> a
  = forall<a,e> fn<<exn,exn,async|e>>(b: () -> <async-exn|e> a, @y-x11060: hnd/ev-index){
    val w0 : hnd/evv<hnd/_e2>
      = std/core/hnd/evv-swap-delete(@y-x11060, std/core/types/True);
    val x@0 : a
      = b();
    val _ : ()
      = std/core/hnd/evv-set(w0);
    val x@12194 : a
      = (match ((std/core/hnd/yielding())) {
        ((std/core/types/True() : bool ) as @pat@1: bool)
           -> std/core/hnd/yield-cont((forall<b> fn<<exn,exn,async|e>>(cont: (b) -> <exn,exn,async|e> a, res: b){
            std/core/hnd/mask-at1(@y-x11060, std/core/types/True, cont, res);
          }));
        ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
           -> x@0;
      });
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-extend((fn<<exn,exn,async|e>>(x@0@0: a){
          (std/async/async/@mlift-firstof@11442(x@0@0));
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> std/async/async/@mlift-firstof@11442(x@12194);
    });
  };
// monadic lift
fun @mlift-firstof@11444 : forall<a,e> (@y-x11064 : (error<a>, error<a>)) -> <async,exn|e> a
  = forall<a,e> fn<<async,exn|e>>(@y-x11064: (error<a>, error<a>)){
    (match (@y-x11064) {
      ((@skip std/core/types/Tuple2((ra: error<a>), (rb: error<a>)) : (error<a>, error<a>) ) as @pat: (error<a>, error<a>))
         -> (match (ra) {
          ((std/core/exn/Error((exn: exception)) : error<a> ) as @pat@0: (error<a>))
             | (match (exn) {
              ((@skip std/core/exn/Exception((@pat@0@0: string), (@x: exception-info)) : exception ) as @pat@1: exception)
                 -> (match (@x) {
                  ((std/async/async/Cancel() : exception-info ) as @pat@2: exception-info)
                     -> std/core/types/True;
                  (@pat@0@1: exception-info)
                     -> std/core/types/False;
                });
            }) -> val i@12199 : (hnd/ev-index == 1 ssize_t)
                    = std/core/hnd/@evv-index(std/core/exn/exn/@tag);
                  val w : hnd/evv<<exn,async|e>>
                    = std/core/hnd/evv-swap-create1(i@12199);
                  val y : a
                    = std/core/exn/untry(rb);
                  val _ : ()
                    = std/core/hnd/evv-set(w);
            (match ((std/core/hnd/yielding())) {
              ((std/core/types/True() : bool ) as @pat@3: bool)
                 -> std/core/hnd/yield-cont((forall<b> fn<<exn,async|e>>(cont: (b) -> <exn,async|e> a, res: b){
                  std/core/hnd/open-at1(i@12199, cont, res);
                }));
              ((@skip std/core/types/False() : bool ) as @pat@0@2: bool)
                 -> y;
            });
          (@pat@1@0: (error<a>))
             -> val i@0@12202 : (hnd/ev-index == 1 ssize_t)
                  = std/core/hnd/@evv-index(std/core/exn/exn/@tag);
                val w@0 : hnd/evv<<exn,async|e>>
                  = std/core/hnd/evv-swap-create1(i@0@12202);
                val y@0 : a
                  = std/core/exn/untry(ra);
                val _ : ()
                  = std/core/hnd/evv-set(w@0);
            (match ((std/core/hnd/yielding())) {
              ((std/core/types/True() : bool ) as @pat@4: bool)
                 -> std/core/hnd/yield-cont((forall<b> fn<<exn,async|e>>(cont@0: (b) -> <exn,async|e> a, res@0: b){
                  std/core/hnd/open-at1(i@0@12202, cont@0, res@0);
                }));
              ((@skip std/core/types/False() : bool ) as @pat@0@3: bool)
                 -> y@0;
            });
        });
    });
  };
// Execute `a` and `b` interleaved. As soon as one of them finishes,
// `cancel` the other one and return the result of the first.
pub fun firstof : forall<a,e> (a : () -> <async-exn|e> a, b : () -> <async-exn|e> a) -> <async-exn|e> a
  = forall<a,e> fn<<async-exn|e>>(a: () -> <async-exn|e> a, b: () -> <async-exn|e> a){
    std/async/async/cancelable((fn<<async,exn|e>>(){
      val x@12205 : (error<a>, error<a>)
            = (std/async/async/interleavedx((fn<<async-exn,exn|e>>(){
                val x@0@12207 : hnd/ev-index
                      = (std/core/hnd/@evv-index(std/core/exn/exn/@tag));
                (match ((std/core/hnd/yielding())) {
                  ((std/core/types/True() : bool ) as @pat@1: bool)
                     -> std/core/hnd/yield-extend((fn<<exn,exn,async|e>>(@y-x11056: (hnd/ev-index == 1 ssize_t)){
                      (std/async/async/@mlift-firstof@11440(a, @y-x11056));
                    }));
                  ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
                     -> std/async/async/@mlift-firstof@11440(a, x@0@12207);
                });
              }), (fn<<async-exn,exn|e>>(){
                val x@1@12209 : hnd/ev-index
                      = (std/core/hnd/@evv-index(std/core/exn/exn/@tag));
                (match ((std/core/hnd/yielding())) {
                  ((std/core/types/True() : bool ) as @pat@2: bool)
                     -> std/core/hnd/yield-extend((fn<<exn,exn,async|e>>(@y-x11060: (hnd/ev-index == 1 ssize_t)){
                      (std/async/async/@mlift-firstof@11443(b, @y-x11060));
                    }));
                  ((@skip std/core/types/False() : bool ) as @pat@0@1: bool)
                     -> std/async/async/@mlift-firstof@11443(b, x@1@12209);
                });
              })));
      (match ((std/core/hnd/yielding())) {
        ((std/core/types/True() : bool ) as @pat: bool)
           -> std/core/hnd/yield-extend((fn<<async,exn|e>>(@y-x11064: (error<a>, error<a>)){
            (std/async/async/@mlift-firstof@11444(@y-x11064));
          }));
        ((@skip std/core/types/False() : bool ) as @pat@0: bool)
           -> std/async/async/@mlift-firstof@11444(x@12205);
      });
    }));
  };
fun async/set-timeout : (cb : unit-cb, ms : int32, ?set-timeout : (unit-cb, int32) -> <st<global>,console/console,div,fsys,ndet,net,ui> any) -> <st<global>,console/console,div,fsys,ndet,net,ui> timeout-id
  = fn<io-noexn>(cb: unit-cb, ms: int32, @implicit/set-timeout: (unit-cb, int32) -> io-noexn any){
    std/async/async/Timeout-id((?set-timeout(cb, (match ((std/num/int32/(>=)(ms, std/num/int32/zero))) {
        ((std/core/types/True() : bool ) as @pat: bool)
           -> ms;
        ((@skip std/core/types/False() : bool ) as @pat@0: bool)
           -> std/num/int32/zero;
      }))));
  };
// monadic lift
fun @mlift-yield@11445 : (@y-x11072 : maybe<() -> io-noexn ()>) -> io error<maybe<() -> io-noexn ()>>
  = fn<io>(@y-x11072: maybe<() -> io-noexn ()>){
    std/core/exn/Ok(@y-x11072);
  };
// monadic lift
fun @mlift-yield@11446 : (@y-x11074 : error<()>) -> <async,exn,ndet> ()
  = fn<<async,exn,ndet>>(@y-x11074: error<()>){
    val i@12211 : hnd/ev-index
      = std/core/types/@make-ssize_t(1);
    val w : hnd/evv<<exn,async,ndet>>
      = std/core/hnd/evv-swap-create1(i@12211);
    val y : ()
      = match (@y-x11074) {
        ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@0: string), (@pat@1@0: exception-info)) : exception ) as exn@0: exception)) : error<()> ) as @pat@1: (error<()>))
           -> val ev@12214 : hnd/ev<exn>
                    = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
          (match (ev@12214) {
            ((@skip std/core/hnd/Ev<e,a>((@pat@0@1: hnd/htag<exn>), (m: hnd/marker<e,a>), (h: exn<e,a>), (@pat@1@1: hnd/evv<e>)) : hnd/ev<exn> ) as @pat@2: (hnd/ev<exn>))
               -> (match ((std/core/exn/throw-exn/@select(h))) {
                ((@skip std/core/hnd/Clause1((f@0: (hnd/marker<e,a>, hnd/ev<exn>, exception) -> e ())) : hnd/clause1<exception,(),exn,e,a> ) as @pat@2@0: (hnd/clause1<exception,(),exn,e,a>))
                   -> f@0(m, ev@12214, exn@0);
              });
          });
        ((@skip std/core/exn/Ok((x@1: ())) : error<()> ) as @pat@2@1: (error<()>))
           -> x@1;
      };
    val _ : ()
      = std/core/hnd/evv-set(w);
    match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-cont((forall<a> fn<<exn,async,ndet>>(cont: (a) -> <exn,async,ndet> (), res: a){
          std/core/hnd/open-at1(i@12211, cont, res);
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> y;
    };
  };
// Yield to other asynchronous operations. Same as `wait(0)`.
pub fun yield : (?set-timeout : (unit-cb, int32) -> <st<global>,console/console,div,fsys,ndet,net,ui> any) -> <async,exn,ndet> ()
  = fn<asyncx>(@implicit/set-timeout: (unit-cb, int32) -> io-noexn any){
    val i@12220 : hnd/ev-index
      = std/core/types/@make-ssize_t(0);
    val w : hnd/evv<<async,exn,ndet>>
      = std/core/hnd/evv-swap-create1(i@12220);
    val ev@12223 : hnd/ev<async>
      = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
    val y : error<()>
      = match (ev@12223) {
        ((@skip std/core/hnd/Ev<e,a>((@pat@0@1: hnd/htag<async>), (m: hnd/marker<e,a>), (h: async<e,a>), (@pat@1@0: hnd/evv<e>)) : hnd/ev<async> ) as @pat@2: (hnd/ev<async>))
           -> (match (h) {
            ((@skip std/async/async/@Hnd-async((@pat@0: int), (@pat@1: forall<b> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) b,b,async,e,a>), (@pat@2@0: hnd/clause1<scope,(),async,e,a>), (@ctl-do-await: forall<b> hnd/clause1<((await-setup<b> == 4 (cb : (error<b>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>
   )>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<b>,async,e,a>), (@pat@3: (forall<b> hnd/clause1<((await-setup<b> == 4 (cb : (error<b>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<b>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async
   ,e,a>))) : async<e,a> ) as @pat: (async<e,a>))
               -> (match (@ctl-do-await) {
                ((@skip std/core/hnd/Clause1((f@0: (hnd/marker<e,a>, hnd/ev<async>, ((await-setup<()> == 4 (cb : (error<()>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <
   read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool)) -> e error<()>)) : hnd/clause1<((await-setup<()> == 4 (cb : (error<()>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<
   global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<()>,async,e,a> ) as @pat@2@0@0: (hnd/clause1<((await-setup<()> == 4 (cb : (error<()>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet
   ,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<()>,async,e,a>))
                   -> f@0(m, ev@12223, (std/core/types/Tuple3((fn<(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>(cb: (error<()>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()){
                        (match ((std/core/exn/exn/@handle((std/core/exn/@Hnd-exn(0, (forall<b> std/core/hnd/Clause1((fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(m@0: hnd/marker<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>,error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>>, @_wildcard-x653_16: hnd/ev<exn>, x@1: exception){
                              (std/core/hnd/yield-to-final(m@0, (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@_wildcard-x653_45: (hnd/resume-result<b,error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>>) -> <alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>> error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,
   fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>){
                                  (std/core/exn/Error(x@1));
                                })));
                            }))))), (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@res: error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>){
                            @res;
                          }), (fn<<exn,alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(){
                            val w@0 : (hnd/evv<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>,exn>>)
                              = (std/core/hnd/evv-swap-create0());
                            val x@3 : timeout-id
                              = (std/async/async/Timeout-id((?set-timeout((fn<(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>(){
                                  (cb((std/core/exn/Ok(std/core/types/Unit)), std/core/types/True));
                                }), (match ((std/num/int32/(>=)(std/num/int32/zero, std/num/int32/zero))) {
                                  ((std/core/types/True() : bool ) as @pat@4: bool)
                                     -> std/num/int32/zero;
                                  ((@skip std/core/types/False() : bool ) as @pat@0@1@0: bool)
                                     -> std/num/int32/zero;
                                })))));
                            val keep : ()
                              = (std/core/hnd/evv-set(w@0));
                            (match ((std/core/hnd/yielding())) {
                              ((std/core/types/True() : bool ) as @pat@3@0: bool)
                                 -> std/core/hnd/yield-extend(std/async/async/@mlift-yield@11445);
                              ((@skip std/core/types/False() : bool ) as @pat@0@2: bool)
                                 -> std/core/exn/Ok(std/core/types/Nothing);
                            });
                          })))) {
                          ((std/core/exn/Ok((mcleanup: maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)) : error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>> ) as @pat@3@0@0: (error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<
   global>,alloc<global>>)>)>) ()>>))
                             -> mcleanup;
                          ((@skip std/core/exn/Error(((@skip std/core/exn/Exception((@pat@1@0@0: string), (@pat@2@0@0@0: exception-info)) : exception ) as exn: exception)) : error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>> ) as @pat@0@0@0: (error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>))
                             -> val _ : ()
                                      = cb((std/core/exn/Error(exn)), std/core/types/True);
                            std/core/types/Nothing;
                        });
                      }), std/async/async/empty-scope, std/core/types/True)));
              });
          });
      };
    val _ : ()
      = std/core/hnd/evv-set(w);
    val x@12217 : error<()>
      = match ((std/core/hnd/yielding())) {
        ((std/core/types/True() : bool ) as @pat@1@1: bool)
           -> std/core/hnd/yield-cont((forall<a> fn<<async,exn,ndet>>(cont: (a) -> <async,exn,ndet> error<()>, res: a){
            std/core/hnd/open-at1(i@12220, cont, res);
          }));
        ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
           -> y;
      };
    match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat@5: bool)
         -> std/core/hnd/yield-extend(std/async/async/@mlift-yield@11446);
      ((@skip std/core/types/False() : bool ) as @pat@0@3: bool)
         -> val i@0@12235 : (hnd/ev-index == 1 ssize_t)
              = std/core/types/@make-ssize_t(1);
            val w@1 : hnd/evv<<exn,async,ndet>>
              = std/core/hnd/evv-swap-create1(i@0@12235);
            val y@0 : ()
              = (match (x@12217) {
                ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@4: string), (@pat@1@1@0: exception-info)) : exception ) as exn@0: exception)) : error<()> ) as @pat@6: (error<()>))
                   -> val ev@0@12238 : hnd/ev<exn>
                            = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
                  (match (ev@0@12238) {
                    ((@skip std/core/hnd/Ev<e,a>((@pat@0@5: hnd/htag<exn>), (m@1: hnd/marker<e,a>), (h@0: exn<e,a>), (@pat@1@2: hnd/evv<e>)) : hnd/ev<exn> ) as @pat@7: (hnd/ev<exn>))
                       -> (match ((std/core/exn/throw-exn/@select(h@0))) {
                        ((@skip std/core/hnd/Clause1((f@3: (hnd/marker<e,a>, hnd/ev<exn>, exception) -> e ())) : hnd/clause1<exception,(),exn,e,a> ) as @pat@2@1: (hnd/clause1<exception,(),exn,e,a>))
                           -> f@3(m@1, ev@0@12238, exn@0);
                      });
                  });
                ((@skip std/core/exn/Ok((x@6: ())) : error<()> ) as @pat@2@2: (error<()>))
                   -> x@6;
              });
            val _ : ()
              = std/core/hnd/evv-set(w@1);
        (match ((std/core/hnd/yielding())) {
          ((std/core/types/True() : bool ) as @pat@5@0: bool)
             -> std/core/hnd/yield-cont((forall<a> fn<<exn,async,ndet>>(cont@0: (a) -> <exn,async,ndet> (), res@1: a){
              std/core/hnd/open-at1(i@0@12235, cont@0, res@1);
            }));
          ((@skip std/core/types/False() : bool ) as @pat@0@3@0: bool)
             -> y@0;
        });
    };
  };
// monadic lift
fun duration/@mlift-wait@11447 : (@y-x11079 : maybe<() -> io-noexn ()>) -> io error<maybe<() -> io-noexn ()>>
  = fn<io>(@y-x11079: maybe<() -> io-noexn ()>){
    std/core/exn/Ok(@y-x11079);
  };
// monadic lift
fun duration/@mlift-wait@11448 : (@y-x11081 : error<()>) -> <async,exn,ndet> ()
  = fn<<async,exn,ndet>>(@y-x11081: error<()>){
    val i@12241 : hnd/ev-index
      = std/core/types/@make-ssize_t(1);
    val w : hnd/evv<<exn,async,ndet>>
      = std/core/hnd/evv-swap-create1(i@12241);
    val y : ()
      = match (@y-x11081) {
        ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@1@0: string), (@pat@1@0: exception-info)) : exception ) as exn@0: exception)) : error<()> ) as @pat@4@0: (error<()>))
           -> val ev@12244 : hnd/ev<exn>
                    = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
          (match (ev@12244) {
            ((@skip std/core/hnd/Ev<e,a>((@pat@0@0: hnd/htag<exn>), (m: hnd/marker<e,a>), (h: exn<e,a>), (@pat@1@1: hnd/evv<e>)) : hnd/ev<exn> ) as @pat@1: (hnd/ev<exn>))
               -> (match ((std/core/exn/throw-exn/@select(h))) {
                ((@skip std/core/hnd/Clause1((f@0: (hnd/marker<e,a>, hnd/ev<exn>, exception) -> e ())) : hnd/clause1<exception,(),exn,e,a> ) as @pat@2: (hnd/clause1<exception,(),exn,e,a>))
                   -> f@0(m, ev@12244, exn@0);
              });
          });
        ((@skip std/core/exn/Ok((x@1: ())) : error<()> ) as @pat@2@0: (error<()>))
           -> x@1;
      };
    val _ : ()
      = std/core/hnd/evv-set(w);
    match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-cont((forall<a> fn<<exn,async,ndet>>(cont: (a) -> <exn,async,ndet> (), res: a){
          std/core/hnd/open-at1(i@12241, cont, res);
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> y;
    };
  };
// Wait (asynchronously) for optional `secs` seconds `:duration` (`= 0.seconds`).
// Use `yield()` to yield generally to other asynchronous operations.
pub fun duration/wait : (secs : ? std/time/duration/duration, ?set-timeout : (unit-cb, int32) -> <st<global>,console/console,div,fsys,ndet,net,ui> any, ?clear-timeout : (any) -> <st<global>,console/console,div,fsys,ndet,net,ui> ()) -> <async,exn,ndet> ()
  = fn<asyncx>(secs: ? std/time/duration/duration, @implicit/set-timeout: (unit-cb, int32) -> io-noexn any, @implicit/clear-timeout: (any) -> io-noexn ()){
    val w : hnd/evv<<async,exn,ndet>>
      = std/core/hnd/evv-swap-create0();
    val x : bool
      = std/time/duration/(<=)((match (secs) {
          ((std/core/types/@Optional((@uniq-secs@8143: std/time/duration/duration)) : ? std/time/duration/duration ) as @pat: ? std/time/duration/duration)
             -> @uniq-secs@8143;
          ((@skip std/core/types/@None() : ? std/time/duration/duration ) as @pat@0: ? std/time/duration/duration)
             -> std/time/duration/zero;
        }), std/time/duration/zero);
    val keep : ()
      = std/core/hnd/evv-set(w);
    match (x) {
      ((std/core/types/True() : bool ) as @pat@1: bool)
         -> std/async/async/yield(?set-timeout);
      ((@skip std/core/types/False() : bool ) as @pat@2: bool)
         -> val w@0 : hnd/evv<<async,exn,ndet>>
              = std/core/hnd/evv-swap-create0();
            val x@0 : int
              = std/time/duration/milli-seconds((match (secs) {
                ((std/core/types/@Optional((@uniq-secs@8143@0: std/time/duration/duration)) : ? std/time/duration/duration ) as @pat@4: ? std/time/duration/duration)
                   -> @uniq-secs@8143@0;
                ((@skip std/core/types/@None() : ? std/time/duration/duration ) as @pat@0@1: ? std/time/duration/duration)
                   -> std/time/duration/zero;
              }));
            val keep@0 : ()
              = std/core/hnd/evv-set(w@0);
            val @x-x2@0@11353 : int32
              = std/num/int32/int32(x@0);
            val w@1 : hnd/evv<<async,exn,ndet>>
              = std/core/hnd/evv-swap-create0();
            val x@1 : int32
              = (match ((std/num/int32/(>=)(std/num/int32/zero, @x-x2@0@11353))) {
                ((std/core/types/True() : bool ) as @pat@3: bool)
                   -> std/num/int32/zero;
                ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
                   -> @x-x2@0@11353;
              });
            val keep@1 : ()
              = std/core/hnd/evv-set(w@1);
            val i@0@12258 : (hnd/ev-index == 1 ssize_t)
              = std/core/types/@make-ssize_t(0);
            val w@2 : hnd/evv<<async,exn,ndet>>
              = std/core/hnd/evv-swap-create1(i@0@12258);
            val ev@12261 : hnd/ev<async>
              = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
            val y : error<()>
              = (match (ev@12261) {
                ((@skip std/core/hnd/Ev<e,a>((@pat@0@4: hnd/htag<async>), (m: hnd/marker<e,a>), (h: async<e,a>), (@pat@1@0: hnd/evv<e>)) : hnd/ev<async> ) as @pat@7: (hnd/ev<async>))
                   -> (match (h) {
                    ((@skip std/async/async/@Hnd-async((@pat@0@2: int), (@pat@1@1: forall<b> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) b,b,async,e,a>), (@pat@2@0: hnd/clause1<scope,(),async,e,a>), (@ctl-do-await: forall<b> hnd/clause1<((await-setup<b> == 4 (cb : (error<b>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,
   alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<b>,async,e,a>), (@pat@3@0: (forall<b> hnd/clause1<((await-setup<b> == 4 (cb : (error<b>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<
   global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<b>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>
   >)>)>) ()),(),async,e,a>))) : async<e,a> ) as @pat@5: (async<e,a>))
                       -> (match (@ctl-do-await) {
                        ((@skip std/core/hnd/Clause1((f@3: (hnd/marker<e,a>, hnd/ev<async>, ((await-setup<()> == 4 (cb : (error<()>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global>
   == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool)) -> e error<()>)) : hnd/clause1<((await-setup<()> == 4 (cb : (error<()>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,
   ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<()>,async,e,a> ) as @pat@2@0@0: (hnd/clause1<((await-setup<()> == 4 (cb : (error<()>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 
   2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<()>,async,e,a>))
                           -> f@3(m, ev@12261, (std/core/types/Tuple3((fn<(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>(cb: (error<()>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()){
                                (match ((std/core/exn/exn/@handle((std/core/exn/@Hnd-exn(0, (forall<b> std/core/hnd/Clause1((fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(m@0: hnd/marker<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>,error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>>, @_wildcard-x653_16: hnd/ev<exn>, x@4: exception
   ){
                                      (std/core/hnd/yield-to-final(m@0, (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@_wildcard-x653_45: (hnd/resume-result<b,error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>>) -> <alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>> error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/
   console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>){
                                          (std/core/exn/Error(x@4));
                                        })));
                                    }))))), (fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(@res: error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>){
                                    @res;
                                  }), (fn<<exn,alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(){
                                    val w@3 : (hnd/evv<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>,exn>>)
                                      = (std/core/hnd/evv-swap-create0());
                                    val x@6 : timeout-id
                                      = (std/async/async/Timeout-id((?set-timeout((fn<<(st<global> == 1 <alloc<global>,read<global>,write<global>>),console/console,div,fsys,ndet,net,ui>>(){
                                          (cb((std/core/exn/Ok(std/core/types/Unit)), std/core/types/True));
                                        }), (match ((std/num/int32/(>=)(x@1, std/num/int32/zero))) {
                                          ((std/core/types/True() : bool ) as @pat@5@0@0: bool)
                                             -> x@1;
                                          ((@skip std/core/types/False() : bool ) as @pat@0@2@0@0: bool)
                                             -> std/num/int32/zero;
                                        })))));
                                    val keep@2 : ()
                                      = (std/core/hnd/evv-set(w@3));
                                    (match ((std/core/hnd/yielding())) {
                                      ((std/core/types/True() : bool ) as @pat@8: bool)
                                         -> std/core/hnd/yield-extend(std/async/async/duration/@mlift-wait@11447);
                                      ((@skip std/core/types/False() : bool ) as @pat@0@5: bool)
                                         -> std/core/exn/Ok((std/core/types/Just((fn<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>>>(){
                                          (?clear-timeout((match (x@6) {
                                            ((@skip std/async/async/Timeout-id((@x: any)) : timeout-id ) as @pat@6@0: timeout-id)
                                               -> @x;
                                          })));
                                        }))));
                                    });
                                  })))) {
                                  ((std/core/exn/Ok((mcleanup: maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)) : error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>> ) as @pat@5@0: (error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,
   write<global>,alloc<global>>)>)>) ()>>))
                                     -> mcleanup;
                                  ((@skip std/core/exn/Error(((@skip std/core/exn/Exception((@pat@1@1@0: string), (@pat@2@1: exception-info)) : exception ) as exn: exception)) : error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>> ) as @pat@0@2@0: (error<maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>>))
                                     -> val _ : ()
                                              = cb((std/core/exn/Error(exn)), std/core/types/True);
                                    std/core/types/Nothing;
                                });
                              }), std/async/async/empty-scope, std/core/types/True)));
                      });
                  });
              });
            val _ : ()
              = std/core/hnd/evv-set(w@2);
            val x@2@12255 : error<()>
              = (match ((std/core/hnd/yielding())) {
                ((std/core/types/True() : bool ) as @pat@6: bool)
                   -> std/core/hnd/yield-cont((forall<a> fn<<async,exn,ndet>>(cont: (a) -> <async,exn,ndet> error<()>, res: a){
                    std/core/hnd/open-at1(i@0@12258, cont, res);
                  }));
                ((@skip std/core/types/False() : bool ) as @pat@0@3: bool)
                   -> y;
              });
        (match ((std/core/hnd/yielding())) {
          ((std/core/types/True() : bool ) as @pat@5@1: bool)
             -> std/core/hnd/yield-extend(std/async/async/duration/@mlift-wait@11448);
          ((@skip std/core/types/False() : bool ) as @pat@0@2@1: bool)
             -> val i@1@12273 : (hnd/ev-index == 1 ssize_t)
                  = std/core/types/@make-ssize_t(1);
                val w@4 : hnd/evv<<exn,async,ndet>>
                  = std/core/hnd/evv-swap-create1(i@1@12273);
                val y@0 : ()
                  = (match (x@2@12255) {
                    ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@1@0: string), (@pat@1@0@0: exception-info)) : exception ) as exn@0: exception)) : error<()> ) as @pat@4@0: (error<()>))
                       -> val ev@0@12276 : hnd/ev<exn>
                                = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
                      (match (ev@0@12276) {
                        ((@skip std/core/hnd/Ev<e,a>((@pat@0@7: hnd/htag<exn>), (m@1: hnd/marker<e,a>), (h@0: exn<e,a>), (@pat@1@2: hnd/evv<e>)) : hnd/ev<exn> ) as @pat@10: (hnd/ev<exn>))
                           -> (match ((std/core/exn/throw-exn/@select(h@0))) {
                            ((@skip std/core/hnd/Clause1((f@6: (hnd/marker<e,a>, hnd/ev<exn>, exception) -> e ())) : hnd/clause1<exception,(),exn,e,a> ) as @pat@2@2: (hnd/clause1<exception,(),exn,e,a>))
                               -> f@6(m@1, ev@0@12276, exn@0);
                          });
                      });
                    ((@skip std/core/exn/Ok((x@9: ())) : error<()> ) as @pat@2@0@0@0: (error<()>))
                       -> x@9;
                  });
                val _ : ()
                  = std/core/hnd/evv-set(w@4);
            (match ((std/core/hnd/yielding())) {
              ((std/core/types/True() : bool ) as @pat@9: bool)
                 -> std/core/hnd/yield-cont((forall<a> fn<<exn,async,ndet>>(cont@0: (a) -> <exn,async,ndet> (), res@1: a){
                  std/core/hnd/open-at1(i@1@12273, cont@0, res@1);
                }));
              ((@skip std/core/types/False() : bool ) as @pat@0@6: bool)
                 -> y@0;
            });
        });
    };
  };
// Wait (asynchronously) for `secs` seconds as a `:double`.
// Use `yield()` to yield to other asynchronous operations.
pub fun float/wait : (secs : float64, ?set-timeout : (unit-cb, int32) -> <st<global>,console/console,div,fsys,ndet,net,ui> any, ?clear-timeout : (any) -> <st<global>,console/console,div,fsys,ndet,net,ui> ()) -> <async,exn,ndet> ()
  = fn<asyncx>(secs: float64, @implicit/set-timeout: (unit-cb, int32) -> io-noexn any, @implicit/clear-timeout: (any) -> io-noexn ()){
    std/async/async/duration/wait((std/core/types/@Optional((std/time/duration/Duration((std/num/ddouble/Ddouble(secs, 0.0)))))), ?set-timeout, ?clear-timeout);
  };
// monadic lift
fun @mlift-timeout@11449 : forall<a,e> (wild_ : ()) -> <async,exn,ndet|e> maybe<a>
  = forall<a,e> fn<<async,exn,ndet|e>>(wild_: ()){
    std/core/types/Nothing;
  };
// monadic lift
fun @mlift-timeout@11450 : forall<a,e> (@y-x11086 : a) -> <asyncx|e> maybe<a>
  = forall<a,e> fn<<asyncx|e>>(@y-x11086: a){
    std/core/types/Just(@y-x11086);
  };
pub fun timeout : forall<a,e> (secs : std/time/duration/duration, action : () -> <asyncx|e> a, ?set-timeout : (unit-cb, int32) -> io-noexn any, ?clear-timeout : (any) -> io-noexn ()) -> <asyncx|e> maybe<a>
  = forall<a,e> fn<<asyncx|e>>(secs: std/time/duration/duration, action: () -> <asyncx|e> a, @implicit/set-timeout: (unit-cb, int32) -> io-noexn any, @implicit/clear-timeout: (any) -> io-noexn ()){
    std/async/async/cancelable((fn<<async,exn,ndet|e>>(){
      val x@12205 : (error<maybe<a>>, error<maybe<a>>)
            = (std/async/async/interleavedx((fn<<async-exn,exn,ndet|e>>(){
                val x@0@12207 : hnd/ev-index
                  = (std/core/hnd/@evv-index(std/core/exn/exn/@tag));
                val next@0@12208 : ((hnd/ev-index) -> <exn,exn,async,ndet|e> maybe<a>)
                  = (fn<<exn,exn,async,ndet|e>>(@y-x11056: hnd/ev-index){
                    (std/async/async/@mlift-firstof@11440((fn<<async-exn,ndet|e>>(){
                        val indices@12281 : (vector<hnd/ev-index>)
                          = (std/core/vector/unvlist((std/core/types/Cons((std/core/hnd/@evv-index(std/async/async/async/@tag)), (std/core/types/Cons((std/core/hnd/@evv-index(std/core/exn/exn/@tag)), std/core/types/Nil))))));
                        val w : (hnd/evv<<async,exn,ndet|e>>)
                          = (std/core/hnd/evv-swap-create(indices@12281));
                        val y : ()
                          = (std/async/async/duration/wait((std/core/types/@Optional(secs)), ?set-timeout, ?clear-timeout));
                        val _ : ()
                          = (std/core/hnd/evv-set(w));
                        val x@12279 : ()
                          = (match ((std/core/hnd/yielding())) {
                            ((std/core/types/True() : bool ) as @pat@1@0: bool)
                               -> std/core/hnd/yield-cont((forall<b> fn<<async,exn,ndet|e>>(cont: (b) -> <async,exn,ndet|e> (), res: b){
                                std/core/hnd/open1(indices@12281, cont, res);
                              }));
                            ((@skip std/core/types/False() : bool ) as @pat@0@0@0: bool)
                               -> y;
                          });
                        (match ((std/core/hnd/yielding())) {
                          ((std/core/types/True() : bool ) as @pat@3: bool)
                             -> std/core/hnd/yield-extend((fn<<async,exn,ndet|e>>(wild_: ()){
                              std/core/types/Nothing;
                            }));
                          ((@skip std/core/types/False() : bool ) as @pat@0@2: bool)
                             -> std/core/types/Nothing;
                        });
                      }), @y-x11056));
                  });
                (match ((std/core/hnd/yielding())) {
                  ((std/core/types/True() : bool ) as @pat@1: bool)
                     -> std/core/hnd/yield-extend(next@0@12208);
                  ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
                     -> next@0@12208(x@0@12207);
                });
              }), (fn<<async-exn,exn,ndet|e>>(){
                val x@1@12209 : hnd/ev-index
                  = (std/core/hnd/@evv-index(std/core/exn/exn/@tag));
                val next@1@12210 : ((hnd/ev-index) -> <exn,exn,async,ndet|e> maybe<a>)
                  = (fn<<exn,exn,async,ndet|e>>(@y-x11060: hnd/ev-index){
                    (std/async/async/@mlift-firstof@11443((fn<<async-exn,ndet|e>>(){
                        val x@0@12287 : a
                              = (action());
                        (match ((std/core/hnd/yielding())) {
                          ((std/core/types/True() : bool ) as @pat@2@0: bool)
                             -> std/core/hnd/yield-extend((fn<<(asyncx == 1 <async,exn,ndet>)|e>>(@y-x11086: a){
                              (std/core/types/Just(@y-x11086));
                            }));
                          ((@skip std/core/types/False() : bool ) as @pat@0@1@0: bool)
                             -> std/core/types/Just(x@0@12287);
                        });
                      }), @y-x11060));
                  });
                (match ((std/core/hnd/yielding())) {
                  ((std/core/types/True() : bool ) as @pat@2: bool)
                     -> std/core/hnd/yield-extend(next@1@12210);
                  ((@skip std/core/types/False() : bool ) as @pat@0@1: bool)
                     -> next@1@12210(x@1@12209);
                });
              })));
      (match ((std/core/hnd/yielding())) {
        ((std/core/types/True() : bool ) as @pat: bool)
           -> std/core/hnd/yield-extend((fn<<async,exn,ndet|e>>(@y-x11064: (error<maybe<a>>, error<maybe<a>>)){
            (std/async/async/@mlift-firstof@11444(@y-x11064));
          }));
        ((@skip std/core/types/False() : bool ) as @pat@0: bool)
           -> std/async/async/@mlift-firstof@11444(x@12205);
      });
    }));
  };
// monadic lift
fun list/@mlift-trmc-lift-interleaved@10768@11451 : forall<a,e> (@uniq-x@10684 : () -> <async-exn|e> a, @y-x11088 : hnd/ev-index) -> <exn,exn,async|e> a
  = forall<a,e> fn<<exn,exn,async|e>>(@uniq-x@10684: () -> <async-exn|e> a, @y-x11088: hnd/ev-index){
    val w0 : hnd/evv<hnd/_e2>
      = std/core/hnd/evv-swap-delete(@y-x11088, std/core/types/True);
    val x : a
      = @uniq-x@10684();
    val _ : ()
      = std/core/hnd/evv-set(w0);
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-cont((forall<b> fn<<exn,exn,async|e>>(cont: (b) -> <exn,exn,async|e> a, res: b){
          std/core/hnd/mask-at1(@y-x11088, std/core/types/True, cont, res);
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> x;
    });
  };
// monadic lift
fun list/@mlift-trmcm-lift-interleaved@10768@11452 : forall<a,e> (@uniq-x@10684 : () -> <async-exn|e> a, @y-x11092 : hnd/ev-index) -> <exn,exn,async|e> a
  = forall<a,e> fn<<exn,exn,async|e>>(@uniq-x@10684@0: () -> <async-exn|e> a, @y-x11092: hnd/ev-index){
    val w0@0 : hnd/evv<hnd/_e2>
      = std/core/hnd/evv-swap-delete(@y-x11092, std/core/types/True);
    val x@0 : a
      = @uniq-x@10684@0();
    val _ : ()
      = std/core/hnd/evv-set(w0@0);
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat@1: bool)
         -> std/core/hnd/yield-cont((forall<b> fn<<exn,exn,async|e>>(cont@0: (b) -> <exn,exn,async|e> a, res@0: b){
          std/core/hnd/mask-at1(@y-x11092, std/core/types/True, cont@0, res@0);
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
         -> x@0;
    });
  };
// lifted local: list/@lift-interleaved@10767, list/interleaved, @spec-x10687
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10682, using:
// @uniq-f@10682 = (fn<<(std/async/async/async :: (E, V) -> V),(exn :: (E, V) -> V)|(e :: E)>>(f: () -> <(std/async/async/async-exn :: E)|(8489 :: E)> 8488){
//   fn<<(std/async/async/async-exn :: E),(exn :: (E, V) -> V)|(e :: E)>>(){
//     std/core/hnd/@mask-at<a,<(exn :: (E, V) -> V),(std/async/async/async :: (E, V) -> V)|(e :: E)>,<(exn :: (E, V) -> V),(exn :: (E, V) -> V),(std/async/async/async :: (E, V) -> V)|(e :: E)>>((std/core/hnd/@evv-index<<(exn :: (E, V) -> V),(exn :: (E, V) -> V),(std/async/async/async :: (E, V) -> V)|(e :: E)>>(std/core/exn/exn/@tag)), std/core/types/True, f);
//   };
// },Own)
fun list/@trmc-lift-interleaved@10768 : forall<a,e> (@uniq-xs@10681 : list<() -> <async-exn|e> a>, @acc : ctx<list<() -> <async-exn,exn|e> a>>) -> <async,exn|e> list<() -> <async-exn,exn|e> a>
  = forall<a,e> fn<<async,exn|e>>(@uniq-xs@10681: list<() -> <async-exn|e> a>, @acc: ctx<list<() -> <async-exn,exn|e> a>>){
    (match (@uniq-xs@10681) {
      ((std/core/types/Cons((@uniq-x@10684@1: () -> <(async-exn == 1 <async,exn>)|e> a), (@uniq-xx@10685: list<() -> <(async-exn == 1 <async,exn>)|e> a>)) : list<() -> <(async-exn == 1 <async,exn>)|e> a> ) as @uniq-pat@10683: (list<() -> <(async-exn == 1 <async,exn>)|e> a>))
         -> val @trmc-x10824 : list<() -> <(async-exn == 1 <async,exn>),exn|e> a>
              = std/core/types/@cctx-hole-create();
            val @trmc-x10825 : list<() -> <(async-exn == 1 <async,exn>),exn|e> a>
              = std/core/types/Cons((fn<<(async-exn == 1 <async,exn>),exn|e>>(){
                  val x@1@12296 : (hnd/ev-index == 1 ssize_t)
                        = (std/core/hnd/@evv-index(std/core/exn/exn/@tag));
                  (match ((std/core/hnd/yielding())) {
                    ((std/core/types/True() : bool ) as @pat@2: bool)
                       -> std/core/hnd/yield-extend((fn<<exn,exn,async|e>>(@y-x11088@0: (hnd/ev-index == 1 ssize_t)){
                        (std/async/async/list/@mlift-trmc-lift-interleaved@10768@11451(@uniq-x@10684@1, @y-x11088@0));
                      }));
                    ((@skip std/core/types/False() : bool ) as @pat@0@1: bool)
                       -> std/async/async/list/@mlift-trmc-lift-interleaved@10768@11451(@uniq-x@10684@1, x@1@12296);
                  });
                }), @trmc-x10824);
        std/async/async/list/@trmc-lift-interleaved@10768(@uniq-xx@10685, (std/core/types/@cctx-extend(@acc, @trmc-x10825, (std/core/types/@field-addr-of(@trmc-x10825, "(\x22std/core/types\x22,\x22\x22,\x22Cons\x22)", "(\x22\x22,\x22\x22,\x22tail\x22)")))));
      ((@skip std/core/types/Nil() : list<() -> <(async-exn == 1 <async,exn>)|e> a> ) as @uniq-pat@0@10686: (list<() -> <(async-exn == 1 <async,exn>)|e> a>))
         -> std/core/types/cctx/((++.))(@acc, std/core/types/Nil);
    });
  };
// lifted local: list/@lift-interleaved@10767, list/interleaved, @spec-x10687
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10682, using:
// @uniq-f@10682 = (fn<<(std/async/async/async :: (E, V) -> V),(exn :: (E, V) -> V)|(e :: E)>>(f: () -> <(std/async/async/async-exn :: E)|(8489 :: E)> 8488){
//   fn<<(std/async/async/async-exn :: E),(exn :: (E, V) -> V)|(e :: E)>>(){
//     std/core/hnd/@mask-at<a,<(exn :: (E, V) -> V),(std/async/async/async :: (E, V) -> V)|(e :: E)>,<(exn :: (E, V) -> V),(exn :: (E, V) -> V),(std/async/async/async :: (E, V) -> V)|(e :: E)>>((std/core/hnd/@evv-index<<(exn :: (E, V) -> V),(exn :: (E, V) -> V),(std/async/async/async :: (E, V) -> V)|(e :: E)>>(std/core/exn/exn/@tag)), std/core/types/True, f);
//   };
// },Own)
fun list/@trmcm-lift-interleaved@10768 : forall<a,e> (@uniq-xs@10681 : list<() -> <async-exn|e> a>, @accm : (list<() -> <async-exn,exn|e> a>) -> list<() -> <async-exn,exn|e> a>) -> <async,exn|e> list<() -> <async-exn,exn|e> a>
  = forall<a,e> fn<<async,exn|e>>(@uniq-xs@10681@0: list<() -> <async-exn|e> a>, @accm: (list<() -> <async-exn,exn|e> a>) -> list<() -> <async-exn,exn|e> a>){
    (match (@uniq-xs@10681@0) {
      ((std/core/types/Cons((@uniq-x@10684@2: () -> <(async-exn == 1 <async,exn>)|e> a), (@uniq-xx@10685@0: list<() -> <(async-exn == 1 <async,exn>)|e> a>)) : list<() -> <(async-exn == 1 <async,exn>)|e> a> ) as @uniq-pat@10683@0: (list<() -> <(async-exn == 1 <async,exn>)|e> a>))
         -> std/async/async/list/@trmcm-lift-interleaved@10768(@uniq-xx@10685@0, (fn(@trmc-x10827: list<() -> <(async-exn == 1 <async,exn>),exn|e> a>){
            (@accm((std/core/types/Cons((fn<<(async-exn == 1 <async,exn>),exn|e>>(){
                val x@2@12298 : (hnd/ev-index == 1 ssize_t)
                      = (std/core/hnd/@evv-index(std/core/exn/exn/@tag));
                (match ((std/core/hnd/yielding())) {
                  ((std/core/types/True() : bool ) as @pat@3: bool)
                     -> std/core/hnd/yield-extend((fn<<exn,exn,async|e>>(@y-x11092@0: (hnd/ev-index == 1 ssize_t)){
                      (std/async/async/list/@mlift-trmcm-lift-interleaved@10768@11452(@uniq-x@10684@2, @y-x11092@0));
                    }));
                  ((@skip std/core/types/False() : bool ) as @pat@0@2: bool)
                     -> std/async/async/list/@mlift-trmcm-lift-interleaved@10768@11452(@uniq-x@10684@2, x@2@12298);
                });
              }), @trmc-x10827))));
          }));
      ((@skip std/core/types/Nil() : list<() -> <(async-exn == 1 <async,exn>)|e> a> ) as @uniq-pat@0@10686@0: (list<() -> <(async-exn == 1 <async,exn>)|e> a>))
         -> @accm(std/core/types/Nil);
    });
  };
// lifted local: list/@lift-interleaved@10767, list/interleaved, @spec-x10687
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10682, using:
// @uniq-f@10682 = (fn<<(std/async/async/async :: (E, V) -> V),(exn :: (E, V) -> V)|(e :: E)>>(f: () -> <(std/async/async/async-exn :: E)|(8489 :: E)> 8488){
//   fn<<(std/async/async/async-exn :: E),(exn :: (E, V) -> V)|(e :: E)>>(){
//     std/core/hnd/@mask-at<a,<(exn :: (E, V) -> V),(std/async/async/async :: (E, V) -> V)|(e :: E)>,<(exn :: (E, V) -> V),(exn :: (E, V) -> V),(std/async/async/async :: (E, V) -> V)|(e :: E)>>((std/core/hnd/@evv-index<<(exn :: (E, V) -> V),(exn :: (E, V) -> V),(std/async/async/async :: (E, V) -> V)|(e :: E)>>(std/core/exn/exn/@tag)), std/core/types/True, f);
//   };
// },Own)
fun list/@lift-interleaved@10768 : forall<a,e> (@uniq-xs@10681 : list<() -> <async-exn|e> a>) -> <async,exn|e> list<() -> <async-exn,exn|e> a>
  = forall<a,e> fn<<async,exn|e>>(@uniq-xs@10681@1: list<() -> <async-exn|e> a>){
    (match ((std/core/hnd/@evv-is-affine())) {
      ((std/core/types/True() : bool ) as @pat@4: bool)
         -> std/async/async/list/@trmc-lift-interleaved@10768(@uniq-xs@10681@1, (std/core/types/cctx/empty()));
      (@pat@0@3: bool)
         -> std/async/async/list/@trmcm-lift-interleaved@10768(@uniq-xs@10681@1, (fn(@trmc-x10826: list<() -> <(async-exn == 1 <async,exn>),exn|e> a>){
            @trmc-x10826;
          }));
    });
  };
// lifted local: list/interleaved, @spec-x10680
// specialized: std/core/list/map, on parameters @uniq-f@10677, using:
// @uniq-f@10677 = (fn<<(std/async/async/async :: (E, V) -> V),(exn :: (E, V) -> V)|(e :: E)>>(f: () -> <(std/async/async/async-exn :: E)|(8489 :: E)> 8488){
//   fn<<(std/async/async/async-exn :: E),(exn :: (E, V) -> V)|(e :: E)>>(){
//     std/core/hnd/@mask-at<a,<(exn :: (E, V) -> V),(std/async/async/async :: (E, V) -> V)|(e :: E)>,<(exn :: (E, V) -> V),(exn :: (E, V) -> V),(std/async/async/async :: (E, V) -> V)|(e :: E)>>((std/core/hnd/@evv-index<<(exn :: (E, V) -> V),(exn :: (E, V) -> V),(std/async/async/async :: (E, V) -> V)|(e :: E)>>(std/core/exn/exn/@tag)), std/core/types/True, f);
//   };
// },Own)
fun list/@lift-interleaved@10767 : forall<a,e> (@uniq-xs@10676 : list<() -> <async-exn|e> a>) -> <async,exn|e> list<() -> <async-exn,exn|e> a>
  = forall<a,e> fn<<async,exn|e>>(@uniq-xs@10676: list<() -> <async-exn|e> a>){
    (match (@uniq-xs@10676) {
      ((std/core/types/Nil() : list<() -> <(async-exn == 1 <async,exn>)|e> a> ) as @uniq-pat@0@10678: (list<() -> <(async-exn == 1 <async,exn>)|e> a>))
         -> std/core/types/Nil;
      (@uniq-pat@10679: (list<() -> <(async-exn == 1 <async,exn>)|e> a>))
         -> std/async/async/list/@lift-interleaved@10768(@uniq-xs@10676);
    });
  };
// monadic lift
fun list/@mlift-trmc-lift-interleaved@10770@11453 : forall<a,e> (@acc : ctx<list<error<a>>>, @uniq-xx@10698 : list<() -> <async-exn,exn|e> a>, @trmc-x10828 : error<a>) -> <async,exn|e> list<error<a>>
  = forall<a,e> fn<<async,exn|e>>(@acc: ctx<list<error<a>>>, @uniq-xx@10698: list<() -> <async-exn,exn|e> a>, @trmc-x10828: error<a>){
    val @trmc-x10829 : list<error<a>>
      = std/core/types/@cctx-hole-create();
    val @trmc-x10830 : list<error<a>>
      = std/core/types/Cons(@trmc-x10828, @trmc-x10829);
    std/async/async/list/@trmc-lift-interleaved@10770(@uniq-xx@10698, (std/core/types/@cctx-extend(@acc, @trmc-x10830, (std/core/types/@field-addr-of(@trmc-x10830, "(\x22std/core/types\x22,\x22\x22,\x22Cons\x22)", "(\x22\x22,\x22\x22,\x22tail\x22)")))));
  };
// monadic lift
fun list/@mlift-trmcm-lift-interleaved@10770@11454 : forall<a,e> (@accm : (list<error<a>>) -> list<error<a>>, @uniq-xx@10698 : list<() -> <async-exn,exn|e> a>, @trmc-x10833 : error<a>) -> <async,exn|e> list<error<a>>
  = forall<a,e> fn<<async,exn|e>>(@accm: (list<error<a>>) -> list<error<a>>, @uniq-xx@10698@0: list<() -> <async-exn,exn|e> a>, @trmc-x10833: error<a>){
    std/async/async/list/@trmcm-lift-interleaved@10770(@uniq-xx@10698@0, (fn(@trmc-x10832: list<error<a>>){
        (@accm((std/core/types/Cons(@trmc-x10833, @trmc-x10832))));
      }));
  };
// lifted local: list/@lift-interleaved@10769, ress, list/interleaved, @spec-x10700
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10695, using:
// @uniq-f@10695 = (std/async/async/unsafe-try-all<a,<(std/async/async/async :: (E, V) -> V),(exn :: (E, V) -> V)|(e :: E)>>,Own)
fun list/@trmc-lift-interleaved@10770 : forall<a,e> (@uniq-xs@10694 : list<() -> <async-exn,exn|e> a>, @acc : ctx<list<error<a>>>) -> <async,exn|e> list<error<a>>
  = forall<a,e> fn<<async,exn|e>>(@uniq-xs@10694: list<() -> <async-exn,exn|e> a>, @acc@0: ctx<list<error<a>>>){
    (match (@uniq-xs@10694) {
      ((std/core/types/Cons((@uniq-x@10697: () -> <(async-exn == 1 <async,exn>),exn|e> a), (@uniq-xx@10698@1: list<() -> <(async-exn == 1 <async,exn>),exn|e> a>)) : list<() -> <(async-exn == 1 <async,exn>),exn|e> a> ) as @uniq-pat@10696: (list<() -> <(async-exn == 1 <async,exn>),exn|e> a>))
         -> val x@12300 : error<a>
                  = std/async/async/unsafe-try-all(@uniq-x@10697);
        (match ((std/core/hnd/yielding())) {
          ((std/core/types/True() : bool ) as @pat: bool)
             -> std/core/hnd/yield-extend((fn<<async,exn|e>>(@trmc-x10828@0: error<a>){
              (std/async/async/list/@mlift-trmc-lift-interleaved@10770@11453(@acc@0, @uniq-xx@10698@1, @trmc-x10828@0));
            }));
          ((@skip std/core/types/False() : bool ) as @pat@0: bool)
             -> val @trmc-x10829@0 : list<error<a>>
                  = std/core/types/@cctx-hole-create();
                val @trmc-x10830@0 : list<error<a>>
                  = std/core/types/Cons(x@12300, @trmc-x10829@0);
            std/async/async/list/@trmc-lift-interleaved@10770(@uniq-xx@10698@1, (std/core/types/@cctx-extend(@acc@0, @trmc-x10830@0, (std/core/types/@field-addr-of(@trmc-x10830@0, "(\x22std/core/types\x22,\x22\x22,\x22Cons\x22)", "(\x22\x22,\x22\x22,\x22tail\x22)")))));
        });
      ((@skip std/core/types/Nil() : list<() -> <(async-exn == 1 <async,exn>),exn|e> a> ) as @uniq-pat@0@10699: (list<() -> <(async-exn == 1 <async,exn>),exn|e> a>))
         -> std/core/types/cctx/((++.))(@acc@0, std/core/types/Nil);
    });
  };
// lifted local: list/@lift-interleaved@10769, ress, list/interleaved, @spec-x10700
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10695, using:
// @uniq-f@10695 = (std/async/async/unsafe-try-all<a,<(std/async/async/async :: (E, V) -> V),(exn :: (E, V) -> V)|(e :: E)>>,Own)
fun list/@trmcm-lift-interleaved@10770 : forall<a,e> (@uniq-xs@10694 : list<() -> <async-exn,exn|e> a>, @accm : (list<error<a>>) -> list<error<a>>) -> <async,exn|e> list<error<a>>
  = forall<a,e> fn<<async,exn|e>>(@uniq-xs@10694@0: list<() -> <async-exn,exn|e> a>, @accm@0: (list<error<a>>) -> list<error<a>>){
    (match (@uniq-xs@10694@0) {
      ((std/core/types/Cons((@uniq-x@10697@0: () -> <(async-exn == 1 <async,exn>),exn|e> a), (@uniq-xx@10698@2: list<() -> <(async-exn == 1 <async,exn>),exn|e> a>)) : list<() -> <(async-exn == 1 <async,exn>),exn|e> a> ) as @uniq-pat@10696@0: (list<() -> <(async-exn == 1 <async,exn>),exn|e> a>))
         -> val x@0@12303 : error<a>
                  = std/async/async/unsafe-try-all(@uniq-x@10697@0);
        (match ((std/core/hnd/yielding())) {
          ((std/core/types/True() : bool ) as @pat@1: bool)
             -> std/core/hnd/yield-extend((fn<<async,exn|e>>(@trmc-x10833@0: error<a>){
              (std/async/async/list/@mlift-trmcm-lift-interleaved@10770@11454(@accm@0, @uniq-xx@10698@2, @trmc-x10833@0));
            }));
          ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
             -> std/async/async/list/@trmcm-lift-interleaved@10770(@uniq-xx@10698@2, (fn(@trmc-x10832@0: list<error<a>>){
                (@accm@0((std/core/types/Cons(x@0@12303, @trmc-x10832@0))));
              }));
        });
      ((@skip std/core/types/Nil() : list<() -> <(async-exn == 1 <async,exn>),exn|e> a> ) as @uniq-pat@0@10699@0: (list<() -> <(async-exn == 1 <async,exn>),exn|e> a>))
         -> @accm@0(std/core/types/Nil);
    });
  };
// lifted local: list/@lift-interleaved@10769, ress, list/interleaved, @spec-x10700
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10695, using:
// @uniq-f@10695 = (std/async/async/unsafe-try-all<a,<(std/async/async/async :: (E, V) -> V),(exn :: (E, V) -> V)|(e :: E)>>,Own)
fun list/@lift-interleaved@10770 : forall<a,e> (@uniq-xs@10694 : list<() -> <async-exn,exn|e> a>) -> <async,exn|e> list<error<a>>
  = forall<a,e> fn<<async,exn|e>>(@uniq-xs@10694@1: list<() -> <async-exn,exn|e> a>){
    (match ((std/core/hnd/@evv-is-affine())) {
      ((std/core/types/True() : bool ) as @pat@2: bool)
         -> std/async/async/list/@trmc-lift-interleaved@10770(@uniq-xs@10694@1, (std/core/types/cctx/empty()));
      (@pat@0@1: bool)
         -> std/async/async/list/@trmcm-lift-interleaved@10770(@uniq-xs@10694@1, (fn(@trmc-x10831: list<error<a>>){
            @trmc-x10831;
          }));
    });
  };
// lifted local: ress, list/interleaved, @spec-x10693
// specialized: std/core/list/map, on parameters @uniq-f@10690, using:
// @uniq-f@10690 = (std/async/async/unsafe-try-all<a,<(std/async/async/async :: (E, V) -> V),(exn :: (E, V) -> V)|(e :: E)>>,Own)
fun list/@lift-interleaved@10769 : forall<a,e> (@uniq-xs@10689 : list<() -> <async-exn,exn|e> a>) -> <async,exn|e> list<error<a>>
  = forall<a,e> fn<<async,exn|e>>(@uniq-xs@10689: list<() -> <async-exn,exn|e> a>){
    (match (@uniq-xs@10689) {
      ((std/core/types/Nil() : list<() -> <(async-exn == 1 <async,exn>),exn|e> a> ) as @uniq-pat@0@10691: (list<() -> <(async-exn == 1 <async,exn>),exn|e> a>))
         -> std/core/types/Nil;
      (@uniq-pat@10692: (list<() -> <(async-exn == 1 <async,exn>),exn|e> a>))
         -> std/async/async/list/@lift-interleaved@10770(@uniq-xs@10689);
    });
  };
// lifted local: list/interleaved, @spec-x10705
// specialized: std/core/list/map, on parameters @uniq-f@10702, using:
// @uniq-f@10702 = (std/core/types/@open<(exn :: (E, V) -> V),<(exn :: (E, V) -> V),(std/async/async/async :: (E, V) -> V)|(e :: E)>,(err : (error :: V -> V)<a>) -> (exn :: (E, V) -> V) a,(err : (error :: V -> V)<a>) -> <(exn :: (E, V) -> V),(std/async/async/async :: (E, V) -> V)|(e :: E)> a>((std/core/exn/untry<a>)),Own)
fun list/@lift-interleaved@10771 : forall<a,e> (@uniq-xs@10701 : list<error<a>>) -> <exn,async|e> list<a>
  = forall<a,e> fn<<exn,async|e>>(@uniq-xs@10701: list<error<a>>){
    (match (@uniq-xs@10701) {
      ((std/core/types/Nil() : list<error<a>> ) as @uniq-pat@0@10703: (list<error<a>>))
         -> std/core/types/Nil;
      (@uniq-pat@10704: (list<error<a>>))
         -> std/core/list/@unroll-map@10010(@uniq-xs@10701, (fn<<exn,async|e>>(@x-x1: error<a>){
            val i@12306 : (hnd/ev-index == 1 ssize_t)
              = (std/core/hnd/@evv-index(std/core/exn/exn/@tag));
            val w : (hnd/evv<<exn,async|e>>)
              = (std/core/hnd/evv-swap-create1(i@12306));
            val y : a
              = (std/core/exn/untry(@x-x1));
            val _ : ()
              = (std/core/hnd/evv-set(w));
            (match ((std/core/hnd/yielding())) {
              ((std/core/types/True() : bool ) as @pat: bool)
                 -> std/core/hnd/yield-cont((forall<b> fn<<exn,async|e>>(cont: (b) -> <exn,async|e> a, res: b){
                  std/core/hnd/open-at1(i@12306, cont, res);
                }));
              ((@skip std/core/types/False() : bool ) as @pat@0: bool)
                 -> y;
            });
          }));
    });
  };
// monadic lift
fun list/@mlift-interleaved@11455 : forall<a,e> (@c-x11119 : list<error<a>>) -> list<a>
  = forall<a,e> fn(@c-x11119: list<error<a>>){
    std/async/async/list/@lift-interleaved@10771(@c-x11119);
  };
// monadic lift
fun list/@mlift-interleaved@11456 : forall<a,e> (xs@0@10160 : list<() -> <async-exn,exn|e> a>) -> <async,exn|e> list<a>
  = forall<a,e> fn<<async,exn|e>>(xs@0@10160: list<() -> <async-exn,exn|e> a>){
    val w : hnd/evv<<async,exn|e>>
      = std/core/hnd/evv-swap-create0();
    val x : int
      = (match (xs@0@10160) {
        ((std/core/types/Nil() : list<() -> <(async-exn == 1 <async,exn>),exn|e> a> ) as @pat@1: (list<() -> <(async-exn == 1 <async,exn>),exn|e> a>))
           -> 0;
        (@pat: (list<() -> <(async-exn == 1 <async,exn>),exn|e> a>))
           -> std/core/list/@unroll-lift-length@5730@10000(xs@0@10160, 0);
      });
    val keep : ()
      = std/core/hnd/evv-set(w);
    val x@0@12311 : list<error<a>>
      = (match ((std/core/int/(==)(x, 0))) {
        ((std/core/types/True() : bool ) as @pat@0@1: bool)
           -> std/core/types/Nil;
        ((@skip std/core/types/False() : bool ) as @pat@0@0@0: bool)
           -> (match ((std/core/int/(==)(x, 1))) {
            ((std/core/types/True() : bool ) as @pat@1@0: bool)
               -> std/async/async/list/@lift-interleaved@10769(xs@0@10160);
            ((@skip std/core/types/False() : bool ) as @pat@2: bool)
               -> std/async/async/interleavedn(x, xs@0@10160);
          });
      });
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat@0: bool)
         -> std/core/hnd/yield-extend((fn(@c-x11119: list<error<a>>){
          (std/async/async/list/@lift-interleaved@10771(@c-x11119));
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
         -> std/async/async/list/@lift-interleaved@10771(x@0@12311);
    });
  };
// Interleave a list of actions around their asynchronous operations.
pub fun list/interleaved : forall<a,e> (xs : list<() -> <async-exn|e> a>) -> <async-exn|e> list<a>
  = forall<a,e> fn<<async-exn|e>>(xs: list<() -> <async-exn|e> a>){
    val x@12314 : list<() -> <async-exn,exn|e> a>
          = std/async/async/list/@lift-interleaved@10767(xs);
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-extend((fn<<async,exn|e>>(xs@0@10160: list<() -> <(async-exn == 1 <async,exn>),exn|e> a>){
          (std/async/async/list/@mlift-interleaved@11456(xs@0@10160));
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> val w : hnd/evv<<async,exn|e>>
              = std/core/hnd/evv-swap-create0();
            val x@0 : int
              = (match (x@12314) {
                ((std/core/types/Nil() : list<() -> <(async-exn == 1 <async,exn>),exn|e> a> ) as @pat@1: (list<() -> <(async-exn == 1 <async,exn>),exn|e> a>))
                   -> 0;
                (@pat@2: (list<() -> <(async-exn == 1 <async,exn>),exn|e> a>))
                   -> std/core/list/@unroll-lift-length@5730@10000(x@12314, 0);
              });
            val keep : ()
              = std/core/hnd/evv-set(w);
            val x@1@12319 : list<error<a>>
              = (match ((std/core/int/(==)(x@0, 0))) {
                ((std/core/types/True() : bool ) as @pat@0@1: bool)
                   -> std/core/types/Nil;
                ((@skip std/core/types/False() : bool ) as @pat@0@0@0: bool)
                   -> (match ((std/core/int/(==)(x@0, 1))) {
                    ((std/core/types/True() : bool ) as @pat@1@0: bool)
                       -> std/async/async/list/@lift-interleaved@10769(x@12314);
                    ((@skip std/core/types/False() : bool ) as @pat@2@0: bool)
                       -> std/async/async/interleavedn(x@0, x@12314);
                  });
              });
        (match ((std/core/hnd/yielding())) {
          ((std/core/types/True() : bool ) as @pat@3: bool)
             -> std/core/hnd/yield-extend((fn(@c-x11119: list<error<a>>){
              (std/async/async/list/@lift-interleaved@10771(@c-x11119));
            }));
          ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
             -> std/async/async/list/@lift-interleaved@10771(x@1@12319);
        });
    });
  };
fun maybe-exn : forall<a> (err : error<a>) -> maybe<exception>
  = forall<a> fn(err: error<a>){
    (match (err) {
      ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0: string), (@pat@1: exception-info)) : exception ) as exn: exception)) : error<a> ) as @pat: (error<a>))
         -> std/core/types/Just(exn);
      (@pat@2: (error<a>))
         -> std/core/types/Nothing;
    });
  };
fun rethrow : forall<a> (exn : exception) -> exn a
  = forall<a> fn<exn>(exn: exception){
    val w : hnd/evv<exn>
      = std/core/hnd/evv-swap-create0();
    val keep : ()
      = std/core/hnd/evv-set(w);
    (match (exn) {
      ((@skip std/core/exn/Exception((@pat@0: string), (@x: exception-info)) : exception ) as @pat: exception)
         -> (match (@x) {
          ((std/async/async/Finalize((yld: hnd/yield-info)) : exception-info ) as @pat@1: exception-info)
             -> std/core/hnd/unsafe-reyield(yld);
          (@pat@0@0: exception-info)
             -> val ev@12325 : hnd/ev<exn>
                      = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
            (match (ev@12325) {
              ((@skip std/core/hnd/Ev<e,b>((@pat@0@1: hnd/htag<exn>), (m: hnd/marker<e,b>), (h: exn<e,b>), (@pat@1@0: hnd/evv<e>)) : hnd/ev<exn> ) as @pat@2: (hnd/ev<exn>))
                 -> (match ((std/core/exn/throw-exn/@select(h))) {
                  ((@skip std/core/hnd/Clause1((f@0: (hnd/marker<e,b>, hnd/ev<exn>, exception) -> e a)) : hnd/clause1<exception,a,exn,e,b> ) as @pat@2@0: (hnd/clause1<exception,a,exn,e,b>))
                     -> f@0(m, ev@12325, exn);
                });
            });
        });
    });
  };
// monadic lift
fun @mlift-lift-ordered_throw@10773@11457 : forall<h> (@uniq-x@10714 : maybe<exception>, exn : exception, mexn : local-var<h,maybe<exception>>, @y-x11124 : maybe<exception>) -> <local<h>,exn> ()
  = forall<h> fn<<local<h>,exn>>(@uniq-x@10714: maybe<exception>, exn: exception, mexn: local-var<h,maybe<exception>>, @y-x11124: maybe<exception>){
    (match (@y-x11124) {
      ((std/core/types/Nothing() : maybe<exception> ) as @pat@3: (maybe<exception>))
         -> std/core/types/local-set(mexn, @uniq-x@10714);
      ((@skip std/core/types/Just(((@skip std/core/exn/Exception((@pat@5: string), (@pat@6: exception-info)) : exception ) as exnx: exception)) : maybe<exception> ) as @pat@4: (maybe<exception>))
         -> val w : hnd/evv<<local<h>,exn>>
              = std/core/hnd/evv-swap-create0();
            val keep : ()
              = std/core/hnd/evv-set(w);
        (match (exn) {
          ((@skip std/core/exn/Exception((@pat@0@0: string), (@x: exception-info)) : exception ) as @pat@7: exception)
             -> (match (@x) {
              ((std/async/async/Finalize((@pat@0@1: hnd/yield-info)) : exception-info ) as @pat@8: exception-info)
                 -> val w@0 : hnd/evv<<local<h>,exn>>
                      = std/core/hnd/evv-swap-create0();
                    val keep@0 : ()
                      = std/core/hnd/evv-set(w@0);
                    val w@1 : hnd/evv<<local<h>,exn>>
                      = std/core/hnd/evv-swap-create0();
                    val keep@1 : ()
                      = std/core/hnd/evv-set(w@1);
                (match (exnx) {
                  ((@skip std/core/exn/Exception((@pat@0@3: string), (@x@0: exception-info)) : exception ) as @pat@10: exception)
                     -> (match (@x@0) {
                      ((std/async/async/Finalize((@pat@0@4: hnd/yield-info)) : exception-info ) as @pat@11: exception-info)
                         -> val w@2 : hnd/evv<<local<h>,exn>>
                              = std/core/hnd/evv-swap-create0();
                            val keep@2 : ()
                              = std/core/hnd/evv-set(w@2);
                        (match (exnx) {
                          ((@skip std/core/exn/Exception((@pat@0@5: string), (@x@1: exception-info)) : exception ) as @pat@12: exception)
                             -> (match (@x@1) {
                              ((std/async/async/Cancel() : exception-info ) as @pat@13: exception-info)
                                 -> val w@3 : hnd/evv<<local<h>,exn>>
                                      = std/core/hnd/evv-swap-create0();
                                    val keep@3 : ()
                                      = std/core/hnd/evv-set(w@3);
                                    val w@4 : hnd/evv<<local<h>,exn>>
                                      = std/core/hnd/evv-swap-create0();
                                    val keep@4 : ()
                                      = std/core/hnd/evv-set(w@4);
                                (match (exn) {
                                  ((@skip std/core/exn/Exception((@pat@0@8: string), (@x@2: exception-info)) : exception ) as @pat@15: exception)
                                     -> (match (@x@2) {
                                      ((std/async/async/Cancel() : exception-info ) as @pat@16: exception-info)
                                         -> std/core/types/Unit;
                                      (@pat@0@9: exception-info)
                                         -> std/core/types/local-set(mexn, @uniq-x@10714);
                                    });
                                });
                              (@pat@0@6: exception-info)
                                 -> std/core/types/Unit;
                            });
                        });
                      (@pat@1@1: exception-info)
                         -> std/core/types/local-set(mexn, @uniq-x@10714);
                    });
                });
              (@pat@1@0: exception-info)
                 -> val w@5 : hnd/evv<<local<h>,exn>>
                      = std/core/hnd/evv-swap-create0();
                    val keep@5 : ()
                      = std/core/hnd/evv-set(w@5);
                (match (exnx) {
                  ((@skip std/core/exn/Exception((@pat@0@10: string), (@x@3: exception-info)) : exception ) as @pat@17: exception)
                     -> (match (@x@3) {
                      ((std/async/async/Cancel() : exception-info ) as @pat@18: exception-info)
                         -> val w@6 : hnd/evv<<local<h>,exn>>
                              = std/core/hnd/evv-swap-create0();
                            val keep@6 : ()
                              = std/core/hnd/evv-set(w@6);
                            val w@7 : hnd/evv<<local<h>,exn>>
                              = std/core/hnd/evv-swap-create0();
                            val keep@7 : ()
                              = std/core/hnd/evv-set(w@7);
                        (match (exn) {
                          ((@skip std/core/exn/Exception((@pat@0@13: string), (@x@4: exception-info)) : exception ) as @pat@20: exception)
                             -> (match (@x@4) {
                              ((std/async/async/Cancel() : exception-info ) as @pat@21: exception-info)
                                 -> std/core/types/Unit;
                              (@pat@0@14: exception-info)
                                 -> std/core/types/local-set(mexn, @uniq-x@10714);
                            });
                        });
                      (@pat@0@11: exception-info)
                         -> std/core/types/Unit;
                    });
                });
            });
        });
    });
  };
// monadic lift
fun @mlift-lift-ordered_throw@10773@11458 : forall<h> (@uniq-xx@10715 : list<maybe<exception>>, mexn : local-var<h,maybe<exception>>, @c-x11136 : ()) -> ()
  = forall<h> fn(@uniq-xx@10715: list<maybe<exception>>, mexn@0: local-var<h,maybe<exception>>, @c-x11136: ()){
    std/async/async/@lift-ordered_throw@10773(mexn@0, @uniq-xx@10715);
  };
// lifted local: @lift-ordered_throw@10772, ordered_throw, @spec-x10717
// specialized: std/core/list/@unroll-foreach@10016, on parameters @uniq-action@10712, using:
// @uniq-action@10712 = (fn<<(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)>>(x: (maybe :: V -> V)<exception>){
//   match (x) {
//     ((std/core/types/Nothing() : (maybe :: V -> V)<exception> ) as @pat: ((maybe :: V -> V)<exception>))
//        -> std/core/types/Unit;
//     ((@skip std/core/types/Just(((@skip std/core/exn/Exception((@pat@1: string) : string, (@pat@2: exception-info) : exception-info) : exception ) as exn: exception) : exception) : (maybe :: V -> V)<exception> ) as @pat@0: ((maybe :: V -> V)<exception>))
//        -> (match ((std/core/types/local-get<(maybe :: V -> V)<exception>,(h :: H),(exn :: (E, V) -> V)>(mexn, (std/core/types/@Hnodiv<(h :: H),(maybe :: V -> V)<exception>,(exn :: (E, V) -> V)>)))) {
//         ((std/core/types/Nothing() : (maybe :: V -> V)<exception> ) as @pat@3: ((maybe :: V -> V)<exception>))
//            -> std/core/types/local-set<(maybe :: V -> V)<exception>,(exn :: (E, V) -> V),(h :: H)>(mexn, x);
//         ((@skip std/core/types/Just(((@skip std/core/exn/Exception((@pat@5: string) : string, (@pat@6: exception-info) : exception-info) : exception ) as exnx: exception) : exception) : (maybe :: V -> V)<exception> ) as @pat@4: ((maybe :: V -> V)<exception>))
//            -> (match ((std/core/types/@open<(total :: E),<(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)>,(exn : exception) -> bool,(exn : exception) -> <(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)> bool>((fn(exn@0: exception){
//             (match (exn@0) {
//               ((@skip std/core/exn/Exception((@pat@0@0: string) : string, (@x: exception-info) : exception-info) : exception ) as @pat@7: exception)
//                  -> (match (@x) {
//                   ((std/async/async/Finalize((@pat@0@1: hnd/yield-info) : hnd/yield-info) : exception-info ) as @pat@8: exception-info)
//                      -> std/core/types/True;
//                   (@pat@1@0: exception-info)
//                      -> std/core/types/False;
//                 });
//             });
//           }))(exn))) {
//             ((std/core/types/True() : bool ) as @pat@7@0: bool)
//                -> (match ((std/core/types/@open<(total :: E),<(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)>,(b : bool) -> bool,(b : bool) -> <(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)> bool>((fn(b: bool){
//                 (match (b) {
//                   ((std/core/types/True() : bool ) as @pat@9: bool)
//                      -> std/core/types/False;
//                   ((@skip std/core/types/False() : bool ) as @pat@0@2: bool)
//                      -> std/core/types/True;
//                 });
//               }))((std/core/types/@open<(total :: E),<(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)>,(exn : exception) -> bool,(exn : exception) -> <(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)> bool>((fn(exn@1: exception){
//                 (match (exn@1) {
//                   ((@skip std/core/exn/Exception((@pat@0@3: string) : string, (@x@0: exception-info) : exception-info) : exception ) as @pat@10: exception)
//                      -> (match (@x@0) {
//                       ((std/async/async/Finalize((@pat@0@4: hnd/yield-info) : hnd/yield-info) : exception-info ) as @pat@11: exception-info)
//                          -> std/core/types/True;
//                       (@pat@1@1: exception-info)
//                          -> std/core/types/False;
//                     });
//                 });
//               }))(exnx))))) {
//                 ((std/core/types/True() : bool ) as @pat@9@0: bool)
//                    -> std/core/types/local-set<(maybe :: V -> V)<exception>,(exn :: (E, V) -> V),(h :: H)>(mexn, x);
//                 (@pat@10@0: bool)
//                    -> (match ((std/core/types/@open<(total :: E),<(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)>,(exn : exception) -> bool,(exn : exception) -> <(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)> bool>((fn(exn@2: exception){
//                     (match (exn@2) {
//                       ((@skip std/core/exn/Exception((@pat@0@5: string) : string, (@x@1: exception-info) : exception-info) : exception ) as @pat@12: exception)
//                          -> (match (@x@1) {
//                           ((std/async/async/Cancel() : exception-info ) as @pat@13: exception-info)
//                              -> std/core/types/True;
//                           (@pat@0@6: exception-info)
//                              -> std/core/types/False;
//                         });
//                     });
//                   }))(exnx))) {
//                     ((std/core/types/True() : bool ) as @pat@11@0: bool)
//                        -> (match ((std/core/types/@open<(total :: E),<(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)>,(b : bool) -> bool,(b : bool) -> <(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)> bool>((fn(b@0: bool){
//                         (match (b@0) {
//                           ((std/core/types/True() : bool ) as @pat@14: bool)
//                              -> std/core/types/False;
//                           ((@skip std/core/types/False() : bool ) as @pat@0@7: bool)
//                              -> std/core/types/True;
//                         });
//                       }))((std/core/types/@open<(total :: E),<(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)>,(exn : exception) -> bool,(exn : exception) -> <(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)> bool>((fn(exn@3: exception){
//                         (match (exn@3) {
//                           ((@skip std/core/exn/Exception((@pat@0@8: string) : string, (@x@2: exception-info) : exception-info) : exception ) as @pat@15: exception)
//                              -> (match (@x@2) {
//                               ((std/async/async/Cancel() : exception-info ) as @pat@16: exception-info)
//                                  -> std/core/types/True;
//                               (@pat@0@9: exception-info)
//                                  -> std/core/types/False;
//                             });
//                         });
//                       }))(exn))))) {
//                         ((std/core/types/True() : bool ) as @pat@13@0: bool)
//                            -> std/core/types/local-set<(maybe :: V -> V)<exception>,(exn :: (E, V) -> V),(h :: H)>(mexn, x);
//                         ((@skip std/core/types/False() : bool ) as @pat@14@0: bool)
//                            -> std/core/types/Unit;
//                       });
//                     (@pat@12@0: bool)
//                        -> std/core/types/Unit;
//                   });
//               });
//             (@pat@8@0: bool)
//                -> (match ((std/core/types/@open<(total :: E),<(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)>,(exn : exception) -> bool,(exn : exception) -> <(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)> bool>((fn(exn@4: exception){
//                 (match (exn@4) {
//                   ((@skip std/core/exn/Exception((@pat@0@10: string) : string, (@x@3: exception-info) : exception-info) : exception ) as @pat@17: exception)
//                      -> (match (@x@3) {
//                       ((std/async/async/Cancel() : exception-info ) as @pat@18: exception-info)
//                          -> std/core/types/True;
//                       (@pat@0@11: exception-info)
//                          -> std/core/types/False;
//                     });
//                 });
//               }))(exnx))) {
//                 ((std/core/types/True() : bool ) as @pat@11@0@0: bool)
//                    -> (match ((std/core/types/@open<(total :: E),<(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)>,(b : bool) -> bool,(b : bool) -> <(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)> bool>((fn(b@1: bool){
//                     (match (b@1) {
//                       ((std/core/types/True() : bool ) as @pat@19: bool)
//                          -> std/core/types/False;
//                       ((@skip std/core/types/False() : bool ) as @pat@0@12: bool)
//                          -> std/core/types/True;
//                     });
//                   }))((std/core/types/@open<(total :: E),<(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)>,(exn : exception) -> bool,(exn : exception) -> <(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)> bool>((fn(exn@5: exception){
//                     (match (exn@5) {
//                       ((@skip std/core/exn/Exception((@pat@0@13: string) : string, (@x@4: exception-info) : exception-info) : exception ) as @pat@20: exception)
//                          -> (match (@x@4) {
//                           ((std/async/async/Cancel() : exception-info ) as @pat@21: exception-info)
//                              -> std/core/types/True;
//                           (@pat@0@14: exception-info)
//                              -> std/core/types/False;
//                         });
//                     });
//                   }))(exn))))) {
//                     ((std/core/types/True() : bool ) as @pat@13@0@0: bool)
//                        -> std/core/types/local-set<(maybe :: V -> V)<exception>,(exn :: (E, V) -> V),(h :: H)>(mexn, x);
//                     ((@skip std/core/types/False() : bool ) as @pat@14@0@0: bool)
//                        -> std/core/types/Unit;
//                   });
//                 (@pat@12@0@0: bool)
//                    -> std/core/types/Unit;
//               });
//           });
//       });
//   };
// },Own)
fun @lift-ordered_throw@10773 : forall<h> (mexn : local-var<h,maybe<exception>>, @uniq-xs@10711 : list<maybe<exception>>) -> <local<h>,exn> ()
  = forall<h> fn<<local<h>,exn>>(mexn@1: local-var<h,maybe<exception>>, @uniq-xs@10711: list<maybe<exception>>){
    (match (@uniq-xs@10711) {
      ((std/core/types/Cons((@uniq-x@10714@0: maybe<exception>), (@uniq-xx@10715@0: list<maybe<exception>>)) : list<maybe<exception>> ) as @uniq-pat@10713: (list<maybe<exception>>))
         -> val x@8@12346 : ()
                  = (match (@uniq-x@10714@0) {
                    ((std/core/types/Nothing() : maybe<exception> ) as @pat@1: (maybe<exception>))
                       -> std/core/types/Unit;
                    ((@skip std/core/types/Just(((@skip std/core/exn/Exception((@pat@1@2: string), (@pat@2: exception-info)) : exception ) as exn@6: exception)) : maybe<exception> ) as @pat@0@15: (maybe<exception>))
                       -> val x@9@12349 : maybe<exception>
                                = std/core/types/local-get(mexn@1, std/core/types/@Hnodiv);
                      (match ((std/core/hnd/yielding())) {
                        ((std/core/types/True() : bool ) as @pat@22: bool)
                           -> std/core/hnd/yield-extend((fn<<local<h>,exn>>(@y-x11124@0: maybe<exception>){
                            (std/async/async/@mlift-lift-ordered_throw@10773@11457(@uniq-x@10714@0, exn@6, mexn@1, @y-x11124@0));
                          }));
                        ((@skip std/core/types/False() : bool ) as @pat@0@16: bool)
                           -> std/async/async/@mlift-lift-ordered_throw@10773@11457(@uniq-x@10714@0, exn@6, mexn@1, x@9@12349);
                      });
                  });
        (match ((std/core/hnd/yielding())) {
          ((std/core/types/True() : bool ) as @pat: bool)
             -> std/core/hnd/yield-extend((fn(@c-x11136@0: ()){
              (std/async/async/@mlift-lift-ordered_throw@10773@11458(@uniq-xx@10715@0, mexn@1, @c-x11136@0));
            }));
          ((@skip std/core/types/False() : bool ) as @pat@0: bool)
             -> std/async/async/@lift-ordered_throw@10773(mexn@1, @uniq-xx@10715@0);
        });
      ((@skip std/core/types/Nil() : list<maybe<exception>> ) as @uniq-pat@0@10716: (list<maybe<exception>>))
         -> std/core/types/Unit;
    });
  };
// lifted local: ordered_throw, @spec-x10710
// specialized: std/core/list/foreach, on parameters @uniq-action@10707, using:
// @uniq-action@10707 = (fn<<(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)>>(x: (maybe :: V -> V)<exception>){
//   match (x) {
//     ((std/core/types/Nothing() : (maybe :: V -> V)<exception> ) as @pat: ((maybe :: V -> V)<exception>))
//        -> std/core/types/Unit;
//     ((@skip std/core/types/Just(((@skip std/core/exn/Exception((@pat@1: string) : string, (@pat@2: exception-info) : exception-info) : exception ) as exn: exception) : exception) : (maybe :: V -> V)<exception> ) as @pat@0: ((maybe :: V -> V)<exception>))
//        -> (match ((std/core/types/local-get<(maybe :: V -> V)<exception>,(h :: H),(exn :: (E, V) -> V)>(mexn, (std/core/types/@Hnodiv<(h :: H),(maybe :: V -> V)<exception>,(exn :: (E, V) -> V)>)))) {
//         ((std/core/types/Nothing() : (maybe :: V -> V)<exception> ) as @pat@3: ((maybe :: V -> V)<exception>))
//            -> std/core/types/local-set<(maybe :: V -> V)<exception>,(exn :: (E, V) -> V),(h :: H)>(mexn, x);
//         ((@skip std/core/types/Just(((@skip std/core/exn/Exception((@pat@5: string) : string, (@pat@6: exception-info) : exception-info) : exception ) as exnx: exception) : exception) : (maybe :: V -> V)<exception> ) as @pat@4: ((maybe :: V -> V)<exception>))
//            -> (match ((std/core/types/@open<(total :: E),<(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)>,(exn : exception) -> bool,(exn : exception) -> <(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)> bool>((fn(exn@0: exception){
//             (match (exn@0) {
//               ((@skip std/core/exn/Exception((@pat@0@0: string) : string, (@x: exception-info) : exception-info) : exception ) as @pat@7: exception)
//                  -> (match (@x) {
//                   ((std/async/async/Finalize((@pat@0@1: hnd/yield-info) : hnd/yield-info) : exception-info ) as @pat@8: exception-info)
//                      -> std/core/types/True;
//                   (@pat@1@0: exception-info)
//                      -> std/core/types/False;
//                 });
//             });
//           }))(exn))) {
//             ((std/core/types/True() : bool ) as @pat@7@0: bool)
//                -> (match ((std/core/types/@open<(total :: E),<(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)>,(b : bool) -> bool,(b : bool) -> <(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)> bool>((fn(b: bool){
//                 (match (b) {
//                   ((std/core/types/True() : bool ) as @pat@9: bool)
//                      -> std/core/types/False;
//                   ((@skip std/core/types/False() : bool ) as @pat@0@2: bool)
//                      -> std/core/types/True;
//                 });
//               }))((std/core/types/@open<(total :: E),<(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)>,(exn : exception) -> bool,(exn : exception) -> <(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)> bool>((fn(exn@1: exception){
//                 (match (exn@1) {
//                   ((@skip std/core/exn/Exception((@pat@0@3: string) : string, (@x@0: exception-info) : exception-info) : exception ) as @pat@10: exception)
//                      -> (match (@x@0) {
//                       ((std/async/async/Finalize((@pat@0@4: hnd/yield-info) : hnd/yield-info) : exception-info ) as @pat@11: exception-info)
//                          -> std/core/types/True;
//                       (@pat@1@1: exception-info)
//                          -> std/core/types/False;
//                     });
//                 });
//               }))(exnx))))) {
//                 ((std/core/types/True() : bool ) as @pat@9@0: bool)
//                    -> std/core/types/local-set<(maybe :: V -> V)<exception>,(exn :: (E, V) -> V),(h :: H)>(mexn, x);
//                 (@pat@10@0: bool)
//                    -> (match ((std/core/types/@open<(total :: E),<(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)>,(exn : exception) -> bool,(exn : exception) -> <(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)> bool>((fn(exn@2: exception){
//                     (match (exn@2) {
//                       ((@skip std/core/exn/Exception((@pat@0@5: string) : string, (@x@1: exception-info) : exception-info) : exception ) as @pat@12: exception)
//                          -> (match (@x@1) {
//                           ((std/async/async/Cancel() : exception-info ) as @pat@13: exception-info)
//                              -> std/core/types/True;
//                           (@pat@0@6: exception-info)
//                              -> std/core/types/False;
//                         });
//                     });
//                   }))(exnx))) {
//                     ((std/core/types/True() : bool ) as @pat@11@0: bool)
//                        -> (match ((std/core/types/@open<(total :: E),<(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)>,(b : bool) -> bool,(b : bool) -> <(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)> bool>((fn(b@0: bool){
//                         (match (b@0) {
//                           ((std/core/types/True() : bool ) as @pat@14: bool)
//                              -> std/core/types/False;
//                           ((@skip std/core/types/False() : bool ) as @pat@0@7: bool)
//                              -> std/core/types/True;
//                         });
//                       }))((std/core/types/@open<(total :: E),<(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)>,(exn : exception) -> bool,(exn : exception) -> <(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)> bool>((fn(exn@3: exception){
//                         (match (exn@3) {
//                           ((@skip std/core/exn/Exception((@pat@0@8: string) : string, (@x@2: exception-info) : exception-info) : exception ) as @pat@15: exception)
//                              -> (match (@x@2) {
//                               ((std/async/async/Cancel() : exception-info ) as @pat@16: exception-info)
//                                  -> std/core/types/True;
//                               (@pat@0@9: exception-info)
//                                  -> std/core/types/False;
//                             });
//                         });
//                       }))(exn))))) {
//                         ((std/core/types/True() : bool ) as @pat@13@0: bool)
//                            -> std/core/types/local-set<(maybe :: V -> V)<exception>,(exn :: (E, V) -> V),(h :: H)>(mexn, x);
//                         ((@skip std/core/types/False() : bool ) as @pat@14@0: bool)
//                            -> std/core/types/Unit;
//                       });
//                     (@pat@12@0: bool)
//                        -> std/core/types/Unit;
//                   });
//               });
//             (@pat@8@0: bool)
//                -> (match ((std/core/types/@open<(total :: E),<(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)>,(exn : exception) -> bool,(exn : exception) -> <(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)> bool>((fn(exn@4: exception){
//                 (match (exn@4) {
//                   ((@skip std/core/exn/Exception((@pat@0@10: string) : string, (@x@3: exception-info) : exception-info) : exception ) as @pat@17: exception)
//                      -> (match (@x@3) {
//                       ((std/async/async/Cancel() : exception-info ) as @pat@18: exception-info)
//                          -> std/core/types/True;
//                       (@pat@0@11: exception-info)
//                          -> std/core/types/False;
//                     });
//                 });
//               }))(exnx))) {
//                 ((std/core/types/True() : bool ) as @pat@11@0@0: bool)
//                    -> (match ((std/core/types/@open<(total :: E),<(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)>,(b : bool) -> bool,(b : bool) -> <(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)> bool>((fn(b@1: bool){
//                     (match (b@1) {
//                       ((std/core/types/True() : bool ) as @pat@19: bool)
//                          -> std/core/types/False;
//                       ((@skip std/core/types/False() : bool ) as @pat@0@12: bool)
//                          -> std/core/types/True;
//                     });
//                   }))((std/core/types/@open<(total :: E),<(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)>,(exn : exception) -> bool,(exn : exception) -> <(local :: H -> X)<(h :: H)>,(exn :: (E, V) -> V)> bool>((fn(exn@5: exception){
//                     (match (exn@5) {
//                       ((@skip std/core/exn/Exception((@pat@0@13: string) : string, (@x@4: exception-info) : exception-info) : exception ) as @pat@20: exception)
//                          -> (match (@x@4) {
//                           ((std/async/async/Cancel() : exception-info ) as @pat@21: exception-info)
//                              -> std/core/types/True;
//                           (@pat@0@14: exception-info)
//                              -> std/core/types/False;
//                         });
//                     });
//                   }))(exn))))) {
//                     ((std/core/types/True() : bool ) as @pat@13@0@0: bool)
//                        -> std/core/types/local-set<(maybe :: V -> V)<exception>,(exn :: (E, V) -> V),(h :: H)>(mexn, x);
//                     ((@skip std/core/types/False() : bool ) as @pat@14@0@0: bool)
//                        -> std/core/types/Unit;
//                   });
//                 (@pat@12@0@0: bool)
//                    -> std/core/types/Unit;
//               });
//           });
//       });
//   };
// },Own)
fun @lift-ordered_throw@10772 : forall<h> (mexn : local-var<h,maybe<exception>>, @uniq-xs@10706 : list<maybe<exception>>) -> <local<h>,exn> ()
  = forall<h> fn<<local<h>,exn>>(mexn: local-var<h,maybe<exception>>, @uniq-xs@10706: list<maybe<exception>>){
    (match (@uniq-xs@10706) {
      ((std/core/types/Nil() : list<maybe<exception>> ) as @uniq-pat@0@10708: (list<maybe<exception>>))
         -> std/core/types/Unit;
      (@uniq-pat@10709: (list<maybe<exception>>))
         -> std/async/async/@lift-ordered_throw@10773(mexn, @uniq-xs@10706);
    });
  };
// monadic lift
fun @mlift-ordered_throw@11459 : forall<h> (@y-x11142 : maybe<exception>) -> <local<h>,exn> ()
  = forall<h> fn<<local<h>,exn>>(@y-x11142: maybe<exception>){
    (match (@y-x11142) {
      ((std/core/types/Just(((@skip std/core/exn/Exception((@pat@16@0: string), (@pat@17@0: exception-info)) : exception ) as exn@0@0: exception)) : maybe<exception> ) as @pat@15@0: (maybe<exception>))
         -> std/async/async/rethrow(exn@0@0);
      ((@skip std/core/types/Nothing() : maybe<exception> ) as @pat@18@0: (maybe<exception>))
         -> std/core/types/Unit;
    });
  };
// monadic lift
fun @mlift-ordered_throw@11460 : forall<h> (mexn : local-var<h,maybe<exception>>, wild_ : ()) -> <local<h>,exn> ()
  = forall<h> fn<<local<h>,exn>>(mexn: local-var<h,maybe<exception>>, wild_: ()){
    val x@12351 : maybe<exception>
      = std/core/types/local-get(mexn, std/core/types/@Hnodiv);
    val next@12352 : (maybe<exception>) -> <local<h>,exn> ()
      = fn<<local<h>,exn>>(@y-x11142: maybe<exception>){
        (match (@y-x11142) {
          ((std/core/types/Just(((@skip std/core/exn/Exception((@pat@16@0: string), (@pat@17@0: exception-info)) : exception ) as exn@0@0: exception)) : maybe<exception> ) as @pat@15@0: (maybe<exception>))
             -> std/async/async/rethrow(exn@0@0);
          ((@skip std/core/types/Nothing() : maybe<exception> ) as @pat@18@0: (maybe<exception>))
             -> std/core/types/Unit;
        });
      };
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-extend(next@12352);
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> next@12352(x@12351);
    });
  };
fun ordered_throw : (xs : list<maybe<exception>>) -> exn ()
  = fn<exn>(xs: list<maybe<exception>>){
    (forall<h> fn<<local<h>,exn>>(){
      val loc : local-var<h,maybe<exception>>
        = std/core/types/local-new(std/core/types/Nothing);
      val x@12356 : ()
        = std/async/async/@lift-ordered_throw@10772(loc, xs);
      val res : ()
        = (match ((std/core/hnd/yielding())) {
          ((std/core/types/True() : bool ) as @pat: bool)
             -> std/core/hnd/yield-extend((fn<<local<h>,exn>>(wild_: ()){
              (std/async/async/@mlift-ordered_throw@11460(loc, wild_));
            }));
          ((@skip std/core/types/False() : bool ) as @pat@0: bool)
             -> std/async/async/@mlift-ordered_throw@11460(loc, x@12356);
        });
      std/core/hnd/prompt-local-var(loc, res);
    })();
  };
// monadic lift
fun two/@mlift-interleaved@11461 : forall<a,b,e> (@y-x11153 : a, @y-x11154 : b) -> <exn,async|e> (a, b)
  = forall<a,b,e> fn<<exn,async|e>>(@y-x11153: a, @y-x11154: b){
    std/core/types/Tuple2(@y-x11153, @y-x11154);
  };
// monadic lift
fun two/@mlift-interleaved@11462 : forall<a,b,e> (rb : error<b>, @y-x11153 : a) -> <exn,async|e> (a, b)
  = forall<a,b,e> fn<<exn,async|e>>(rb: error<b>, @y-x11153: a){
    val i@12360 : hnd/ev-index
      = std/core/hnd/@evv-index(std/core/exn/exn/@tag);
    val w : hnd/evv<<exn,async|e>>
      = std/core/hnd/evv-swap-create1(i@12360);
    val y : b
      = std/core/exn/untry(rb);
    val _ : ()
      = std/core/hnd/evv-set(w);
    val x@12358 : b
      = (match ((std/core/hnd/yielding())) {
        ((std/core/types/True() : bool ) as @pat@1: bool)
           -> std/core/hnd/yield-cont((forall<c> fn<<exn,async|e>>(cont: (c) -> <exn,async|e> b, res: c){
            std/core/hnd/open-at1(i@12360, cont, res);
          }));
        ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
           -> y;
      });
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-extend((fn<<exn,async|e>>(@y-x11154: b){
          (std/core/types/Tuple2(@y-x11153, @y-x11154));
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> std/core/types/Tuple2(@y-x11153, x@12358);
    });
  };
// monadic lift
fun two/@mlift-interleaved@11463 : forall<a,b,e> (ra : error<a>, rb : error<b>, wild_ : ()) -> <exn,async|e> (a, b)
  = forall<a,b,e> fn<<exn,async|e>>(ra: error<a>, rb: error<b>, wild_: ()){
    val i@12367 : hnd/ev-index
      = std/core/hnd/@evv-index(std/core/exn/exn/@tag);
    val w : hnd/evv<<exn,async|e>>
      = std/core/hnd/evv-swap-create1(i@12367);
    val y : a
      = std/core/exn/untry(ra);
    val _ : ()
      = std/core/hnd/evv-set(w);
    val x@12365 : a
      = (match ((std/core/hnd/yielding())) {
        ((std/core/types/True() : bool ) as @pat@1: bool)
           -> std/core/hnd/yield-cont((forall<c> fn<<exn,async|e>>(cont: (c) -> <exn,async|e> a, res: c){
            std/core/hnd/open-at1(i@12367, cont, res);
          }));
        ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
           -> y;
      });
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-extend((fn<<exn,async|e>>(@y-x11153: a){
          (std/async/async/two/@mlift-interleaved@11462(rb, @y-x11153));
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> std/async/async/two/@mlift-interleaved@11462(rb, x@12365);
    });
  };
// monadic lift
fun two/@mlift-interleaved@11464 : forall<a,e> (action1 : () -> <async-exn|e> a, @y-x11147 : hnd/ev-index) -> <exn,exn,async|e> a
  = forall<a,e> fn<<exn,exn,async|e>>(action1: () -> <async-exn|e> a, @y-x11147: hnd/ev-index){
    val w0 : hnd/evv<hnd/_e2>
      = std/core/hnd/evv-swap-delete(@y-x11147, std/core/types/True);
    val x : a
      = action1();
    val _ : ()
      = std/core/hnd/evv-set(w0);
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-cont((forall<b> fn<<exn,exn,async|e>>(cont: (b) -> <exn,exn,async|e> a, res: b){
          std/core/hnd/mask-at1(@y-x11147, std/core/types/True, cont, res);
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> x;
    });
  };
// monadic lift
fun two/@mlift-interleaved@11465 : forall<a,e> (action2 : () -> <async-exn|e> a, @y-x11149 : hnd/ev-index) -> <exn,exn,async|e> a
  = forall<a,e> fn<<exn,exn,async|e>>(action2: () -> <async-exn|e> a, @y-x11149: hnd/ev-index){
    val w0 : hnd/evv<hnd/_e2>
      = std/core/hnd/evv-swap-delete(@y-x11149, std/core/types/True);
    val x : a
      = action2();
    val _ : ()
      = std/core/hnd/evv-set(w0);
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-cont((forall<b> fn<<exn,exn,async|e>>(cont: (b) -> <exn,exn,async|e> a, res: b){
          std/core/hnd/mask-at1(@y-x11149, std/core/types/True, cont, res);
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> x;
    });
  };
// monadic lift
fun two/@mlift-interleaved@11466 : forall<a,b,e> (@y-x11151 : (error<a>, error<b>)) -> <async,exn|e> (a, b)
  = forall<a,b,e> fn<<async,exn|e>>(@y-x11151: (error<a>, error<b>)){
    (match (@y-x11151) {
      ((@skip std/core/types/Tuple2((ra: error<a>), (rb: error<b>)) : (error<a>, error<b>) ) as @pat: (error<a>, error<b>))
         -> val w : hnd/evv<<exn,async|e>>
              = std/core/hnd/evv-swap-create0();
            val keep : ()
              = std/core/hnd/evv-set(w);
            val w@0 : hnd/evv<<exn,async|e>>
              = std/core/hnd/evv-swap-create0();
            val keep@0 : ()
              = std/core/hnd/evv-set(w@0);
            val i@12382 : (hnd/ev-index == 1 ssize_t)
              = std/core/hnd/@evv-index(std/core/exn/exn/@tag);
            val w@1 : hnd/evv<<exn,async|e>>
              = std/core/hnd/evv-swap-create1(i@12382);
            val y : ()
              = std/async/async/ordered_throw((std/core/types/Cons((match (ra) {
                  ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@0: string), (@pat@1: exception-info)) : exception ) as exn: exception)) : error<a> ) as @pat@0: (error<a>))
                     -> std/core/types/Just(exn);
                  (@pat@2: (error<a>))
                     -> std/core/types/Nothing;
                }), (std/core/types/Cons((match (rb) {
                    ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@1: string), (@pat@1@0: exception-info)) : exception ) as exn@0: exception)) : error<b> ) as @pat@3: (error<b>))
                       -> std/core/types/Just(exn@0);
                    (@pat@2@0: (error<b>))
                       -> std/core/types/Nothing;
                  }), std/core/types/Nil)))));
            val _ : ()
              = std/core/hnd/evv-set(w@1);
            val x@1@12380 : ()
              = (match ((std/core/hnd/yielding())) {
                ((std/core/types/True() : bool ) as @pat@5: bool)
                   -> std/core/hnd/yield-cont((forall<c> fn<<exn,async|e>>(cont: (c) -> <exn,async|e> (), res: c){
                    std/core/hnd/open-at1(i@12382, cont, res);
                  }));
                ((@skip std/core/types/False() : bool ) as @pat@0@3: bool)
                   -> y;
              });
        (match ((std/core/hnd/yielding())) {
          ((std/core/types/True() : bool ) as @pat@4: bool)
             -> std/core/hnd/yield-extend((fn<<exn,async|e>>(wild_: ()){
              (std/async/async/two/@mlift-interleaved@11463(ra, rb, wild_));
            }));
          ((@skip std/core/types/False() : bool ) as @pat@0@2: bool)
             -> std/async/async/two/@mlift-interleaved@11463(ra, rb, x@1@12380);
        });
    });
  };
// Interleave two actions around their asynchronous operations.
pub fun two/interleaved : forall<a,b,e> (action1 : () -> <async-exn|e> a, action2 : () -> <async-exn|e> b) -> <async-exn|e> (a, b)
  = forall<a,b,e> fn<<async-exn|e>>(action1: () -> <async-exn|e> a, action2: () -> <async-exn|e> b){
    val x@12385 : (error<a>, error<b>)
          = std/async/async/interleavedx((fn<<async-exn,exn|e>>(){
              val x@0@12388 : hnd/ev-index
                    = (std/core/hnd/@evv-index(std/core/exn/exn/@tag));
              (match ((std/core/hnd/yielding())) {
                ((std/core/types/True() : bool ) as @pat@1: bool)
                   -> std/core/hnd/yield-extend((fn<<exn,exn,async|e>>(@y-x11147: (hnd/ev-index == 1 ssize_t)){
                    (std/async/async/two/@mlift-interleaved@11464(action1, @y-x11147));
                  }));
                ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
                   -> std/async/async/two/@mlift-interleaved@11464(action1, x@0@12388);
              });
            }), (fn<<async-exn,exn|e>>(){
              val x@1@12390 : hnd/ev-index
                    = (std/core/hnd/@evv-index(std/core/exn/exn/@tag));
              (match ((std/core/hnd/yielding())) {
                ((std/core/types/True() : bool ) as @pat@2: bool)
                   -> std/core/hnd/yield-extend((fn<<exn,exn,async|e>>(@y-x11149: (hnd/ev-index == 1 ssize_t)){
                    (std/async/async/two/@mlift-interleaved@11465(action2, @y-x11149));
                  }));
                ((@skip std/core/types/False() : bool ) as @pat@0@1: bool)
                   -> std/async/async/two/@mlift-interleaved@11465(action2, x@1@12390);
              });
            }));
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-extend((fn<<async,exn|e>>(@y-x11151: (error<a>, error<b>)){
          (std/async/async/two/@mlift-interleaved@11466(@y-x11151));
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> (match (x@12385) {
          ((@skip std/core/types/Tuple2((ra: error<a>), (rb: error<b>)) : (error<a>, error<b>) ) as @pat@3: (error<a>, error<b>))
             -> val w : hnd/evv<<exn,async|e>>
                  = std/core/hnd/evv-swap-create0();
                val keep : ()
                  = std/core/hnd/evv-set(w);
                val w@0 : hnd/evv<<exn,async|e>>
                  = std/core/hnd/evv-swap-create0();
                val keep@0 : ()
                  = std/core/hnd/evv-set(w@0);
                val i@12399 : (hnd/ev-index == 1 ssize_t)
                  = std/core/hnd/@evv-index(std/core/exn/exn/@tag);
                val w@1 : hnd/evv<<exn,async|e>>
                  = std/core/hnd/evv-swap-create1(i@12399);
                val y : ()
                  = std/async/async/ordered_throw((std/core/types/Cons((match (ra) {
                      ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@0@0: string), (@pat@1@0: exception-info)) : exception ) as exn: exception)) : error<a> ) as @pat@0@2: (error<a>))
                         -> std/core/types/Just(exn);
                      (@pat@2@0: (error<a>))
                         -> std/core/types/Nothing;
                    }), (std/core/types/Cons((match (rb) {
                        ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@1@0: string), (@pat@1@0@0: exception-info)) : exception ) as exn@0: exception)) : error<b> ) as @pat@3@0: (error<b>))
                           -> std/core/types/Just(exn@0);
                        (@pat@2@0@0: (error<b>))
                           -> std/core/types/Nothing;
                      }), std/core/types/Nil)))));
                val _ : ()
                  = std/core/hnd/evv-set(w@1);
                val x@4@12396 : ()
                  = (match ((std/core/hnd/yielding())) {
                    ((std/core/types/True() : bool ) as @pat@5: bool)
                       -> std/core/hnd/yield-cont((forall<c> fn<<exn,async|e>>(cont: (c) -> <exn,async|e> (), res: c){
                        std/core/hnd/open-at1(i@12399, cont, res);
                      }));
                    ((@skip std/core/types/False() : bool ) as @pat@0@4: bool)
                       -> y;
                  });
            (match ((std/core/hnd/yielding())) {
              ((std/core/types/True() : bool ) as @pat@4: bool)
                 -> std/core/hnd/yield-extend((fn<<exn,async|e>>(wild_: ()){
                  (std/async/async/two/@mlift-interleaved@11463(ra, rb, wild_));
                }));
              ((@skip std/core/types/False() : bool ) as @pat@0@3: bool)
                 -> val i@0@12405 : (hnd/ev-index == 1 ssize_t)
                      = std/core/hnd/@evv-index(std/core/exn/exn/@tag);
                    val w@2 : hnd/evv<<exn,async|e>>
                      = std/core/hnd/evv-swap-create1(i@0@12405);
                    val y@0 : a
                      = std/core/exn/untry(ra);
                    val _ : ()
                      = std/core/hnd/evv-set(w@2);
                    val x@6@12402 : a
                      = (match ((std/core/hnd/yielding())) {
                        ((std/core/types/True() : bool ) as @pat@7: bool)
                           -> std/core/hnd/yield-cont((forall<c> fn<<exn,async|e>>(cont@0: (c) -> <exn,async|e> a, res@0: c){
                            std/core/hnd/open-at1(i@0@12405, cont@0, res@0);
                          }));
                        ((@skip std/core/types/False() : bool ) as @pat@0@6: bool)
                           -> y@0;
                      });
                (match ((std/core/hnd/yielding())) {
                  ((std/core/types/True() : bool ) as @pat@6: bool)
                     -> std/core/hnd/yield-extend((fn<<exn,async|e>>(@y-x11153: a){
                      (std/async/async/two/@mlift-interleaved@11462(rb, @y-x11153));
                    }));
                  ((@skip std/core/types/False() : bool ) as @pat@0@5: bool)
                     -> val i@1@12411 : (hnd/ev-index == 1 ssize_t)
                          = std/core/hnd/@evv-index(std/core/exn/exn/@tag);
                        val w@3 : hnd/evv<<exn,async|e>>
                          = std/core/hnd/evv-swap-create1(i@1@12411);
                        val y@1 : b
                          = std/core/exn/untry(rb);
                        val _ : ()
                          = std/core/hnd/evv-set(w@3);
                        val x@8@12408 : b
                          = (match ((std/core/hnd/yielding())) {
                            ((std/core/types/True() : bool ) as @pat@9: bool)
                               -> std/core/hnd/yield-cont((forall<c> fn<<exn,async|e>>(cont@1: (c) -> <exn,async|e> b, res@1: c){
                                std/core/hnd/open-at1(i@1@12411, cont@1, res@1);
                              }));
                            ((@skip std/core/types/False() : bool ) as @pat@0@8: bool)
                               -> y@1;
                          });
                    (match ((std/core/hnd/yielding())) {
                      ((std/core/types/True() : bool ) as @pat@8: bool)
                         -> std/core/hnd/yield-extend((fn<<exn,async|e>>(@y-x11154: b){
                          (std/core/types/Tuple2(x@6@12402, @y-x11154));
                        }));
                      ((@skip std/core/types/False() : bool ) as @pat@0@7: bool)
                         -> std/core/types/Tuple2(x@6@12402, x@8@12408);
                    });
                });
            });
        });
    });
  };
fun io-noexn : forall<a> (f : () -> io-noexn a) -> io a
  = forall<a> fn<io>(f: () -> io-noexn a){
    std/core/hnd/@open-none0(f);
  };
// lifted local: @lift-show@10774, show, @spec-x10730
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10725, using:
// @uniq-f@10725 = (std/core/int/show,Own)
fun @trmc-lift-show@10775 : (@uniq-xs@10724 : list<int>, @acc : ctx<list<string>>) -> list<string>
  = fn(@uniq-xs@10724: list<int>, @acc: ctx<list<string>>){
    match (@uniq-xs@10724) {
      ((std/core/types/Cons((@uniq-x@10727: int), (@uniq-xx@10728: list<int>)) : list<int> ) as @uniq-pat@10726: (list<int>))
         -> val @trmc-x10834 : string
              = std/core/int/show(@uniq-x@10727);
            val @trmc-x10835 : list<string>
              = std/core/types/@cctx-hole-create();
            val @trmc-x10836 : list<string>
              = std/core/types/Cons(@trmc-x10834, @trmc-x10835);
        std/async/async/@trmc-lift-show@10775(@uniq-xx@10728, (std/core/types/@cctx-extend(@acc, @trmc-x10836, (std/core/types/@field-addr-of(@trmc-x10836, "(\x22std/core/types\x22,\x22\x22,\x22Cons\x22)", "(\x22\x22,\x22\x22,\x22tail\x22)")))));
      ((@skip std/core/types/Nil() : list<int> ) as @uniq-pat@0@10729: (list<int>))
         -> std/core/types/cctx/((++.))(@acc, std/core/types/Nil);
    };
  };
// lifted local: @lift-show@10774, show, @spec-x10730
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10725, using:
// @uniq-f@10725 = (std/core/int/show,Own)
fun @lift-show@10775 : (@uniq-xs@10724 : list<int>) -> list<string>
  = fn(@uniq-xs@10724@0: list<int>){
    std/async/async/@trmc-lift-show@10775(@uniq-xs@10724@0, (std/core/types/cctx/empty()));
  };
// lifted local: show, @spec-x10723
// specialized: std/core/list/map, on parameters @uniq-f@10720, using:
// @uniq-f@10720 = (std/core/int/show,Own)
fun @lift-show@10774 : (@uniq-xs@10719 : list<int>) -> list<string>
  = fn(@uniq-xs@10719: list<int>){
    match (@uniq-xs@10719) {
      ((std/core/types/Nil() : list<int> ) as @uniq-pat@0@10721: (list<int>))
         -> std/core/types/Nil;
      (@uniq-pat@10722: (list<int>))
         -> std/async/async/@trmc-lift-show@10775(@uniq-xs@10719, (std/core/types/cctx/empty()));
    };
  };
fun show : (s : scope) -> string
  = fn(s: scope){
    match (s) {
      ((@skip std/async/async/Scope((ids: list<int>)) : scope ) as @pat: scope)
         -> val xs@10169 : list<string>
                  = std/async/async/@lift-show@10774(ids);
        (match (xs@10169) {
          ((std/core/types/Nil() : list<string> ) as @pat@0: (list<string>))
             -> "";
          ((@skip std/core/types/Cons((x: string), ((std/core/types/Nil() : list<string> ) as @pat@1: list<string>)) : list<string> ) as @pat@0@0: (list<string>))
             -> x;
          ((std/core/types/Cons((x@0: string), ((std/core/types/Cons((y: string), ((std/core/types/Nil() : list<string> ) as @pat@4: list<string>)) : list<string> ) as @pat@3: list<string>)) : list<string> ) as @pat@2: (list<string>))
             | std/core/string/(==)("-", "") -> std/core/types/(++)(x@0, y);
          (@pat@5: (list<string>))
             -> std/core/string/vectorsep/join((std/core/vector/unvlist(xs@10169)), "-");
        });
    };
  };
fun trace-channel-io : forall<a> (msg : string, ch : channel<a>) -> io-noexn ()
  = forall<a> fn<io-noexn>(msg: string, ch: channel<a>){
    val msgx : string
          = std/core/types/(++)(msg, (std/core/types/(++)(": id=", (std/core/int/show((match (ch) {
                ((@skip std/async/async/Channel((@x: int), (@pat@0: ref<global,channel-state<a>>)) : channel<a> ) as @pat: (channel<a>))
                   -> @x;
              }))))));
    (match ((std/core/types/ref/(!)((match (ch) {
        ((@skip std/async/async/Channel((@pat@0@0: int), (@x@0: ref<global,channel-state<a>>)) : channel<a> ) as @pat@1: (channel<a>))
           -> @x@0;
      }), std/core/types/@Hdiv))) {
      ((std/async/async/Empty() : channel-state<a> ) as @pat@2: (channel-state<a>))
         -> val message@10173 : string
                  = std/core/types/(++)(msgx, ", empty");
        (match ((std/core/types/ref/(!)(std/core/debug/trace-enabled, std/core/types/@Hnodiv))) {
          ((std/core/types/True() : bool ) as @pat@3: bool)
             -> std/core/debug/xtrace(message@10173);
          ((@skip std/core/types/False() : bool ) as @pat@0@1: bool)
             -> std/core/types/Unit;
        });
      ((std/async/async/Values((v: a), (vs: list<a>)) : channel-state<a> ) as @pat@0@2: (channel-state<a>))
         -> val y@10177 : int
              = (match (vs) {
                ((std/core/types/Nil() : list<a> ) as @pat@1@0: (list<a>))
                   -> 0;
                (@pat@5: (list<a>))
                   -> std/core/list/@unroll-lift-length@5730@10000(vs, 0);
              });
            val message@0@10174 : string
              = std/core/types/(++)(msgx, (std/core/types/(++)(", full: ", (std/core/types/(++)((std/core/int/show((std/core/int/int-add(1, y@10177)))), ": ")))));
        (match ((std/core/types/ref/(!)(std/core/debug/trace-enabled, std/core/types/@Hnodiv))) {
          ((std/core/types/True() : bool ) as @pat@4: bool)
             -> std/core/debug/xtrace-any(message@0@10174, v);
          ((@skip std/core/types/False() : bool ) as @pat@0@3: bool)
             -> std/core/types/Unit;
        });
      ((@skip std/async/async/Waiting((@pat@2@0: (a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()), (ls: list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>)) : channel-state<a> ) as @pat@1@1: (channel-state<a>))
         -> val y@0@10181 : int
              = (match (ls) {
                ((std/core/types/Nil() : list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()> ) as @pat@1@2: (list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>))
                   -> 0;
                (@pat@7: (list<(a) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>))
                   -> std/core/list/@unroll-lift-length@5730@10000(ls, 0);
              });
            val message@1@10179 : string
              = std/core/types/(++)(msgx, (std/core/types/(++)(", listeners: ", (std/core/int/show((std/core/int/int-add(1, y@0@10181)))))));
        (match ((std/core/types/ref/(!)(std/core/debug/trace-enabled, std/core/types/@Hnodiv))) {
          ((std/core/types/True() : bool ) as @pat@6: bool)
             -> std/core/debug/xtrace(message@1@10179);
          ((@skip std/core/types/False() : bool ) as @pat@0@4: bool)
             -> std/core/types/Unit;
        });
    });
  };
fun trace-channel : forall<a> (msg : string, ch : channel<a>) -> <async,ndet> ()
  = forall<a> fn<<async,ndet>>(msg: string, ch: channel<a>){
    val ev@12417 : hnd/ev<async>
          = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
    (match (ev@12417) {
      ((@skip std/core/hnd/Ev<e,b>((@pat@0: hnd/htag<async>), (m: hnd/marker<e,b>), (h: async<e,b>), (@pat@1: hnd/evv<e>)) : hnd/ev<async> ) as @pat: (hnd/ev<async>))
         -> (match (h) {
          ((@skip std/async/async/@Hnd-async((@pat@0@0: int), (@ctl-async-iox: forall<c> hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) c,c,async,e,b>), (@pat@1@0: hnd/clause1<scope,(),async,e,b>), (@pat@2@0: forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>
   >)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool),error<c>,async,e,b>), (@pat@3: (forall<c> hnd/clause1<((await-setup<c> == 4 (cb : (error<c>, bool) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<
   global>,write<global>,alloc<global>>)>)>) ()) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) maybe<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()>), scope, bool, (error<c>) -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()),(),async
   ,e,b>))) : async<e,b> ) as @pat@2: (async<e,b>))
             -> (match (@ctl-async-iox) {
              ((@skip std/core/hnd/Clause1((f: (hnd/marker<e,b>, hnd/ev<async>, () -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) ()) -> e ())) : hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>) (),(),async,e,b> ) as @pat@2@1: (hnd/clause1<() -> (io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st
   <global> == 1 <read<global>,write<global>,alloc<global>>)>)>) (),(),async,e,b>))
                 -> f(m, ev@12417, (fn<(io-noexn == 3 <div,(io-total == 2 <ndet,console/console,net,fsys,ui,(st<global> == 1 <read<global>,write<global>,alloc<global>>)>)>)>(){
                    (std/async/async/trace-channel-io(msg, ch));
                  }));
            });
        });
    });
  };
extern unsafe-no-ndet-div-cast : forall<a,e> (() -> <ndet,div|e> a) -> (() -> e a) = inline "#1";
extern inject-effects : forall<a,b,e> (() -> e a) -> (() -> <strands<a>,ndet,div|e> a) = inline "#1";
extern interject-async : forall<a,e> (action : () -> <async|e> a) -> (() -> <async,async|e> a) = inline "#1";
module async
import std/core/types = std/core/types pub = "";
import std/core/hnd = std/core/hnd pub = "";
import std/core/exn = std/core/exn pub = "";
import std/core/bool = std/core/bool pub = "";
import std/core/order = std/core/order pub = "";
import std/core/char = std/core/char pub = "";
import std/core/int = std/core/int pub = "";
import std/core/vector = std/core/vector pub = "";
import std/core/string = std/core/string pub = "";
import std/core/sslice = std/core/sslice pub = "";
import std/core/list = std/core/list pub = "";
import std/core/maybe = std/core/maybe pub = "";
import std/core/maybe2 = std/core/maybe2 pub = "";
import std/core/either = std/core/either pub = "";
import std/core/tuple = std/core/tuple pub = "";
import std/core/lazy = std/core/lazy pub = "";
import std/core/show = std/core/show pub = "";
import std/core/debug = std/core/debug pub = "";
import std/core/delayed = std/core/delayed pub = "";
import std/core/console = std/core/console pub = "";
import std/num/ddouble = std/num/ddouble pub = "";
import std/num/float64 = std/num/float64 pub = "";
import std/time/duration = std/time/duration pub = "";
import std/time/timestamp = std/time/timestamp pub = "";
import std/core = std/core = "";
pub import std/async/async = std/async/async = "";
pub import std/async/timer = std/async/timer = "";
module std/jsextern
import std/num/ddouble = std/num/ddouble pub = "";
import std/num/float64 = std/num/float64 pub = "";
import std/time/duration = std/time/duration pub = "";
import std/time/timestamp = std/time/timestamp pub = "";
import std/core/types = std/core/types pub = "";
import std/core/hnd = std/core/hnd pub = "";
import std/core/exn = std/core/exn pub = "";
import std/core/bool = std/core/bool pub = "";
import std/core/order = std/core/order pub = "";
import std/core/char = std/core/char pub = "";
import std/core/int = std/core/int pub = "";
import std/core/vector = std/core/vector pub = "";
import std/core/string = std/core/string pub = "";
import std/core/sslice = std/core/sslice pub = "";
import std/core/list = std/core/list pub = "";
import std/core/maybe = std/core/maybe pub = "";
import std/core/maybe2 = std/core/maybe2 pub = "";
import std/core/either = std/core/either pub = "";
import std/core/tuple = std/core/tuple pub = "";
import std/core/lazy = std/core/lazy pub = "";
import std/core/show = std/core/show pub = "";
import std/core/debug = std/core/debug pub = "";
import std/core/delayed = std/core/delayed pub = "";
import std/core/console = std/core/console pub = "";
import std/async/async = std/async/async pub = "";
import std/async/timer = std/async/timer pub = "";
import std/core = std/core = "";
pub import async = async = "";
// A type alias for asynchronous operations that can raise exceptions non-deterministically.
// This is common for almost all `:async` operations since `cancel` and `timeout` can
// cancel operations non-deterministically which raises the `Cancel` exception and cancels
// outstanding asynchronous requests.
local alias std/async/async/asyncx :: E = <(std/async/async/async :: (E, V) -> V),(exn :: (E, V) -> V),(ndet :: X)> = 1;
// The `:io-noexn` effect is used for functions that perform arbitrary I/O operations, but raise no exceptions
local alias io-noexn :: E = <(div :: X),((io-total :: E) == 2 <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)>)> = 3;
// The `:io-total` effect is used for functions that perform arbitrary I/O operations, but are terminating without raising exceptions.
local alias io-total :: E = <(ndet :: X),(console/console :: X),(net :: X),(fsys :: X),(ui :: X),((st :: H -> E)<(global :: H)> == 1 <(read :: H -> X)<(global :: H)>,(write :: H -> X)<(global :: H)>,(alloc :: H -> X)<(global :: H)>>)> = 2;
pub value{0,1,8} type jsobject[14,1,15,16] <a> :: V -> V {
  pub con Jsobject[14,12,14,19](internal: any){0,1,8} : forall<a> (internal : any) -> (jsobject :: V -> V)<a> = 1;
};
// A marker function that t is a subtype of s
pub alias is-subtype<a,b> :: (V, V) -> V = ((jsobject :: V -> V)<a>, (jsobject :: V -> V)<b>) -> bool = 1;
pub value{0,1,8} type jsarray[17,1,18,16] <a> :: V -> V {
  pub con Jsarray[17,12,17,18](internal: any){0,1,8} : forall<a> (internal : any) -> (jsarray :: V -> V)<a> = 1;
};
pub value{0,1,8} type jspromise[392,1,393,16] <a> :: V -> V {
  pub con Jspromise[392,12,392,20](internal: any){0,1,8} : forall<a> (internal : any) -> (jspromise :: V -> V)<a> = 1;
};
pub extend type exception-info[395,1,396,39] {
  pub con JSError[396,11,396,17](error: (jsobject :: V -> V)<any>){0,2,8} : (error : (jsobject :: V -> V)<any>) -> exception-info = 1;
};
// Automatically generated. Retrieves the `internal` constructor field of the `:jsobject` type.
pub fun jsobject/internal : forall<a> (^ jsobject : jsobject<a>) -> any
  = forall<a> fn(jsobject: jsobject<a>){
    (match (jsobject) {
      ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
         -> @x;
    });
  };
pub fun jsobject/@copy : forall<a> (@this : jsobject<a>, internal : ? any) -> jsobject<a>
  = forall<a> fn(@this: jsobject<a>, internal: ? any){
    std/jsextern/Jsobject((match (internal) {
      ((std/core/types/@Optional((@uniq-internal@674: any)) : ? any ) as @pat: ? any)
         -> @uniq-internal@674;
      ((@skip std/core/types/@None() : ? any ) as @pat@0: ? any)
         -> (match (@this) {
          ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat@1: (jsobject<a>))
             -> @x;
        });
    }));
  };
// Automatically generated. Retrieves the `internal` constructor field of the `:jsarray` type.
pub fun jsarray/internal : forall<a> (^ jsarray : jsarray<a>) -> any
  = forall<a> fn(jsarray: jsarray<a>){
    (match (jsarray) {
      ((@skip std/jsextern/Jsarray((@x: any)) : jsarray<a> ) as @pat: (jsarray<a>))
         -> @x;
    });
  };
pub fun jsarray/@copy : forall<a> (@this : jsarray<a>, internal : ? any) -> jsarray<a>
  = forall<a> fn(@this: jsarray<a>, internal: ? any){
    std/jsextern/Jsarray((match (internal) {
      ((std/core/types/@Optional((@uniq-internal@724: any)) : ? any ) as @pat: ? any)
         -> @uniq-internal@724;
      ((@skip std/core/types/@None() : ? any ) as @pat@0: ? any)
         -> (match (@this) {
          ((@skip std/jsextern/Jsarray((@x: any)) : jsarray<a> ) as @pat@1: (jsarray<a>))
             -> @x;
        });
    }));
  };
// String fields
pub fun ext/get-mstring : (a : any, key : string) -> maybe<string>
  = fn(a: any, key: string){
    std/jsextern/ext/@extern-get-mstring(a, key);
  };
// Automatically generated. Retrieves the `internal` constructor field of the `:jspromise` type.
pub fun jspromise/internal : forall<a> (^ jspromise : jspromise<a>) -> any
  = forall<a> fn(jspromise: jspromise<a>){
    (match (jspromise) {
      ((@skip std/jsextern/Jspromise((@x: any)) : jspromise<a> ) as @pat: (jspromise<a>))
         -> @x;
    });
  };
pub fun arr/is-array : forall<a> (a : jsobject<a>) -> bool
  = forall<a> fn(a: jsobject<a>){
    std/jsextern/any/is-array((match (a) {
      ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
         -> @x;
    }));
  };
pub fun obj/new : forall<a> () -> jsobject<a>
  = forall<a> fn(){
    std/jsextern/Jsobject((std/jsextern/ext/new-obj()));
  };
pub fun arr/new : forall<a> () -> jsarray<a>
  = forall<a> fn(){
    std/jsextern/Jsarray((std/jsextern/ext/new-array()));
  };
pub fun arr/copy : forall<a> (a : jsarray<a>) -> jsarray<a>
  = forall<a> fn(a: jsarray<a>){
    std/jsextern/Jsarray((std/jsextern/ext/arr/copy((match (a) {
      ((@skip std/jsextern/Jsarray((@x: any)) : jsarray<a> ) as @pat: (jsarray<a>))
         -> @x;
    }))));
  };
pub fun obj/copy : forall<a> (a : jsobject<a>) -> jsobject<a>
  = forall<a> fn(a: jsobject<a>){
    std/jsextern/Jsobject((std/jsextern/ext/obj/copy((match (a) {
      ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
         -> @x;
    }))));
  };
pub fun obj/unsafe-as-array : forall<a,b> (a : jsobject<b>) -> jsarray<a>
  = forall<a,b> fn(a: jsobject<b>){
    std/jsextern/Jsarray((match (a) {
      ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<b> ) as @pat: (jsobject<b>))
         -> @x;
    }));
  };
pub fun maybeobj/unsafe-cast : forall<a,b> (a : maybe<jsobject<b>>) -> maybe<jsobject<a>>
  = forall<a,b> fn(a: maybe<jsobject<b>>){
    (match (a) {
      ((std/core/types/Just((x: jsobject<b>)) : maybe<jsobject<b>> ) as @pat: (maybe<jsobject<b>>))
         -> std/core/types/Just((std/jsextern/Jsobject((match (x) {
          ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<b> ) as @pat@0: (jsobject<b>))
             -> @x;
        }))));
      ((@skip std/core/types/Nothing() : maybe<jsobject<b>> ) as @pat@0@0: (maybe<jsobject<b>>))
         -> std/core/types/Nothing;
    });
  };
pub fun obj/unsafe-cast : forall<a,b> (a : jsobject<b>) -> jsobject<a>
  = forall<a,b> fn(a: jsobject<b>){
    std/jsextern/Jsobject((match (a) {
      ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<b> ) as @pat: (jsobject<b>))
         -> @x;
    }));
  };
pub fun field/is-bool : forall<a> (a : jsobject<a>, key : string) -> bool
  = forall<a> fn(a: jsobject<a>, key: string){
    std/jsextern/ext/field/is-bool((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), key);
  };
pub fun obj/is-bool : forall<a> (a : jsobject<a>) -> bool
  = forall<a> fn(a: jsobject<a>){
    std/jsextern/ext/is-bool((match (a) {
      ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
         -> @x;
    }));
  };
pub fun field/is-int : forall<a> (a : jsobject<a>, key : string) -> bool
  = forall<a> fn(a: jsobject<a>, key: string){
    std/jsextern/ext/field/is-int((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), key);
  };
pub fun obj/is-int : forall<a> (a : jsobject<a>) -> bool
  = forall<a> fn(a: jsobject<a>){
    std/jsextern/ext/is-int((match (a) {
      ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
         -> @x;
    }));
  };
pub fun obj/get-mstring : forall<a> (a : jsobject<a>, key : string) -> maybe<string>
  = forall<a> fn(a: jsobject<a>, key: string){
    std/jsextern/ext/get-mstring((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), key);
  };
pub fun obj/get-string : forall<a> (a : jsobject<a>, key : string) -> string
  = forall<a> fn(a: jsobject<a>, key: string){
    std/jsextern/ext/get-string((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), key);
  };
pub fun obj/set-string : forall<a> (a : jsobject<a>, key : string, value : string) -> ()
  = forall<a> fn(a: jsobject<a>, key: string, value: string){
    std/jsextern/ext/set-string((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), key, value);
  };
// Bool fields
pub fun ext/get-mbool : (a : any, key : string) -> maybe<bool>
  = fn(a: any, key: string){
    std/jsextern/ext/@extern-get-mbool(a, key);
  };
pub fun obj/get-mbool : forall<a> (a : jsobject<a>, key : string) -> maybe<bool>
  = forall<a> fn(a: jsobject<a>, key: string){
    std/jsextern/ext/get-mbool((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), key);
  };
pub fun obj/get-bool : forall<a> (a : jsobject<a>, key : string) -> bool
  = forall<a> fn(a: jsobject<a>, key: string){
    std/jsextern/ext/get-bool((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), key);
  };
pub fun obj/set-bool : forall<a> (a : jsobject<a>, key : string, value : bool) -> ()
  = forall<a> fn(a: jsobject<a>, key: string, value: bool){
    std/jsextern/ext/set-bool((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), key, value);
  };
// Int fields
pub fun ext/get-mint : (a : any, key : string) -> maybe<int>
  = fn(a: any, key: string){
    std/jsextern/ext/@extern-get-mint(a, key);
  };
pub fun obj/get-mint : forall<a> (a : jsobject<a>, key : string) -> maybe<int>
  = forall<a> fn(a: jsobject<a>, key: string){
    std/jsextern/ext/get-mint((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), key);
  };
pub fun obj/get-int : forall<a> (a : jsobject<a>, key : string) -> int
  = forall<a> fn(a: jsobject<a>, key: string){
    std/jsextern/ext/get-int((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), key);
  };
pub fun obj/set-int : forall<a> (a : jsobject<a>, key : string, value : int) -> ()
  = forall<a> fn(a: jsobject<a>, key: string, value: int){
    std/jsextern/ext/set-int((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), key, value);
  };
// Float fields
pub fun ext/get-mfloat : (a : any, key : string) -> maybe<float64>
  = fn(a: any, key: string){
    std/jsextern/ext/@extern-get-mfloat(a, key);
  };
pub fun field/is-float : forall<a> (a : jsobject<a>, key : string) -> bool
  = forall<a> fn(a: jsobject<a>, key: string){
    std/jsextern/ext/field/is-float((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), key);
  };
pub fun field/is-num : forall<a> (a : jsobject<a>, key : string) -> bool
  = forall<a> fn(a: jsobject<a>, key: string){
    std/jsextern/ext/field/is-float((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), key);
  };
pub fun obj/is-num : forall<a> (a : jsobject<a>) -> bool
  = forall<a> fn(a: jsobject<a>){
    std/jsextern/ext/is-num((match (a) {
      ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
         -> @x;
    }));
  };
pub fun obj/is-string : forall<a> (a : jsobject<a>) -> bool
  = forall<a> fn(a: jsobject<a>){
    std/jsextern/ext/is-string((match (a) {
      ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
         -> @x;
    }));
  };
// Cast to a supertype, given the evidence that t is a subtype of s
pub fun obj/supertype-cast : forall<a,b> (a : jsobject<b>, ?is-subtype : is-subtype<b,a>) -> jsobject<a>
  = forall<a,b> fn(a: jsobject<b>, @implicit/is-subtype: is-subtype<b,a>){
    std/jsextern/Jsobject((match (a) {
      ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<b> ) as @pat: (jsobject<b>))
         -> @x;
    }));
  };
pub fun unit/supertype-cast : forall<a> (a : jsobject<a>) -> jsobject<a>
  = forall<a> fn(a: jsobject<a>){
    a;
  };
// Cast to a subtype, given the evidence that t is a supertype of s
pub fun obj/subtype-cast : forall<a,b> (a : jsobject<b>, ?is-subtype : is-subtype<a,b>) -> jsobject<a>
  = forall<a,b> fn(a: jsobject<b>, @implicit/is-subtype: is-subtype<a,b>){
    std/jsextern/Jsobject((match (a) {
      ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<b> ) as @pat: (jsobject<b>))
         -> @x;
    }));
  };
pub fun unit/subtype-cast : forall<a> (a : jsobject<a>) -> jsobject<a>
  = forall<a> fn(a: jsobject<a>){
    a;
  };
// Transitive closure for evidence
pub fun trans/is-subtype : forall<a,b,c> (a : jsobject<c>, b : jsobject<b>, ?a/is-subtype : is-subtype<c,a>, ?b/is-subtype : is-subtype<a,b>) -> bool
  = forall<a,b,c> fn(a: jsobject<c>, b: jsobject<b>, @implicit/a/is-subtype: is-subtype<c,a>, @implicit/b/is-subtype: is-subtype<a,b>){
    std/core/types/True;
  };
// An object of the same type is trivially a subtype of itself
pub fun unit/is-subtype : forall<a> (a : jsobject<a>, b : jsobject<a>) -> bool
  = forall<a> fn(a: jsobject<a>, b: jsobject<a>){
    std/core/types/True;
  };
pub fun array/show : forall<a> (a : jsarray<a>) -> string
  = forall<a> fn(a: jsarray<a>){
    std/jsextern/ext/show((match (a) {
      ((@skip std/jsextern/Jsarray((@x: any)) : jsarray<a> ) as @pat: (jsarray<a>))
         -> @x;
    }));
  };
pub fun obj/show : forall<a> (a : jsobject<a>) -> string
  = forall<a> fn(a: jsobject<a>){
    std/jsextern/ext/show((match (a) {
      ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
         -> @x;
    }));
  };
pub fun obj/update-string : forall<a> (a : jsobject<a>, key : string, value : string) -> jsobject<a>
  = forall<a> fn(a: jsobject<a>, key: string, value: string){
    std/jsextern/Jsobject((std/jsextern/ext/update-string((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), key, value)));
  };
pub fun obj/update-bool : forall<a> (a : jsobject<a>, key : string, value : bool) -> jsobject<a>
  = forall<a> fn(a: jsobject<a>, key: string, value: bool){
    std/jsextern/Jsobject((std/jsextern/ext/update-bool((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), key, value)));
  };
pub fun obj/update-int : forall<a> (a : jsobject<a>, key : string, value : int) -> jsobject<a>
  = forall<a> fn(a: jsobject<a>, key: string, value: int){
    std/jsextern/Jsobject((std/jsextern/ext/update-int((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), key, value)));
  };
pub fun obj/get-mfloat : forall<a> (a : jsobject<a>, key : string) -> maybe<float64>
  = forall<a> fn(a: jsobject<a>, key: string){
    std/jsextern/ext/get-mfloat((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), key);
  };
pub fun obj/get-float : forall<a> (a : jsobject<a>, key : string) -> float64
  = forall<a> fn(a: jsobject<a>, key: string){
    std/jsextern/ext/get-float((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), key);
  };
pub fun obj/set-float : forall<a> (a : jsobject<a>, key : string, value : float64) -> ()
  = forall<a> fn(a: jsobject<a>, key: string, value: float64){
    std/jsextern/ext/set-float((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), key, value);
  };
pub fun obj/update-float : forall<a> (a : jsobject<a>, key : string, value : float64) -> jsobject<a>
  = forall<a> fn(a: jsobject<a>, key: string, value: float64){
    std/jsextern/Jsobject((std/jsextern/ext/update-float((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), key, value)));
  };
// Object fields
pub fun ext/get-mobj : (a : any, key : string) -> maybe<any>
  = fn(a: any, key: string){
    std/jsextern/ext/@extern-get-mobj(a, key);
  };
pub fun obj/get-mobj : forall<a,b> (a : jsobject<b>, key : string) -> maybe<jsobject<a>>
  = forall<a,b> fn(a: jsobject<b>, key: string){
    val m@10036 : maybe<any>
          = std/jsextern/ext/get-mobj((match (a) {
              ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<b> ) as @pat@1: (jsobject<b>))
                 -> @x;
            }), key);
    (match (m@10036) {
      ((std/core/types/Nothing() : maybe<any> ) as @pat: (maybe<any>))
         -> std/core/types/Nothing;
      ((@skip std/core/types/Just((x: any)) : maybe<any> ) as @pat@0: (maybe<any>))
         -> std/core/types/Just((std/jsextern/Jsobject(x)));
    });
  };
pub fun obj/get-obj : forall<a,b> (a : jsobject<b>, key : string) -> jsobject<a>
  = forall<a,b> fn(a: jsobject<b>, key: string){
    std/jsextern/Jsobject((std/jsextern/ext/get-obj((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<b> ) as @pat: (jsobject<b>))
           -> @x;
      }), key)));
  };
pub fun obj/set-obj : forall<a,b> (a : jsobject<b>, key : string, value : jsobject<a>) -> ()
  = forall<a,b> fn(a: jsobject<b>, key: string, value: jsobject<a>){
    std/jsextern/ext/set-obj((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<b> ) as @pat: (jsobject<b>))
           -> @x;
      }), key, (match (value) {
        ((@skip std/jsextern/Jsobject((@x@0: any)) : jsobject<a> ) as @pat@0: (jsobject<a>))
           -> @x@0;
      }));
  };
pub fun obj/update-obj : forall<a,b> (a : jsobject<b>, key : string, value : jsobject<a>) -> jsobject<b>
  = forall<a,b> fn(a: jsobject<b>, key: string, value: jsobject<a>){
    std/jsextern/Jsobject((std/jsextern/ext/update-obj((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<b> ) as @pat: (jsobject<b>))
           -> @x;
      }), key, (match (value) {
        ((@skip std/jsextern/Jsobject((@x@0: any)) : jsobject<a> ) as @pat@0: (jsobject<a>))
           -> @x@0;
      }))));
  };
// Array fields
pub fun obj/get-marray : forall<a,b> (a : jsobject<b>, key : string) -> maybe<jsarray<a>>
  = forall<a,b> fn(a: jsobject<b>, key: string){
    (match ((std/jsextern/ext/get-mobj((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<b> ) as @pat: (jsobject<b>))
           -> @x;
      }), key))) {
      ((std/core/types/Just((internal: any)) : maybe<any> ) as @pat@0: (maybe<any>))
         -> std/core/types/Just((std/jsextern/Jsarray(internal)));
      ((@skip std/core/types/Nothing() : maybe<any> ) as @pat@0@0: (maybe<any>))
         -> std/core/types/Nothing;
    });
  };
pub fun arr/get-array : forall<a,b> (a : jsobject<b>, key : string) -> jsarray<a>
  = forall<a,b> fn(a: jsobject<b>, key: string){
    std/jsextern/Jsarray((std/jsextern/ext/get-obj((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<b> ) as @pat: (jsobject<b>))
           -> @x;
      }), key)));
  };
pub fun obj/set-array : forall<a,b> (a : jsobject<b>, key : string, value : jsarray<a>) -> ()
  = forall<a,b> fn(a: jsobject<b>, key: string, value: jsarray<a>){
    std/jsextern/ext/set-obj((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<b> ) as @pat: (jsobject<b>))
           -> @x;
      }), key, (match (value) {
        ((@skip std/jsextern/Jsarray((@x@0: any)) : jsarray<a> ) as @pat@0: (jsarray<a>))
           -> @x@0;
      }));
  };
pub fun obj/update-array : forall<a,b> (a : jsobject<b>, key : string, value : jsarray<a>) -> jsobject<b>
  = forall<a,b> fn(a: jsobject<b>, key: string, value: jsarray<a>){
    std/jsextern/Jsobject((std/jsextern/ext/update-obj((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<b> ) as @pat: (jsobject<b>))
           -> @x;
      }), key, (match (value) {
        ((@skip std/jsextern/Jsarray((@x@0: any)) : jsarray<a> ) as @pat@0: (jsarray<a>))
           -> @x@0;
      }))));
  };
pub fun obj/has-key : forall<a> (a : jsobject<a>, key : string) -> bool
  = forall<a> fn(a: jsobject<a>, key: string){
    std/jsextern/has-key((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), key);
  };
pub fun obj/unsafe-as-string : forall<a> (a : jsobject<a>) -> string
  = forall<a> fn(a: jsobject<a>){
    std/jsextern/ext/unsafe-as-string((match (a) {
      ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
         -> @x;
    }));
  };
pub fun ext/unsafe-as-int : (a : any) -> int
  = fn(a: any){
    std/jsextern/ext/@extern-unsafe-as-int(a);
  };
pub fun obj/unsafe-as-int : forall<a> (a : jsobject<a>) -> int
  = forall<a> fn(a: jsobject<a>){
    std/jsextern/ext/unsafe-as-int((match (a) {
      ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
         -> @x;
    }));
  };
pub fun ext/unsafe-as-float : (a : any) -> float64
  = fn(a: any){
    std/jsextern/ext/@extern-unsafe-as-float(a);
  };
pub fun obj/unsafe-as-float : forall<a> (a : jsobject<a>) -> float64
  = forall<a> fn(a: jsobject<a>){
    std/jsextern/ext/unsafe-as-float((match (a) {
      ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
         -> @x;
    }));
  };
pub fun ext/unsafe-as-bool : (a : any) -> bool
  = fn(a: any){
    std/jsextern/ext/@extern-unsafe-as-bool(a);
  };
pub fun obj/unsafe-as-bool : forall<a> (a : jsobject<a>) -> bool
  = forall<a> fn(a: jsobject<a>){
    std/jsextern/ext/unsafe-as-bool((match (a) {
      ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
         -> @x;
    }));
  };
// Indexing operations
pub fun obj/int/@index : forall<a> (a : jsobject<a>, index : string) -> int
  = forall<a> fn(a: jsobject<a>, index: string){
    std/jsextern/ext/get-int((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), index);
  };
pub fun obj/mint/@index : forall<a> (a : jsobject<a>, index : string) -> maybe<int>
  = forall<a> fn(a: jsobject<a>, index: string){
    std/jsextern/ext/get-mint((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), index);
  };
pub fun obj/float/@index : forall<a> (a : jsobject<a>, index : string) -> float64
  = forall<a> fn(a: jsobject<a>, index: string){
    std/jsextern/ext/get-float((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), index);
  };
pub fun obj/mfloat/@index : forall<a> (a : jsobject<a>, index : string) -> maybe<float64>
  = forall<a> fn(a: jsobject<a>, index: string){
    std/jsextern/ext/get-mfloat((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), index);
  };
pub fun obj/bool/@index : forall<a> (a : jsobject<a>, index : string) -> bool
  = forall<a> fn(a: jsobject<a>, index: string){
    std/jsextern/ext/get-bool((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), index);
  };
pub fun obj/mbool/@index : forall<a> (a : jsobject<a>, index : string) -> maybe<bool>
  = forall<a> fn(a: jsobject<a>, index: string){
    std/jsextern/ext/get-mbool((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), index);
  };
pub fun obj/string/@index : forall<a> (a : jsobject<a>, index : string) -> string
  = forall<a> fn(a: jsobject<a>, index: string){
    std/jsextern/ext/get-string((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), index);
  };
pub fun obj/mstring/@index : forall<a> (a : jsobject<a>, index : string) -> maybe<string>
  = forall<a> fn(a: jsobject<a>, index: string){
    std/jsextern/ext/get-mstring((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), index);
  };
pub fun obj/obj/@index : forall<a,b> (a : jsobject<b>, index : string) -> jsobject<a>
  = forall<a,b> fn(a: jsobject<b>, index: string){
    std/jsextern/Jsobject((std/jsextern/ext/get-obj((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<b> ) as @pat: (jsobject<b>))
           -> @x;
      }), index)));
  };
pub fun obj/mobj/@index : forall<a,b> (a : jsobject<b>, index : string) -> maybe<jsobject<a>>
  = forall<a,b> fn(a: jsobject<b>, index: string){
    val m@10084 : maybe<any>
          = std/jsextern/ext/get-mobj((match (a) {
              ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<b> ) as @pat@1: (jsobject<b>))
                 -> @x;
            }), index);
    (match (m@10084) {
      ((std/core/types/Nothing() : maybe<any> ) as @pat: (maybe<any>))
         -> std/core/types/Nothing;
      ((@skip std/core/types/Just((x: any)) : maybe<any> ) as @pat@0: (maybe<any>))
         -> std/core/types/Just((std/jsextern/Jsobject(x)));
    });
  };
pub fun obj/array/@index : forall<a,b> (a : jsobject<b>, index : string) -> jsarray<a>
  = forall<a,b> fn(a: jsobject<b>, index: string){
    std/jsextern/Jsarray((std/jsextern/ext/get-obj((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<b> ) as @pat: (jsobject<b>))
           -> @x;
      }), index)));
  };
pub fun obj/int/@assign : forall<a> (a : jsobject<a>, index : string, value : int) -> ()
  = forall<a> fn(a: jsobject<a>, index: string, value: int){
    std/jsextern/ext/set-int((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), index, value);
  };
pub fun obj/float/@assign : forall<a> (a : jsobject<a>, index : string, value : float64) -> ()
  = forall<a> fn(a: jsobject<a>, index: string, value: float64){
    std/jsextern/ext/set-float((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), index, value);
  };
pub fun obj/bool/@assign : forall<a> (a : jsobject<a>, index : string, value : bool) -> ()
  = forall<a> fn(a: jsobject<a>, index: string, value: bool){
    std/jsextern/ext/set-bool((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), index, value);
  };
pub fun obj/string/@assign : forall<a> (a : jsobject<a>, index : string, value : string) -> ()
  = forall<a> fn(a: jsobject<a>, index: string, value: string){
    std/jsextern/ext/set-string((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }), index, value);
  };
pub fun obj/obj/@assign : forall<a,b> (a : jsobject<b>, index : string, value : jsobject<a>) -> ()
  = forall<a,b> fn(a: jsobject<b>, index: string, value: jsobject<a>){
    std/jsextern/ext/set-obj((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<b> ) as @pat: (jsobject<b>))
           -> @x;
      }), index, (match (value) {
        ((@skip std/jsextern/Jsobject((@x@0: any)) : jsobject<a> ) as @pat@0: (jsobject<a>))
           -> @x@0;
      }));
  };
pub fun obj/array/@assign : forall<a,b> (a : jsobject<b>, index : string, value : jsarray<a>) -> ()
  = forall<a,b> fn(a: jsobject<b>, index: string, value: jsarray<a>){
    std/jsextern/ext/set-obj((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<b> ) as @pat: (jsobject<b>))
           -> @x;
      }), index, (match (value) {
        ((@skip std/jsextern/Jsarray((@x@0: any)) : jsarray<a> ) as @pat@0: (jsarray<a>))
           -> @x@0;
      }));
  };
pub fun boolarray/@index : (a : jsarray<bool>, index : int) -> bool
  = fn(a: jsarray<bool>, index: int){
    std/jsextern/bool/@index((match (a) {
        ((@skip std/jsextern/Jsarray((@x: any)) : jsarray<bool> ) as @pat: (jsarray<bool>))
           -> @x;
      }), index);
  };
pub fun floatarray/@index : (a : jsarray<float64>, index : int) -> float64
  = fn(a: jsarray<float64>, index: int){
    std/jsextern/float/@index((match (a) {
        ((@skip std/jsextern/Jsarray((@x: any)) : jsarray<float64> ) as @pat: (jsarray<float64>))
           -> @x;
      }), index);
  };
pub fun intarray/@index : (a : jsarray<int>, index : int) -> int
  = fn(a: jsarray<int>, index: int){
    std/jsextern/int/@index((match (a) {
        ((@skip std/jsextern/Jsarray((@x: any)) : jsarray<int> ) as @pat: (jsarray<int>))
           -> @x;
      }), index);
  };
pub fun jsarray/@index : forall<a> (a : jsarray<jsarray<a>>, index : int) -> jsarray<a>
  = forall<a> fn(a: jsarray<jsarray<a>>, index: int){
    std/jsextern/Jsarray((std/jsextern/any/@index((match (a) {
        ((@skip std/jsextern/Jsarray((@x: any)) : jsarray<jsarray<a>> ) as @pat: (jsarray<jsarray<a>>))
           -> @x;
      }), index)));
  };
pub fun mboolarray/@index : (a : jsarray<maybe<bool>>, index : int) -> maybe<bool>
  = fn(a: jsarray<maybe<bool>>, index: int){
    std/jsextern/mbool/@index((match (a) {
        ((@skip std/jsextern/Jsarray((@x: any)) : jsarray<maybe<bool>> ) as @pat: (jsarray<maybe<bool>>))
           -> @x;
      }), index);
  };
pub fun mfloatarray/@index : (a : jsarray<maybe<float64>>, index : int) -> maybe<float64>
  = fn(a: jsarray<maybe<float64>>, index: int){
    std/jsextern/mfloat/@index((match (a) {
        ((@skip std/jsextern/Jsarray((@x: any)) : jsarray<maybe<float64>> ) as @pat: (jsarray<maybe<float64>>))
           -> @x;
      }), index);
  };
pub fun mintarray/@index : (a : jsarray<maybe<int>>, index : int) -> maybe<int>
  = fn(a: jsarray<maybe<int>>, index: int){
    std/jsextern/mint/@index((match (a) {
        ((@skip std/jsextern/Jsarray((@x: any)) : jsarray<maybe<int>> ) as @pat: (jsarray<maybe<int>>))
           -> @x;
      }), index);
  };
pub fun mjsarray/@index : forall<a> (a : jsarray<int>, index : int) -> maybe<jsarray<a>>
  = forall<a> fn(a: jsarray<int>, index: int){
    val m@10123 : maybe<any>
          = std/jsextern/many/@index((match (a) {
              ((@skip std/jsextern/Jsarray((@x: any)) : jsarray<int> ) as @pat@1: (jsarray<int>))
                 -> @x;
            }), index);
    (match (m@10123) {
      ((std/core/types/Nothing() : maybe<any> ) as @pat: (maybe<any>))
         -> std/core/types/Nothing;
      ((@skip std/core/types/Just((x: any)) : maybe<any> ) as @pat@0: (maybe<any>))
         -> std/core/types/Just((std/jsextern/Jsarray(x)));
    });
  };
pub fun mobjarray/@index : forall<a> (a : jsarray<maybe<jsobject<a>>>, index : int) -> maybe<jsobject<a>>
  = forall<a> fn(a: jsarray<maybe<jsobject<a>>>, index: int){
    val m@10126 : maybe<any>
          = std/jsextern/many/@index((match (a) {
              ((@skip std/jsextern/Jsarray((@x: any)) : jsarray<maybe<jsobject<a>>> ) as @pat@1: (jsarray<maybe<jsobject<a>>>))
                 -> @x;
            }), index);
    (match (m@10126) {
      ((std/core/types/Nothing() : maybe<any> ) as @pat: (maybe<any>))
         -> std/core/types/Nothing;
      ((@skip std/core/types/Just((x: any)) : maybe<any> ) as @pat@0: (maybe<any>))
         -> std/core/types/Just((std/jsextern/Jsobject(x)));
    });
  };
pub fun mstrarray/@index : (a : jsarray<maybe<string>>, index : int) -> maybe<string>
  = fn(a: jsarray<maybe<string>>, index: int){
    std/jsextern/mstring/@index((match (a) {
        ((@skip std/jsextern/Jsarray((@x: any)) : jsarray<maybe<string>> ) as @pat: (jsarray<maybe<string>>))
           -> @x;
      }), index);
  };
pub fun objarray/@index : forall<a> (a : jsarray<jsobject<a>>, index : int) -> jsobject<a>
  = forall<a> fn(a: jsarray<jsobject<a>>, index: int){
    std/jsextern/Jsobject((std/jsextern/any/@index((match (a) {
        ((@skip std/jsextern/Jsarray((@x: any)) : jsarray<jsobject<a>> ) as @pat: (jsarray<jsobject<a>>))
           -> @x;
      }), index)));
  };
pub fun strarray/@index : (a : jsarray<string>, index : int) -> string
  = fn(a: jsarray<string>, index: int){
    std/jsextern/string/@index((match (a) {
        ((@skip std/jsextern/Jsarray((@x: any)) : jsarray<string> ) as @pat: (jsarray<string>))
           -> @x;
      }), index);
  };
pub fun boolarray/@assign : (a : jsarray<bool>, index : int, value : bool) -> ()
  = fn(a: jsarray<bool>, index: int, value: bool){
    std/jsextern/bool/@assign((match (a) {
        ((@skip std/jsextern/Jsarray((@x: any)) : jsarray<bool> ) as @pat: (jsarray<bool>))
           -> @x;
      }), index, value);
  };
pub fun floatarray/@assign : (a : jsarray<float64>, index : int, value : float64) -> ()
  = fn(a: jsarray<float64>, index: int, value: float64){
    std/jsextern/float/@assign((match (a) {
        ((@skip std/jsextern/Jsarray((@x: any)) : jsarray<float64> ) as @pat: (jsarray<float64>))
           -> @x;
      }), index, value);
  };
pub fun intarray/@assign : (a : jsarray<int>, index : int, value : int) -> ()
  = fn(a: jsarray<int>, index: int, value: int){
    std/jsextern/int/@assign((match (a) {
        ((@skip std/jsextern/Jsarray((@x: any)) : jsarray<int> ) as @pat: (jsarray<int>))
           -> @x;
      }), index, value);
  };
pub fun jsarray/@assign : forall<a> (a : jsarray<jsobject<a>>, index : int, value : jsarray<a>) -> ()
  = forall<a> fn(a: jsarray<jsobject<a>>, index: int, value: jsarray<a>){
    std/jsextern/any/@assign((match (a) {
        ((@skip std/jsextern/Jsarray((@x: any)) : jsarray<jsobject<a>> ) as @pat: (jsarray<jsobject<a>>))
           -> @x;
      }), index, (match (value) {
        ((@skip std/jsextern/Jsarray((@x@0: any)) : jsarray<a> ) as @pat@0: (jsarray<a>))
           -> @x@0;
      }));
  };
pub fun objarray/@assign : forall<a> (a : jsarray<jsobject<a>>, index : int, value : jsobject<a>) -> ()
  = forall<a> fn(a: jsarray<jsobject<a>>, index: int, value: jsobject<a>){
    std/jsextern/any/@assign((match (a) {
        ((@skip std/jsextern/Jsarray((@x: any)) : jsarray<jsobject<a>> ) as @pat: (jsarray<jsobject<a>>))
           -> @x;
      }), index, (match (value) {
        ((@skip std/jsextern/Jsobject((@x@0: any)) : jsobject<a> ) as @pat@0: (jsobject<a>))
           -> @x@0;
      }));
  };
pub fun strarray/@assign : (a : jsarray<string>, index : int, value : string) -> ()
  = fn(a: jsarray<string>, index: int, value: string){
    std/jsextern/string/@assign((match (a) {
        ((@skip std/jsextern/Jsarray((@x: any)) : jsarray<string> ) as @pat: (jsarray<string>))
           -> @x;
      }), index, value);
  };
pub fun arr/length : forall<a> (a : jsarray<a>) -> int
  = forall<a> fn(a: jsarray<a>){
    std/jsextern/ext/length((match (a) {
      ((@skip std/jsextern/Jsarray((@x: any)) : jsarray<a> ) as @pat: (jsarray<a>))
         -> @x;
    }));
  };
// lifted local: arrarr/@lift-list@10419, arrarr/list, @spec-x10326
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10321, using:
// @uniq-f@10321 = (fn(i: int){
//   std/jsextern/Jsarray<a>((std/jsextern/any/@index((match (a) {
//       ((@skip std/jsextern/Jsarray((@x@0: any) : any) : (std/jsextern/jsarray :: V -> V)<(std/jsextern/jsarray :: V -> V)<a>> ) as @pat@0: ((std/jsextern/jsarray :: V -> V)<(std/jsextern/jsarray :: V -> V)<4880>>))
//          -> @x@0;
//     }), i)));
// },Own)
fun arrarr/@trmc-lift-list@10420 : forall<a> (a : jsarray<jsarray<a>>, @uniq-xs@10320 : list<int>, @acc : ctx<list<jsarray<a>>>) -> list<jsarray<a>>
  = forall<a> fn(a: jsarray<jsarray<a>>, @uniq-xs@10320: list<int>, @acc: ctx<list<jsarray<a>>>){
    (match (@uniq-xs@10320) {
      ((std/core/types/Cons((@uniq-x@10323: int), (@uniq-xx@10324: list<int>)) : list<int> ) as @uniq-pat@10322: (list<int>))
         -> val @trmc-x10451 : jsarray<a>
              = std/jsextern/Jsarray((std/jsextern/any/@index((match (a) {
                  ((@skip std/jsextern/Jsarray((@x@0: any)) : jsarray<jsarray<a>> ) as @pat@0: (jsarray<jsarray<a>>))
                     -> @x@0;
                }), @uniq-x@10323)));
            val @trmc-x10452 : list<jsarray<a>>
              = std/core/types/@cctx-hole-create();
            val @trmc-x10453 : list<jsarray<a>>
              = std/core/types/Cons(@trmc-x10451, @trmc-x10452);
        std/jsextern/arrarr/@trmc-lift-list@10420(a, @uniq-xx@10324, (std/core/types/@cctx-extend(@acc, @trmc-x10453, (std/core/types/@field-addr-of(@trmc-x10453, "(\x22std/core/types\x22,\x22\x22,\x22Cons\x22)", "(\x22\x22,\x22\x22,\x22tail\x22)")))));
      ((@skip std/core/types/Nil() : list<int> ) as @uniq-pat@0@10325: (list<int>))
         -> std/core/types/cctx/((++.))(@acc, std/core/types/Nil);
    });
  };
// lifted local: arrarr/@lift-list@10419, arrarr/list, @spec-x10326
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10321, using:
// @uniq-f@10321 = (fn(i: int){
//   std/jsextern/Jsarray<a>((std/jsextern/any/@index((match (a) {
//       ((@skip std/jsextern/Jsarray((@x@0: any) : any) : (std/jsextern/jsarray :: V -> V)<(std/jsextern/jsarray :: V -> V)<a>> ) as @pat@0: ((std/jsextern/jsarray :: V -> V)<(std/jsextern/jsarray :: V -> V)<4880>>))
//          -> @x@0;
//     }), i)));
// },Own)
fun arrarr/@lift-list@10420 : forall<a> (a : jsarray<jsarray<a>>, @uniq-xs@10320 : list<int>) -> list<jsarray<a>>
  = forall<a> fn(a@0: jsarray<jsarray<a>>, @uniq-xs@10320@0: list<int>){
    std/jsextern/arrarr/@trmc-lift-list@10420(a@0, @uniq-xs@10320@0, (std/core/types/cctx/empty()));
  };
// lifted local: arrarr/list, @spec-x10319
// specialized: std/core/list/map, on parameters @uniq-f@10316, using:
// @uniq-f@10316 = (fn(i: int){
//   std/jsextern/Jsarray<a>((std/jsextern/any/@index((match (a) {
//       ((@skip std/jsextern/Jsarray((@x@0: any) : any) : (std/jsextern/jsarray :: V -> V)<(std/jsextern/jsarray :: V -> V)<a>> ) as @pat@0: ((std/jsextern/jsarray :: V -> V)<(std/jsextern/jsarray :: V -> V)<4880>>))
//          -> @x@0;
//     }), i)));
// },Own)
fun arrarr/@lift-list@10419 : forall<a> (a : jsarray<jsarray<a>>, @uniq-xs@10315 : list<int>) -> list<jsarray<a>>
  = forall<a> fn(a: jsarray<jsarray<a>>, @uniq-xs@10315: list<int>){
    (match (@uniq-xs@10315) {
      ((std/core/types/Nil() : list<int> ) as @uniq-pat@0@10317: (list<int>))
         -> std/core/types/Nil;
      (@uniq-pat@10318: (list<int>))
         -> std/jsextern/arrarr/@trmc-lift-list@10420(a, @uniq-xs@10315, (std/core/types/cctx/empty()));
    });
  };
pub fun arrarr/list : forall<a> (a : jsarray<jsarray<a>>) -> list<jsarray<a>>
  = forall<a> fn(a: jsarray<jsarray<a>>){
    val x@10141 : int
      = std/jsextern/ext/length((match (a) {
        ((@skip std/jsextern/Jsarray((@x: any)) : jsarray<jsarray<a>> ) as @pat: (jsarray<jsarray<a>>))
           -> @x;
      }));
    val @uniq-xs@10315@10436 : list<int>
      = std/core/list/range/list(0, (std/core/int/int-sub(x@10141, 1)));
    std/jsextern/arrarr/@lift-list@10419(a, @uniq-xs@10315@10436);
  };
// lifted local: boolarray/@lift-list@10421, boolarray/list, @spec-x10339
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10334, using:
// @uniq-f@10334 = (fn(i: int){
//   std/jsextern/bool/@index((match (a) {
//       ((@skip std/jsextern/Jsarray((@x@0: any) : any) : (std/jsextern/jsarray :: V -> V)<bool> ) as @pat@0: ((std/jsextern/jsarray :: V -> V)<bool>))
//          -> @x@0;
//     }), i);
// },Own)
fun boolarray/@trmc-lift-list@10422 : (a : jsarray<bool>, @uniq-xs@10333 : list<int>, @acc : ctx<list<bool>>) -> list<bool>
  = fn(a: jsarray<bool>, @uniq-xs@10333: list<int>, @acc: ctx<list<bool>>){
    match (@uniq-xs@10333) {
      ((std/core/types/Cons((@uniq-x@10336: int), (@uniq-xx@10337: list<int>)) : list<int> ) as @uniq-pat@10335: (list<int>))
         -> val @trmc-x10454 : bool
              = std/jsextern/bool/@index((match (a) {
                  ((@skip std/jsextern/Jsarray((@x@0: any)) : jsarray<bool> ) as @pat@0: (jsarray<bool>))
                     -> @x@0;
                }), @uniq-x@10336);
            val @trmc-x10455 : list<bool>
              = std/core/types/@cctx-hole-create();
            val @trmc-x10456 : list<bool>
              = std/core/types/Cons(@trmc-x10454, @trmc-x10455);
        std/jsextern/boolarray/@trmc-lift-list@10422(a, @uniq-xx@10337, (std/core/types/@cctx-extend(@acc, @trmc-x10456, (std/core/types/@field-addr-of(@trmc-x10456, "(\x22std/core/types\x22,\x22\x22,\x22Cons\x22)", "(\x22\x22,\x22\x22,\x22tail\x22)")))));
      ((@skip std/core/types/Nil() : list<int> ) as @uniq-pat@0@10338: (list<int>))
         -> std/core/types/cctx/((++.))(@acc, std/core/types/Nil);
    };
  };
// lifted local: boolarray/@lift-list@10421, boolarray/list, @spec-x10339
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10334, using:
// @uniq-f@10334 = (fn(i: int){
//   std/jsextern/bool/@index((match (a) {
//       ((@skip std/jsextern/Jsarray((@x@0: any) : any) : (std/jsextern/jsarray :: V -> V)<bool> ) as @pat@0: ((std/jsextern/jsarray :: V -> V)<bool>))
//          -> @x@0;
//     }), i);
// },Own)
fun boolarray/@lift-list@10422 : (a : jsarray<bool>, @uniq-xs@10333 : list<int>) -> list<bool>
  = fn(a@0: jsarray<bool>, @uniq-xs@10333@0: list<int>){
    std/jsextern/boolarray/@trmc-lift-list@10422(a@0, @uniq-xs@10333@0, (std/core/types/cctx/empty()));
  };
// lifted local: boolarray/list, @spec-x10332
// specialized: std/core/list/map, on parameters @uniq-f@10329, using:
// @uniq-f@10329 = (fn(i: int){
//   std/jsextern/bool/@index((match (a) {
//       ((@skip std/jsextern/Jsarray((@x@0: any) : any) : (std/jsextern/jsarray :: V -> V)<bool> ) as @pat@0: ((std/jsextern/jsarray :: V -> V)<bool>))
//          -> @x@0;
//     }), i);
// },Own)
fun boolarray/@lift-list@10421 : (a : jsarray<bool>, @uniq-xs@10328 : list<int>) -> list<bool>
  = fn(a: jsarray<bool>, @uniq-xs@10328: list<int>){
    match (@uniq-xs@10328) {
      ((std/core/types/Nil() : list<int> ) as @uniq-pat@0@10330: (list<int>))
         -> std/core/types/Nil;
      (@uniq-pat@10331: (list<int>))
         -> std/jsextern/boolarray/@trmc-lift-list@10422(a, @uniq-xs@10328, (std/core/types/cctx/empty()));
    };
  };
pub fun boolarray/list : (a : jsarray<bool>) -> list<bool>
  = fn(a: jsarray<bool>){
    val x@10148 : int
      = std/jsextern/ext/length((match (a) {
        ((@skip std/jsextern/Jsarray((@x: any)) : jsarray<bool> ) as @pat: (jsarray<bool>))
           -> @x;
      }));
    val @uniq-xs@10328@10438 : list<int>
      = std/core/list/range/list(0, (std/core/int/int-sub(x@10148, 1)));
    std/jsextern/boolarray/@lift-list@10421(a, @uniq-xs@10328@10438);
  };
// lifted local: floatarray/@lift-list@10423, floatarray/list, @spec-x10352
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10347, using:
// @uniq-f@10347 = (fn(i: int){
//   std/jsextern/float/@index((match (a) {
//       ((@skip std/jsextern/Jsarray((@x@0: any) : any) : (std/jsextern/jsarray :: V -> V)<float64> ) as @pat@0: ((std/jsextern/jsarray :: V -> V)<float64>))
//          -> @x@0;
//     }), i);
// },Own)
fun floatarray/@trmc-lift-list@10424 : (a : jsarray<float64>, @uniq-xs@10346 : list<int>, @acc : ctx<list<float64>>) -> list<float64>
  = fn(a: jsarray<float64>, @uniq-xs@10346: list<int>, @acc: ctx<list<float64>>){
    match (@uniq-xs@10346) {
      ((std/core/types/Cons((@uniq-x@10349: int), (@uniq-xx@10350: list<int>)) : list<int> ) as @uniq-pat@10348: (list<int>))
         -> val @trmc-x10457 : float64
              = std/jsextern/float/@index((match (a) {
                  ((@skip std/jsextern/Jsarray((@x@0: any)) : jsarray<float64> ) as @pat@0: (jsarray<float64>))
                     -> @x@0;
                }), @uniq-x@10349);
            val @trmc-x10458 : list<float64>
              = std/core/types/@cctx-hole-create();
            val @trmc-x10459 : list<float64>
              = std/core/types/Cons(@trmc-x10457, @trmc-x10458);
        std/jsextern/floatarray/@trmc-lift-list@10424(a, @uniq-xx@10350, (std/core/types/@cctx-extend(@acc, @trmc-x10459, (std/core/types/@field-addr-of(@trmc-x10459, "(\x22std/core/types\x22,\x22\x22,\x22Cons\x22)", "(\x22\x22,\x22\x22,\x22tail\x22)")))));
      ((@skip std/core/types/Nil() : list<int> ) as @uniq-pat@0@10351: (list<int>))
         -> std/core/types/cctx/((++.))(@acc, std/core/types/Nil);
    };
  };
// lifted local: floatarray/@lift-list@10423, floatarray/list, @spec-x10352
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10347, using:
// @uniq-f@10347 = (fn(i: int){
//   std/jsextern/float/@index((match (a) {
//       ((@skip std/jsextern/Jsarray((@x@0: any) : any) : (std/jsextern/jsarray :: V -> V)<float64> ) as @pat@0: ((std/jsextern/jsarray :: V -> V)<float64>))
//          -> @x@0;
//     }), i);
// },Own)
fun floatarray/@lift-list@10424 : (a : jsarray<float64>, @uniq-xs@10346 : list<int>) -> list<float64>
  = fn(a@0: jsarray<float64>, @uniq-xs@10346@0: list<int>){
    std/jsextern/floatarray/@trmc-lift-list@10424(a@0, @uniq-xs@10346@0, (std/core/types/cctx/empty()));
  };
// lifted local: floatarray/list, @spec-x10345
// specialized: std/core/list/map, on parameters @uniq-f@10342, using:
// @uniq-f@10342 = (fn(i: int){
//   std/jsextern/float/@index((match (a) {
//       ((@skip std/jsextern/Jsarray((@x@0: any) : any) : (std/jsextern/jsarray :: V -> V)<float64> ) as @pat@0: ((std/jsextern/jsarray :: V -> V)<float64>))
//          -> @x@0;
//     }), i);
// },Own)
fun floatarray/@lift-list@10423 : (a : jsarray<float64>, @uniq-xs@10341 : list<int>) -> list<float64>
  = fn(a: jsarray<float64>, @uniq-xs@10341: list<int>){
    match (@uniq-xs@10341) {
      ((std/core/types/Nil() : list<int> ) as @uniq-pat@0@10343: (list<int>))
         -> std/core/types/Nil;
      (@uniq-pat@10344: (list<int>))
         -> std/jsextern/floatarray/@trmc-lift-list@10424(a, @uniq-xs@10341, (std/core/types/cctx/empty()));
    };
  };
pub fun floatarray/list : (a : jsarray<float64>) -> list<float64>
  = fn(a: jsarray<float64>){
    val x@10155 : int
      = std/jsextern/ext/length((match (a) {
        ((@skip std/jsextern/Jsarray((@x: any)) : jsarray<float64> ) as @pat: (jsarray<float64>))
           -> @x;
      }));
    val @uniq-xs@10341@10440 : list<int>
      = std/core/list/range/list(0, (std/core/int/int-sub(x@10155, 1)));
    std/jsextern/floatarray/@lift-list@10423(a, @uniq-xs@10341@10440);
  };
// lifted local: intarray/@lift-list@10425, intarray/list, @spec-x10365
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10360, using:
// @uniq-f@10360 = (fn(i: int){
//   std/jsextern/int/@index((match (a) {
//       ((@skip std/jsextern/Jsarray((@x@0: any) : any) : (std/jsextern/jsarray :: V -> V)<int> ) as @pat@0: ((std/jsextern/jsarray :: V -> V)<int>))
//          -> @x@0;
//     }), i);
// },Own)
fun intarray/@trmc-lift-list@10426 : (a : jsarray<int>, @uniq-xs@10359 : list<int>, @acc : ctx<list<int>>) -> list<int>
  = fn(a: jsarray<int>, @uniq-xs@10359: list<int>, @acc: ctx<list<int>>){
    match (@uniq-xs@10359) {
      ((std/core/types/Cons((@uniq-x@10362: int), (@uniq-xx@10363: list<int>)) : list<int> ) as @uniq-pat@10361: (list<int>))
         -> val @trmc-x10460 : int
              = std/jsextern/int/@index((match (a) {
                  ((@skip std/jsextern/Jsarray((@x@0: any)) : jsarray<int> ) as @pat@0: (jsarray<int>))
                     -> @x@0;
                }), @uniq-x@10362);
            val @trmc-x10461 : list<int>
              = std/core/types/@cctx-hole-create();
            val @trmc-x10462 : list<int>
              = std/core/types/Cons(@trmc-x10460, @trmc-x10461);
        std/jsextern/intarray/@trmc-lift-list@10426(a, @uniq-xx@10363, (std/core/types/@cctx-extend(@acc, @trmc-x10462, (std/core/types/@field-addr-of(@trmc-x10462, "(\x22std/core/types\x22,\x22\x22,\x22Cons\x22)", "(\x22\x22,\x22\x22,\x22tail\x22)")))));
      ((@skip std/core/types/Nil() : list<int> ) as @uniq-pat@0@10364: (list<int>))
         -> std/core/types/cctx/((++.))(@acc, std/core/types/Nil);
    };
  };
// lifted local: intarray/@lift-list@10425, intarray/list, @spec-x10365
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10360, using:
// @uniq-f@10360 = (fn(i: int){
//   std/jsextern/int/@index((match (a) {
//       ((@skip std/jsextern/Jsarray((@x@0: any) : any) : (std/jsextern/jsarray :: V -> V)<int> ) as @pat@0: ((std/jsextern/jsarray :: V -> V)<int>))
//          -> @x@0;
//     }), i);
// },Own)
fun intarray/@lift-list@10426 : (a : jsarray<int>, @uniq-xs@10359 : list<int>) -> list<int>
  = fn(a@0: jsarray<int>, @uniq-xs@10359@0: list<int>){
    std/jsextern/intarray/@trmc-lift-list@10426(a@0, @uniq-xs@10359@0, (std/core/types/cctx/empty()));
  };
// lifted local: intarray/list, @spec-x10358
// specialized: std/core/list/map, on parameters @uniq-f@10355, using:
// @uniq-f@10355 = (fn(i: int){
//   std/jsextern/int/@index((match (a) {
//       ((@skip std/jsextern/Jsarray((@x@0: any) : any) : (std/jsextern/jsarray :: V -> V)<int> ) as @pat@0: ((std/jsextern/jsarray :: V -> V)<int>))
//          -> @x@0;
//     }), i);
// },Own)
fun intarray/@lift-list@10425 : (a : jsarray<int>, @uniq-xs@10354 : list<int>) -> list<int>
  = fn(a: jsarray<int>, @uniq-xs@10354: list<int>){
    match (@uniq-xs@10354) {
      ((std/core/types/Nil() : list<int> ) as @uniq-pat@0@10356: (list<int>))
         -> std/core/types/Nil;
      (@uniq-pat@10357: (list<int>))
         -> std/jsextern/intarray/@trmc-lift-list@10426(a, @uniq-xs@10354, (std/core/types/cctx/empty()));
    };
  };
pub fun intarray/list : (a : jsarray<int>) -> list<int>
  = fn(a: jsarray<int>){
    val x@10162 : int
      = std/jsextern/ext/length((match (a) {
        ((@skip std/jsextern/Jsarray((@x: any)) : jsarray<int> ) as @pat: (jsarray<int>))
           -> @x;
      }));
    val @uniq-xs@10354@10442 : list<int>
      = std/core/list/range/list(0, (std/core/int/int-sub(x@10162, 1)));
    std/jsextern/intarray/@lift-list@10425(a, @uniq-xs@10354@10442);
  };
// lifted local: mobjarr/@lift-list@10427, mobjarr/list, @spec-x10378
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10373, using:
// @uniq-f@10373 = (fn(i: int){
//   val m@10175 : (maybe :: V -> V)<any>
//         = std/jsextern/many/@index((match (a) {
//             ((@skip std/jsextern/Jsarray((@x@0: any) : any) : (std/jsextern/jsarray :: V -> V)<(maybe :: V -> V)<(std/jsextern/jsobject :: V -> V)<a>>> ) as @pat@1: ((std/jsextern/jsarray :: V -> V)<(maybe :: V -> V)<(std/jsextern/jsobject :: V -> V)<5476>>>))
//                -> @x@0;
//           }), i);
//   match (m@10175) {
//     ((std/core/types/Nothing() : (maybe :: V -> V)<any> ) as @pat@0: ((maybe :: V -> V)<any>))
//        -> std/core/types/Nothing<(std/jsextern/jsobject :: V -> V)<a>>;
//     ((@skip std/core/types/Just((x@0: any) : any) : (maybe :: V -> V)<any> ) as @pat@0@0: ((maybe :: V -> V)<any>))
//        -> std/core/types/Just<(std/jsextern/jsobject :: V -> V)<a>>((std/jsextern/Jsobject<a>(x@0)));
//   };
// },Own)
fun mobjarr/@trmc-lift-list@10428 : forall<a> (a : jsarray<maybe<jsobject<a>>>, @uniq-xs@10372 : list<int>, @acc : ctx<list<maybe<jsobject<a>>>>) -> list<maybe<jsobject<a>>>
  = forall<a> fn(a: jsarray<maybe<jsobject<a>>>, @uniq-xs@10372: list<int>, @acc: ctx<list<maybe<jsobject<a>>>>){
    (match (@uniq-xs@10372) {
      ((std/core/types/Cons((@uniq-x@10375: int), (@uniq-xx@10376: list<int>)) : list<int> ) as @uniq-pat@10374: (list<int>))
         -> val m@10175 : maybe<any>
              = std/jsextern/many/@index((match (a) {
                  ((@skip std/jsextern/Jsarray((@x@0: any)) : jsarray<maybe<jsobject<a>>> ) as @pat@1: (jsarray<maybe<jsobject<a>>>))
                     -> @x@0;
                }), @uniq-x@10375);
            val @trmc-x10463 : list<maybe<jsobject<a>>>
              = std/core/types/@cctx-hole-create();
            val @trmc-x10464 : list<maybe<jsobject<a>>>
              = std/core/types/Cons((match (m@10175) {
                  ((std/core/types/Nothing() : maybe<any> ) as @pat@0: (maybe<any>))
                     -> std/core/types/Nothing;
                  ((@skip std/core/types/Just((x@0: any)) : maybe<any> ) as @pat@0@0: (maybe<any>))
                     -> std/core/types/Just((std/jsextern/Jsobject(x@0)));
                }), @trmc-x10463);
        std/jsextern/mobjarr/@trmc-lift-list@10428(a, @uniq-xx@10376, (std/core/types/@cctx-extend(@acc, @trmc-x10464, (std/core/types/@field-addr-of(@trmc-x10464, "(\x22std/core/types\x22,\x22\x22,\x22Cons\x22)", "(\x22\x22,\x22\x22,\x22tail\x22)")))));
      ((@skip std/core/types/Nil() : list<int> ) as @uniq-pat@0@10377: (list<int>))
         -> std/core/types/cctx/((++.))(@acc, std/core/types/Nil);
    });
  };
// lifted local: mobjarr/@lift-list@10427, mobjarr/list, @spec-x10378
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10373, using:
// @uniq-f@10373 = (fn(i: int){
//   val m@10175 : (maybe :: V -> V)<any>
//         = std/jsextern/many/@index((match (a) {
//             ((@skip std/jsextern/Jsarray((@x@0: any) : any) : (std/jsextern/jsarray :: V -> V)<(maybe :: V -> V)<(std/jsextern/jsobject :: V -> V)<a>>> ) as @pat@1: ((std/jsextern/jsarray :: V -> V)<(maybe :: V -> V)<(std/jsextern/jsobject :: V -> V)<5476>>>))
//                -> @x@0;
//           }), i);
//   match (m@10175) {
//     ((std/core/types/Nothing() : (maybe :: V -> V)<any> ) as @pat@0: ((maybe :: V -> V)<any>))
//        -> std/core/types/Nothing<(std/jsextern/jsobject :: V -> V)<a>>;
//     ((@skip std/core/types/Just((x@0: any) : any) : (maybe :: V -> V)<any> ) as @pat@0@0: ((maybe :: V -> V)<any>))
//        -> std/core/types/Just<(std/jsextern/jsobject :: V -> V)<a>>((std/jsextern/Jsobject<a>(x@0)));
//   };
// },Own)
fun mobjarr/@lift-list@10428 : forall<a> (a : jsarray<maybe<jsobject<a>>>, @uniq-xs@10372 : list<int>) -> list<maybe<jsobject<a>>>
  = forall<a> fn(a@0: jsarray<maybe<jsobject<a>>>, @uniq-xs@10372@0: list<int>){
    std/jsextern/mobjarr/@trmc-lift-list@10428(a@0, @uniq-xs@10372@0, (std/core/types/cctx/empty()));
  };
// lifted local: mobjarr/list, @spec-x10371
// specialized: std/core/list/map, on parameters @uniq-f@10368, using:
// @uniq-f@10368 = (fn(i: int){
//   val m@10175 : (maybe :: V -> V)<any>
//         = std/jsextern/many/@index((match (a) {
//             ((@skip std/jsextern/Jsarray((@x@0: any) : any) : (std/jsextern/jsarray :: V -> V)<(maybe :: V -> V)<(std/jsextern/jsobject :: V -> V)<a>>> ) as @pat@1: ((std/jsextern/jsarray :: V -> V)<(maybe :: V -> V)<(std/jsextern/jsobject :: V -> V)<5476>>>))
//                -> @x@0;
//           }), i);
//   match (m@10175) {
//     ((std/core/types/Nothing() : (maybe :: V -> V)<any> ) as @pat@0: ((maybe :: V -> V)<any>))
//        -> std/core/types/Nothing<(std/jsextern/jsobject :: V -> V)<a>>;
//     ((@skip std/core/types/Just((x@0: any) : any) : (maybe :: V -> V)<any> ) as @pat@0@0: ((maybe :: V -> V)<any>))
//        -> std/core/types/Just<(std/jsextern/jsobject :: V -> V)<a>>((std/jsextern/Jsobject<a>(x@0)));
//   };
// },Own)
fun mobjarr/@lift-list@10427 : forall<a> (a : jsarray<maybe<jsobject<a>>>, @uniq-xs@10367 : list<int>) -> list<maybe<jsobject<a>>>
  = forall<a> fn(a: jsarray<maybe<jsobject<a>>>, @uniq-xs@10367: list<int>){
    (match (@uniq-xs@10367) {
      ((std/core/types/Nil() : list<int> ) as @uniq-pat@0@10369: (list<int>))
         -> std/core/types/Nil;
      (@uniq-pat@10370: (list<int>))
         -> std/jsextern/mobjarr/@trmc-lift-list@10428(a, @uniq-xs@10367, (std/core/types/cctx/empty()));
    });
  };
pub fun mobjarr/list : forall<a> (a : jsarray<maybe<jsobject<a>>>) -> list<maybe<jsobject<a>>>
  = forall<a> fn(a: jsarray<maybe<jsobject<a>>>){
    val x@10169 : int
      = std/jsextern/ext/length((match (a) {
        ((@skip std/jsextern/Jsarray((@x: any)) : jsarray<maybe<jsobject<a>>> ) as @pat: (jsarray<maybe<jsobject<a>>>))
           -> @x;
      }));
    val @uniq-xs@10367@10444 : list<int>
      = std/core/list/range/list(0, (std/core/int/int-sub(x@10169, 1)));
    std/jsextern/mobjarr/@lift-list@10427(a, @uniq-xs@10367@10444);
  };
// lifted local: objarr/@lift-list@10429, objarr/list, @spec-x10391
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10386, using:
// @uniq-f@10386 = (fn(i: int){
//   std/jsextern/Jsobject<a>((std/jsextern/any/@index((match (a) {
//       ((@skip std/jsextern/Jsarray((@x@0: any) : any) : (std/jsextern/jsarray :: V -> V)<(std/jsextern/jsobject :: V -> V)<a>> ) as @pat@0: ((std/jsextern/jsarray :: V -> V)<(std/jsextern/jsobject :: V -> V)<5631>>))
//          -> @x@0;
//     }), i)));
// },Own)
fun objarr/@trmc-lift-list@10430 : forall<a> (a : jsarray<jsobject<a>>, @uniq-xs@10385 : list<int>, @acc : ctx<list<jsobject<a>>>) -> list<jsobject<a>>
  = forall<a> fn(a: jsarray<jsobject<a>>, @uniq-xs@10385: list<int>, @acc: ctx<list<jsobject<a>>>){
    (match (@uniq-xs@10385) {
      ((std/core/types/Cons((@uniq-x@10388: int), (@uniq-xx@10389: list<int>)) : list<int> ) as @uniq-pat@10387: (list<int>))
         -> val @trmc-x10465 : jsobject<a>
              = std/jsextern/Jsobject((std/jsextern/any/@index((match (a) {
                  ((@skip std/jsextern/Jsarray((@x@0: any)) : jsarray<jsobject<a>> ) as @pat@0: (jsarray<jsobject<a>>))
                     -> @x@0;
                }), @uniq-x@10388)));
            val @trmc-x10466 : list<jsobject<a>>
              = std/core/types/@cctx-hole-create();
            val @trmc-x10467 : list<jsobject<a>>
              = std/core/types/Cons(@trmc-x10465, @trmc-x10466);
        std/jsextern/objarr/@trmc-lift-list@10430(a, @uniq-xx@10389, (std/core/types/@cctx-extend(@acc, @trmc-x10467, (std/core/types/@field-addr-of(@trmc-x10467, "(\x22std/core/types\x22,\x22\x22,\x22Cons\x22)", "(\x22\x22,\x22\x22,\x22tail\x22)")))));
      ((@skip std/core/types/Nil() : list<int> ) as @uniq-pat@0@10390: (list<int>))
         -> std/core/types/cctx/((++.))(@acc, std/core/types/Nil);
    });
  };
// lifted local: objarr/@lift-list@10429, objarr/list, @spec-x10391
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10386, using:
// @uniq-f@10386 = (fn(i: int){
//   std/jsextern/Jsobject<a>((std/jsextern/any/@index((match (a) {
//       ((@skip std/jsextern/Jsarray((@x@0: any) : any) : (std/jsextern/jsarray :: V -> V)<(std/jsextern/jsobject :: V -> V)<a>> ) as @pat@0: ((std/jsextern/jsarray :: V -> V)<(std/jsextern/jsobject :: V -> V)<5631>>))
//          -> @x@0;
//     }), i)));
// },Own)
fun objarr/@lift-list@10430 : forall<a> (a : jsarray<jsobject<a>>, @uniq-xs@10385 : list<int>) -> list<jsobject<a>>
  = forall<a> fn(a@0: jsarray<jsobject<a>>, @uniq-xs@10385@0: list<int>){
    std/jsextern/objarr/@trmc-lift-list@10430(a@0, @uniq-xs@10385@0, (std/core/types/cctx/empty()));
  };
// lifted local: objarr/list, @spec-x10384
// specialized: std/core/list/map, on parameters @uniq-f@10381, using:
// @uniq-f@10381 = (fn(i: int){
//   std/jsextern/Jsobject<a>((std/jsextern/any/@index((match (a) {
//       ((@skip std/jsextern/Jsarray((@x@0: any) : any) : (std/jsextern/jsarray :: V -> V)<(std/jsextern/jsobject :: V -> V)<a>> ) as @pat@0: ((std/jsextern/jsarray :: V -> V)<(std/jsextern/jsobject :: V -> V)<5631>>))
//          -> @x@0;
//     }), i)));
// },Own)
fun objarr/@lift-list@10429 : forall<a> (a : jsarray<jsobject<a>>, @uniq-xs@10380 : list<int>) -> list<jsobject<a>>
  = forall<a> fn(a: jsarray<jsobject<a>>, @uniq-xs@10380: list<int>){
    (match (@uniq-xs@10380) {
      ((std/core/types/Nil() : list<int> ) as @uniq-pat@0@10382: (list<int>))
         -> std/core/types/Nil;
      (@uniq-pat@10383: (list<int>))
         -> std/jsextern/objarr/@trmc-lift-list@10430(a, @uniq-xs@10380, (std/core/types/cctx/empty()));
    });
  };
pub fun objarr/list : forall<a> (a : jsarray<jsobject<a>>) -> list<jsobject<a>>
  = forall<a> fn(a: jsarray<jsobject<a>>){
    val x@10178 : int
      = std/jsextern/ext/length((match (a) {
        ((@skip std/jsextern/Jsarray((@x: any)) : jsarray<jsobject<a>> ) as @pat: (jsarray<jsobject<a>>))
           -> @x;
      }));
    val @uniq-xs@10380@10446 : list<int>
      = std/core/list/range/list(0, (std/core/int/int-sub(x@10178, 1)));
    std/jsextern/objarr/@lift-list@10429(a, @uniq-xs@10380@10446);
  };
// lifted local: strarray/@lift-list@10431, strarray/list, @spec-x10404
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10399, using:
// @uniq-f@10399 = (fn(i: int){
//   std/jsextern/string/@index((match (a) {
//       ((@skip std/jsextern/Jsarray((@x@0: any) : any) : (std/jsextern/jsarray :: V -> V)<string> ) as @pat@0: ((std/jsextern/jsarray :: V -> V)<string>))
//          -> @x@0;
//     }), i);
// },Own)
fun strarray/@trmc-lift-list@10432 : (a : jsarray<string>, @uniq-xs@10398 : list<int>, @acc : ctx<list<string>>) -> list<string>
  = fn(a: jsarray<string>, @uniq-xs@10398: list<int>, @acc: ctx<list<string>>){
    match (@uniq-xs@10398) {
      ((std/core/types/Cons((@uniq-x@10401: int), (@uniq-xx@10402: list<int>)) : list<int> ) as @uniq-pat@10400: (list<int>))
         -> val @trmc-x10468 : string
              = std/jsextern/string/@index((match (a) {
                  ((@skip std/jsextern/Jsarray((@x@0: any)) : jsarray<string> ) as @pat@0: (jsarray<string>))
                     -> @x@0;
                }), @uniq-x@10401);
            val @trmc-x10469 : list<string>
              = std/core/types/@cctx-hole-create();
            val @trmc-x10470 : list<string>
              = std/core/types/Cons(@trmc-x10468, @trmc-x10469);
        std/jsextern/strarray/@trmc-lift-list@10432(a, @uniq-xx@10402, (std/core/types/@cctx-extend(@acc, @trmc-x10470, (std/core/types/@field-addr-of(@trmc-x10470, "(\x22std/core/types\x22,\x22\x22,\x22Cons\x22)", "(\x22\x22,\x22\x22,\x22tail\x22)")))));
      ((@skip std/core/types/Nil() : list<int> ) as @uniq-pat@0@10403: (list<int>))
         -> std/core/types/cctx/((++.))(@acc, std/core/types/Nil);
    };
  };
// lifted local: strarray/@lift-list@10431, strarray/list, @spec-x10404
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10399, using:
// @uniq-f@10399 = (fn(i: int){
//   std/jsextern/string/@index((match (a) {
//       ((@skip std/jsextern/Jsarray((@x@0: any) : any) : (std/jsextern/jsarray :: V -> V)<string> ) as @pat@0: ((std/jsextern/jsarray :: V -> V)<string>))
//          -> @x@0;
//     }), i);
// },Own)
fun strarray/@lift-list@10432 : (a : jsarray<string>, @uniq-xs@10398 : list<int>) -> list<string>
  = fn(a@0: jsarray<string>, @uniq-xs@10398@0: list<int>){
    std/jsextern/strarray/@trmc-lift-list@10432(a@0, @uniq-xs@10398@0, (std/core/types/cctx/empty()));
  };
// lifted local: strarray/list, @spec-x10397
// specialized: std/core/list/map, on parameters @uniq-f@10394, using:
// @uniq-f@10394 = (fn(i: int){
//   std/jsextern/string/@index((match (a) {
//       ((@skip std/jsextern/Jsarray((@x@0: any) : any) : (std/jsextern/jsarray :: V -> V)<string> ) as @pat@0: ((std/jsextern/jsarray :: V -> V)<string>))
//          -> @x@0;
//     }), i);
// },Own)
fun strarray/@lift-list@10431 : (a : jsarray<string>, @uniq-xs@10393 : list<int>) -> list<string>
  = fn(a: jsarray<string>, @uniq-xs@10393: list<int>){
    match (@uniq-xs@10393) {
      ((std/core/types/Nil() : list<int> ) as @uniq-pat@0@10395: (list<int>))
         -> std/core/types/Nil;
      (@uniq-pat@10396: (list<int>))
         -> std/jsextern/strarray/@trmc-lift-list@10432(a, @uniq-xs@10393, (std/core/types/cctx/empty()));
    };
  };
pub fun strarray/list : (a : jsarray<string>) -> list<string>
  = fn(a: jsarray<string>){
    val x@10185 : int
      = std/jsextern/ext/length((match (a) {
        ((@skip std/jsextern/Jsarray((@x: any)) : jsarray<string> ) as @pat: (jsarray<string>))
           -> @x;
      }));
    val @uniq-xs@10393@10448 : list<int>
      = std/core/list/range/list(0, (std/core/int/int-sub(x@10185, 1)));
    std/jsextern/strarray/@lift-list@10431(a, @uniq-xs@10393@10448);
  };
// lifted local: obj/@lift-entries@10433, obj/entries, @spec-x10417
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10412, using:
// @uniq-f@10412 = (fn(i: int){
//   val jsobj : (std/jsextern/jsarray :: V -> V)<(std/jsextern/jsobject :: V -> V)<any>>;
//   val a@2@10200 : (std/jsextern/jsobject :: V -> V)<any>;
//   val key : string;
//   val value : (std/jsextern/jsobject :: V -> V)<any>;
//   std/core/types/Tuple2<string,(std/jsextern/jsobject :: V -> V)<any>>(key, value);
// },Own)
fun obj/@trmc-lift-entries@10434 : (entries : jsarray<jsarray<jsobject<any>>>, @uniq-xs@10411 : list<int>, @acc : ctx<list<(string, jsobject<any>)>>) -> list<(string, jsobject<any>)>
  = fn(entries: jsarray<jsarray<jsobject<any>>>, @uniq-xs@10411: list<int>, @acc: ctx<list<(string, jsobject<any>)>>){
    match (@uniq-xs@10411) {
      ((std/core/types/Cons((@uniq-x@10414: int), (@uniq-xx@10415: list<int>)) : list<int> ) as @uniq-pat@10413: (list<int>))
         -> val jsobj : jsarray<jsobject<any>>
              = std/jsextern/Jsarray((std/jsextern/any/@index((match (entries) {
                  ((@skip std/jsextern/Jsarray((@x@1: any)) : jsarray<jsarray<jsobject<any>>> ) as @pat@1: (jsarray<jsarray<jsobject<any>>>))
                     -> @x@1;
                }), @uniq-x@10414)));
            val a@2@10200 : jsobject<any>
              = std/jsextern/Jsobject((std/jsextern/any/@index((match (jsobj) {
                  ((@skip std/jsextern/Jsarray((@x@3: any)) : jsarray<jsobject<any>> ) as @pat@3: (jsarray<jsobject<any>>))
                     -> @x@3;
                }), 0)));
            val key : string
              = std/jsextern/ext/unsafe-as-string((match (a@2@10200) {
                ((@skip std/jsextern/Jsobject((@x@2: any)) : jsobject<any> ) as @pat@2: (jsobject<any>))
                   -> @x@2;
              }));
            val value : jsobject<any>
              = std/jsextern/Jsobject((std/jsextern/any/@index((match (jsobj) {
                  ((@skip std/jsextern/Jsarray((@x@4: any)) : jsarray<jsobject<any>> ) as @pat@4: (jsarray<jsobject<any>>))
                     -> @x@4;
                }), 1)));
            val @trmc-x10471 : list<(string, jsobject<any>)>
              = std/core/types/@cctx-hole-create();
            val @trmc-x10472 : list<(string, jsobject<any>)>
              = std/core/types/Cons((std/core/types/Tuple2(key, value)), @trmc-x10471);
        std/jsextern/obj/@trmc-lift-entries@10434(entries, @uniq-xx@10415, (std/core/types/@cctx-extend(@acc, @trmc-x10472, (std/core/types/@field-addr-of(@trmc-x10472, "(\x22std/core/types\x22,\x22\x22,\x22Cons\x22)", "(\x22\x22,\x22\x22,\x22tail\x22)")))));
      ((@skip std/core/types/Nil() : list<int> ) as @uniq-pat@0@10416: (list<int>))
         -> std/core/types/cctx/((++.))(@acc, std/core/types/Nil);
    };
  };
// lifted local: obj/@lift-entries@10433, obj/entries, @spec-x10417
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10412, using:
// @uniq-f@10412 = (fn(i: int){
//   val jsobj : (std/jsextern/jsarray :: V -> V)<(std/jsextern/jsobject :: V -> V)<any>>;
//   val a@2@10200 : (std/jsextern/jsobject :: V -> V)<any>;
//   val key : string;
//   val value : (std/jsextern/jsobject :: V -> V)<any>;
//   std/core/types/Tuple2<string,(std/jsextern/jsobject :: V -> V)<any>>(key, value);
// },Own)
fun obj/@lift-entries@10434 : (entries : jsarray<jsarray<jsobject<any>>>, @uniq-xs@10411 : list<int>) -> list<(string, jsobject<any>)>
  = fn(entries@0: jsarray<jsarray<jsobject<any>>>, @uniq-xs@10411@0: list<int>){
    std/jsextern/obj/@trmc-lift-entries@10434(entries@0, @uniq-xs@10411@0, (std/core/types/cctx/empty()));
  };
// lifted local: obj/entries, @spec-x10410
// specialized: std/core/list/map, on parameters @uniq-f@10407, using:
// @uniq-f@10407 = (fn(i: int){
//   val jsobj : (std/jsextern/jsarray :: V -> V)<(std/jsextern/jsobject :: V -> V)<any>>;
//   val a@2@10200 : (std/jsextern/jsobject :: V -> V)<any>;
//   val key : string;
//   val value : (std/jsextern/jsobject :: V -> V)<any>;
//   std/core/types/Tuple2<string,(std/jsextern/jsobject :: V -> V)<any>>(key, value);
// },Own)
fun obj/@lift-entries@10433 : (entries : jsarray<jsarray<jsobject<any>>>, @uniq-xs@10406 : list<int>) -> list<(string, jsobject<any>)>
  = fn(entries: jsarray<jsarray<jsobject<any>>>, @uniq-xs@10406: list<int>){
    match (@uniq-xs@10406) {
      ((std/core/types/Nil() : list<int> ) as @uniq-pat@0@10408: (list<int>))
         -> std/core/types/Nil;
      (@uniq-pat@10409: (list<int>))
         -> std/jsextern/obj/@trmc-lift-entries@10434(entries, @uniq-xs@10406, (std/core/types/cctx/empty()));
    };
  };
pub fun obj/entries : forall<a> (a : jsobject<a>) -> list<(string, jsobject<any>)>
  = forall<a> fn(a: jsobject<a>){
    val entries : jsarray<jsarray<jsobject<any>>>
      = std/jsextern/Jsarray((std/jsextern/ext/entries((match (a) {
        ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
           -> @x;
      }))));
    val len : int
      = std/jsextern/ext/length((match (entries) {
        ((@skip std/jsextern/Jsarray((@x@0: any)) : jsarray<jsarray<jsobject<any>>> ) as @pat@0: (jsarray<jsarray<jsobject<any>>>))
           -> @x@0;
      }));
    val @uniq-xs@10406@10450 : list<int>
      = std/core/list/range/list(0, (std/core/int/int-sub(len, 1)));
    std/jsextern/obj/@lift-entries@10433(entries, @uniq-xs@10406@10450);
  };
pub fun obj/keys : forall<a> (a : jsobject<a>) -> jsarray<string>
  = forall<a> fn(a: jsobject<a>){
    std/jsextern/Jsarray((std/jsextern/ext/keys((match (a) {
      ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
         -> @x;
    }))));
  };
pub fun obj/values : forall<a,b> (a : jsobject<b>) -> jsarray<a>
  = forall<a,b> fn(a: jsobject<b>){
    std/jsextern/Jsarray((std/jsextern/ext/values((match (a) {
      ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<b> ) as @pat: (jsobject<b>))
         -> @x;
    }))));
  };
pub fun jspromise/@copy : forall<a> (@this : jspromise<a>, internal : ? any) -> jspromise<a>
  = forall<a> fn(@this: jspromise<a>, internal: ? any){
    std/jsextern/Jspromise((match (internal) {
      ((std/core/types/@Optional((@uniq-internal@6205: any)) : ? any ) as @pat: ? any)
         -> @uniq-internal@6205;
      ((@skip std/core/types/@None() : ? any ) as @pat@0: ? any)
         -> (match (@this) {
          ((@skip std/jsextern/Jspromise((@x: any)) : jspromise<a> ) as @pat@1: (jspromise<a>))
             -> @x;
        });
    }));
  };
pub val @tag-JSError : string
  = "std/jsextern/JSError";
// Automatically generated. Tests for the `JSError` constructor of the `:exception-info` type.
pub fip fun is-jserror : (^ exception-info : exception-info) -> bool
  = fn(exception-info: exception-info){
    match (exception-info) {
      ((std/jsextern/JSError((@pat@0: jsobject<any>)) : exception-info ) as @pat: exception-info)
         -> std/core/types/True;
      (@pat@1: exception-info)
         -> std/core/types/False;
    };
  };
pub fun js-promise/resolve : forall<a> (value : jsobject<a>) -> jspromise<a>
  = forall<a> fn(value: jsobject<a>){
    std/jsextern/Jspromise((std/jsextern/any/resolve((match (value) {
      ((@skip std/jsextern/Jsobject((@x: any)) : jsobject<a> ) as @pat: (jsobject<a>))
         -> @x;
    }))));
  };
pub fun js-promise/on-resolve : forall<a,b> (value : jspromise<b>, success : (jsobject<b>) -> io-noexn (), error : (jsobject<a>) -> io-noexn ()) -> io-noexn ()
  = forall<a,b> fn<io-noexn>(value: jspromise<b>, success: (jsobject<b>) -> io-noexn (), error: (jsobject<a>) -> io-noexn ()){
    std/jsextern/any/on-resolve((match (value) {
        ((@skip std/jsextern/Jspromise((@x: any)) : jspromise<b> ) as @pat: (jspromise<b>))
           -> @x;
      }), (fn<io-noexn>(output: any){
        (success((std/jsextern/Jsobject(output))));
      }), (fn<io-noexn>(err: any){
        (error((std/jsextern/Jsobject(err))));
      }));
  };
// monadic lift
fun js-promise/@mlift-wrap@10485 : forall<a> (@y-x10475 : error<jsobject<a>>) -> <std/async/async/async,exn,ndet> jsobject<a>
  = forall<a> fn<<std/async/async/async,exn,ndet>>(@y-x10475: error<jsobject<a>>){
    val i@10502 : hnd/ev-index
      = std/core/types/@make-ssize_t(1);
    val w : hnd/evv<<exn,std/async/async/async,ndet>>
      = std/core/hnd/evv-swap-create1(i@10502);
    val y : jsobject<a>
      = (match (@y-x10475) {
        ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@0: string), (@pat@1@0: exception-info)) : exception ) as exn@0: exception)) : error<jsobject<a>> ) as @pat@1: (error<jsobject<a>>))
           -> val ev@10505 : hnd/ev<exn>
                    = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
          (match (ev@10505) {
            ((@skip std/core/hnd/Ev<e,b>((@pat@0@1: hnd/htag<exn>), (m: hnd/marker<e,b>), (h: exn<e,b>), (@pat@1@1: hnd/evv<e>)) : hnd/ev<exn> ) as @pat@2: (hnd/ev<exn>))
               -> (match ((std/core/exn/throw-exn/@select(h))) {
                ((@skip std/core/hnd/Clause1((f@0: (hnd/marker<e,b>, hnd/ev<exn>, exception) -> e jsobject<a>)) : hnd/clause1<exception,jsobject<a>,exn,e,b> ) as @pat@2@0: (hnd/clause1<exception,jsobject<a>,exn,e,b>))
                   -> f@0(m, ev@10505, exn@0);
              });
          });
        ((@skip std/core/exn/Ok((x@1: jsobject<a>)) : error<jsobject<a>> ) as @pat@2@1: (error<jsobject<a>>))
           -> x@1;
      });
    val _ : ()
      = std/core/hnd/evv-set(w);
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-cont((forall<b> fn<<exn,std/async/async/async,ndet>>(cont: (b) -> <exn,std/async/async/async,ndet> jsobject<a>, res: b){
          std/core/hnd/open-at1(i@10502, cont, res);
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> y;
    });
  };
pub fun js-promise/wrap : forall<a> (promise : jspromise<a>) -> std/async/async/asyncx jsobject<a>
  = forall<a> fn<std/async/async/asyncx>(promise: jspromise<a>){
    val i@10511 : hnd/ev-index
      = std/core/types/@make-ssize_t(0);
    val w : hnd/evv<<std/async/async/async,exn,ndet>>
      = std/core/hnd/evv-swap-create1(i@10511);
    val y : error<jsobject<a>>
      = std/async/async/await-exn((fn<io>(cb: (error<jsobject<a>>) -> io-noexn ()){
        val w@0 : (hnd/evv<<alloc<global>,console/console,div,fsys,ndet,net,read<global>,ui,write<global>,exn>>)
          = (std/core/hnd/evv-swap-create0());
        val x@1 : ()
          = (std/jsextern/any/on-resolve((match (promise) {
              ((@skip std/jsextern/Jspromise((@x: any)) : jspromise<a> ) as @pat@3: (jspromise<a>))
                 -> @x;
            }), (fn<io-noexn>(output: any){
              (cb((std/core/exn/Ok((std/jsextern/Jsobject(output))))));
            }), (fn<io-noexn>(err@0: any){
              (cb((std/core/exn/Error((std/core/exn/Exception("Exception in promise.", (std/jsextern/JSError((std/jsextern/Jsobject(err@0))))))))));
            })));
        val keep : ()
          = (std/core/hnd/evv-set(w@0));
        std/core/types/Nothing;
      }));
    val _ : ()
      = std/core/hnd/evv-set(w);
    val x@10508 : error<jsobject<a>>
      = (match ((std/core/hnd/yielding())) {
        ((std/core/types/True() : bool ) as @pat@1: bool)
           -> std/core/hnd/yield-cont((forall<b> fn<<std/async/async/async,exn,ndet>>(cont: (b) -> <std/async/async/async,exn,ndet> error<jsobject<a>>, res: b){
            std/core/hnd/open-at1(i@10511, cont, res);
          }));
        ((@skip std/core/types/False() : bool ) as @pat@0@0: bool)
           -> y;
      });
    (match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-extend((fn<<std/async/async/async,exn,ndet>>(@y-x10475: error<jsobject<a>>){
          (std/jsextern/js-promise/@mlift-wrap@10485(@y-x10475));
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> val i@0@10518 : (hnd/ev-index == 1 ssize_t)
              = std/core/types/@make-ssize_t(1);
            val w@1 : hnd/evv<<exn,std/async/async/async,ndet>>
              = std/core/hnd/evv-swap-create1(i@0@10518);
            val y@0 : jsobject<a>
              = (match (x@10508) {
                ((std/core/exn/Error(((@skip std/core/exn/Exception((@pat@0@2: string), (@pat@1@0: exception-info)) : exception ) as exn@0: exception)) : error<jsobject<a>> ) as @pat@4: (error<jsobject<a>>))
                   -> val ev@10521 : hnd/ev<exn>
                            = std/core/hnd/@evv-at((std/core/types/@make-ssize_t(0)));
                  (match (ev@10521) {
                    ((@skip std/core/hnd/Ev<e,b>((@pat@0@3: hnd/htag<exn>), (m: hnd/marker<e,b>), (h: exn<e,b>), (@pat@1@1: hnd/evv<e>)) : hnd/ev<exn> ) as @pat@5: (hnd/ev<exn>))
                       -> (match ((std/core/exn/throw-exn/@select(h))) {
                        ((@skip std/core/hnd/Clause1((f@2: (hnd/marker<e,b>, hnd/ev<exn>, exception) -> e jsobject<a>)) : hnd/clause1<exception,jsobject<a>,exn,e,b> ) as @pat@2@0: (hnd/clause1<exception,jsobject<a>,exn,e,b>))
                           -> f@2(m, ev@10521, exn@0);
                      });
                  });
                ((@skip std/core/exn/Ok((x@4: jsobject<a>)) : error<jsobject<a>> ) as @pat@2@1: (error<jsobject<a>>))
                   -> x@4;
              });
            val _ : ()
              = std/core/hnd/evv-set(w@1);
        (match ((std/core/hnd/yielding())) {
          ((std/core/types/True() : bool ) as @pat@2: bool)
             -> std/core/hnd/yield-cont((forall<b> fn<<exn,std/async/async/async,ndet>>(cont@0: (b) -> <exn,std/async/async/async,ndet> jsobject<a>, res@0: b){
              std/core/hnd/open-at1(i@0@10518, cont@0, res@0);
            }));
          ((@skip std/core/types/False() : bool ) as @pat@0@1: bool)
             -> y@0;
        });
    });
  };
// Basics for objects / arrays
pub extern ext/new-obj : () -> any {
  js inline "({})";
};
pub extern ext/new-array : () -> any {
  js inline "([])";
};
pub extern ext/set-null : (a : any, key : string) -> () {
  js inline "#1[#2] = null";
};
pub extern ext/update-null : (a : any, key : string) -> () {
  js inline "{...#1}[#2] = null";
};
pub extern ext/obj/copy : (a : any) -> any {
  js inline "{...#1}";
};
pub extern ext/arr/copy : (a : any) -> any {
  js inline "[...#1]";
};
pub extern ext/show : (a : any) -> string {
  js inline "JSON.stringify(#1)";
};
pub extern ext/is-bool : (a : any) -> bool {
  js inline "typeof #1 === \x27boolean\x27";
};
pub extern ext/is-int : (a : any) -> bool {
  js inline "Number.isInteger(#1)";
};
pub extern ext/is-num : (a : any) -> bool {
  js inline "typeof #1 === \x27number\x27";
};
pub extern ext/is-string : (a : any) -> bool {
  js inline "typeof #1 === \x27string\x27";
};
pub extern any/is-array : (a : any) -> bool {
  js inline "Array.isArray(#1)";
};
// String fields
extern ext/@extern-get-mstring : (a : any, key : string) -> maybe<string> {
  js inline "maybeget(#1, #2)";
};
pub extern ext/get-string : (a : any, key : string) -> string {
  js inline "#1[#2]";
};
pub extern ext/set-string : (a : any, key : string, value : string) -> () {
  js inline "#1[#2] = #3";
};
pub extern ext/update-string : (a : any, key : string, value : string) -> any {
  js inline "{...#1}[#2] = #3";
};
// Bool fields
extern ext/@extern-get-mbool : (a : any, key : string) -> maybe<bool> {
  js inline "maybeget(#1, #2)";
};
pub extern ext/get-bool : (a : any, key : string) -> bool {
  js inline "#1[#2]";
};
pub extern ext/set-bool : (a : any, key : string, value : bool) -> () {
  js inline "#1[#2] = #3";
};
pub extern ext/update-bool : (a : any, key : string, value : bool) -> any {
  js inline "{...#1}[#2] = #3";
};
pub extern ext/field/is-bool : (a : any, key : string) -> bool {
  js inline "typeof #1[#2] === \x27boolean\x27";
};
// Int fields
extern ext/@extern-get-mint : (a : any, key : string) -> maybe<int> {
  js inline "maybeget(#1, #2)";
};
pub extern ext/get-int : (a : any, key : string) -> int {
  js inline "#1[#2]";
};
pub extern ext/set-int : (a : any, key : string, value : int) -> () {
  js inline "#1[#2] = #3";
};
pub extern ext/update-int : (a : any, key : string, value : int) -> any {
  js inline "{...#1}[#2] = #3";
};
pub extern ext/field/is-int : (a : any, key : string) -> bool {
  js inline "Number.isInteger(#1[#2])";
};
// Float fields
extern ext/@extern-get-mfloat : (a : any, key : string) -> maybe<float64> {
  js inline "maybeget(#1, #2)";
};
pub extern ext/get-float : (a : any, key : string) -> float64 {
  js inline "#1[#2]";
};
pub extern ext/set-float : (a : any, key : string, value : float64) -> () {
  js inline "#1[#2] = #3";
};
pub extern ext/update-float : (a : any, key : string, value : float64) -> any {
  js inline "{...#1}[#2] = #3";
};
pub extern ext/field/is-float : (a : any, key : string) -> bool {
  js inline "typeof #1[#2] === \x27number\x27";
};
// Object fields
extern ext/@extern-get-mobj : (a : any, key : string) -> maybe<any> {
  js inline "maybeget(#1, #2)";
};
pub extern ext/get-obj : (a : any, key : string) -> any {
  js inline "#1[#2]";
};
pub extern ext/set-obj : (a : any, key : string, value : any) -> () {
  js inline "#1[#2] = #3";
};
pub extern ext/update-obj : (a : any, key : string, value : any) -> any {
  js inline "{...#1}[#2] = #3";
};
// Misc object operations
pub extern has-key : (a : any, key : string) -> bool {
  js inline "#1[#2] !== undefined";
};
pub extern ext/unsafe-as-string : (a : any) -> string {
  js inline "#1";
};
extern ext/@extern-unsafe-as-int : (a : any) -> int {
  js inline "#1";
};
extern ext/@extern-unsafe-as-float : (a : any) -> float64 {
  js inline "#1";
};
extern ext/@extern-unsafe-as-bool : (a : any) -> bool {
  js inline "#1";
};
// Object operations
// entries returns an array of [key, value] pairs
pub extern ext/entries : (a : any) -> any {
  js inline "Object.entries(#1)";
};
pub extern ext/keys : (a : any) -> any {
  js inline "Object.keys(#1)";
};
pub extern ext/values : (a : any) -> any {
  js inline "Object.values(#1)";
};
// Array operations
pub extern any/@index : (a : any, index : int) -> any {
  js inline "#1[#2]";
};
pub extern many/@index : (a : any, index : int) -> maybe<any> {
  js inline "maybeget(#1, #2)";
};
pub extern string/@index : (a : any, index : int) -> string {
  js inline "#1[#2]";
};
pub extern mstring/@index : (a : any, index : int) -> maybe<string> {
  js inline "maybeget(#1, #2)";
};
pub extern int/@index : (a : any, index : int) -> int {
  js inline "#1[#2]";
};
pub extern mint/@index : (a : any, index : int) -> maybe<int> {
  js inline "maybeget(#1, #2)";
};
pub extern float/@index : (a : any, index : int) -> float64 {
  js inline "#1[#2]";
};
pub extern mfloat/@index : (a : any, index : int) -> maybe<float64> {
  js inline "maybeget(#1, #2)";
};
pub extern bool/@index : (a : any, index : int) -> bool {
  js inline "#1[#2]";
};
pub extern mbool/@index : (a : any, index : int) -> maybe<bool> {
  js inline "maybeget(#1, #2)";
};
pub extern any/@assign : (a : any, index : int, value : any) -> () {
  js inline "#1[#2] = #3";
};
pub extern string/@assign : (a : any, index : int, value : string) -> () {
  js inline "#1[#2] = #3";
};
pub extern int/@assign : (a : any, index : int, value : int) -> () {
  js inline "#1[#2] = #3";
};
pub extern float/@assign : (a : any, index : int, value : float64) -> () {
  js inline "#1[#2] = #3";
};
pub extern bool/@assign : (a : any, index : int, value : bool) -> () {
  js inline "#1[#2] = #3";
};
// More array methods
pub extern ext/length : (a : any) -> int {
  js inline "#1.length";
};
pub extern any/resolve : (value : any) -> any {
  js inline "Promise.resolve(#1)";
};
pub extern any/on-resolve : (promise : any, success : (any) -> io-noexn (), error : (any) -> io-noexn ()) -> io-noexn () {
  js inline "#1.then(#2).catch(#3)";
};
module examples/async/x
import std/time/duration = std/time/duration pub = "";
import std/time/timestamp = std/time/timestamp pub = "";
import std/async/timer = std/async/timer pub = "";
import std/core/types = std/core/types pub = "";
import std/core/hnd = std/core/hnd pub = "";
import std/core/exn = std/core/exn pub = "";
import std/core/bool = std/core/bool pub = "";
import std/core/order = std/core/order pub = "";
import std/core/char = std/core/char pub = "";
import std/core/int = std/core/int pub = "";
import std/core/vector = std/core/vector pub = "";
import std/core/string = std/core/string pub = "";
import std/core/sslice = std/core/sslice pub = "";
import std/core/list = std/core/list pub = "";
import std/core/maybe = std/core/maybe pub = "";
import std/core/maybe2 = std/core/maybe2 pub = "";
import std/core/either = std/core/either pub = "";
import std/core/tuple = std/core/tuple pub = "";
import std/core/lazy = std/core/lazy pub = "";
import std/core/show = std/core/show pub = "";
import std/core/debug = std/core/debug pub = "";
import std/core/delayed = std/core/delayed pub = "";
import std/core/console = std/core/console pub = "";
import std/num/ddouble = std/num/ddouble pub = "";
import std/num/float64 = std/num/float64 pub = "";
import async = async pub = "";
import std/core = std/core = "";
import std/async/async = std/async/async = "";
import std/data/json = std/data/json = "";
import std/jsextern = std/jsextern = "";
// A type alias for asynchronous operations that can raise exceptions non-deterministically.
// This is common for almost all `:async` operations since `cancel` and `timeout` can
// cancel operations non-deterministically which raises the `Cancel` exception and cancels
// outstanding asynchronous requests.
local alias std/async/async/asyncx :: E = <(std/async/async/async :: (E, V) -> V),(exn :: (E, V) -> V),(ndet :: X)> = 1;
pub fun do_fetch : (url : string) -> any
  = fn(url: string){
    examples/async/x/@extern-do_fetch(url);
  };
// monadic lift
fun @mlift-fetch_data@10179 : forall<_a> (@y-x10152 : std/jsextern/jsobject<_a>) -> std/async/async/asyncx string
  = forall<_a> fn<std/async/async/asyncx>(@y-x10152: std/jsextern/jsobject<_a>){
    val w : hnd/evv<<std/async/async/async,exn,ndet>>
      = std/core/hnd/evv-swap-create0();
    val x : string
      = std/jsextern/ext/unsafe-as-string((match (@y-x10152) {
        ((@skip std/jsextern/Jsobject((@x: any)) : std/jsextern/jsobject<_a> ) as @pat: (std/jsextern/jsobject<_a>))
           -> @x;
      }));
    val keep : ()
      = std/core/hnd/evv-set(w);
    x;
  };
pub fun fetch_data : (url : string) -> <std/async/async/async,exn,ndet> string
  = fn<std/async/async/asyncx>(url: string){
    val x : std/jsextern/jsobject<_a>
          = std/jsextern/js-promise/wrap((std/jsextern/Jspromise((std/core/hnd/@open-none1(examples/async/x/do_fetch, url)))));
    match ((std/core/hnd/yielding())) {
      ((std/core/types/True() : bool ) as @pat: bool)
         -> std/core/hnd/yield-extend((fn<(std/async/async/asyncx == 1 <std/async/async/async,exn,ndet>)>(@y-x10152: std/jsextern/jsobject<_42>){
          (examples/async/x/@mlift-fetch_data@10179(@y-x10152));
        }));
      ((@skip std/core/types/False() : bool ) as @pat@0: bool)
         -> val w : hnd/evv<<std/async/async/async,exn,ndet>>
              = std/core/hnd/evv-swap-create0();
            val x@0 : string
              = std/jsextern/ext/unsafe-as-string((match (x) {
                ((@skip std/jsextern/Jsobject((@x: any)) : std/jsextern/jsobject<_a> ) as @pat@1: (std/jsextern/jsobject<_42>))
                   -> @x;
              }));
            val keep : ()
              = std/core/hnd/evv-set(w);
        x@0;
    };
  };
pub fun do_parse : forall<a> (input : string) -> std/jsextern/jsobject<a>
  = forall<a> fn(input: string){
    examples/async/x/@extern-do_parse(input);
  };
// lifted local: convert, @spec-x10122
// specialized: std/core/list/map, on parameters @uniq-f@10119, using:
// @uniq-f@10119 = (fn<(div :: X)>(x: (std/jsextern/jsobject :: V -> V)<_149>){
//   examples/async/x/convert<_a>(x, (std/core/types/@Optional<int>((std/core/int/int-add((match (depth) {
//         ((std/core/types/@Optional((@uniq-depth@91: int) : int) : ? int ) as @pat: ? int)
//            -> @uniq-depth@91;
//         ((@skip std/core/types/@None() : ? int ) as @pat@0: ? int)
//            -> 0;
//       }), 1)))));
// },Own)
fun @lift-convert@10144 : forall<_a> (depth : ? int, @uniq-xs@10118 : list<std/jsextern/jsobject<_a>>) -> div list<std/data/json/json>
  = forall<_a> fn<div>(depth: ? int, @uniq-xs@10118: list<std/jsextern/jsobject<_a>>){
    (match (@uniq-xs@10118) {
      ((std/core/types/Nil() : list<std/jsextern/jsobject<_a>> ) as @uniq-pat@0@10120: (list<std/jsextern/jsobject<_a>>))
         -> std/core/types/Nil;
      (@uniq-pat@10121: (list<std/jsextern/jsobject<_a>>))
         -> examples/async/x/@lift-convert@10145(depth, @uniq-xs@10118);
    });
  };
// lifted local: convert, @spec-x10135
// specialized: std/core/list/map, on parameters @uniq-f@10132, using:
// @uniq-f@10132 = (fn<(div :: X)>(@pat-x41_15: (string, (std/jsextern/jsobject :: V -> V)<any>)){
//   match (@pat-x41_15) {
//     ((@skip std/core/types/Tuple2((k: string) : string, (v: (std/jsextern/jsobject :: V -> V)<any>) : (std/jsextern/jsobject :: V -> V)<any>) : (string, (std/jsextern/jsobject :: V -> V)<any>) ) as @pat@11@0: (string, (std/jsextern/jsobject :: V -> V)<any>))
//        -> std/core/types/Tuple2<string,std/data/json/json>(k, (examples/async/x/convert<any>(v, (std/core/types/@Optional<int>((std/core/int/int-add((match (depth) {
//               ((std/core/types/@Optional((@uniq-depth@91: int) : int) : ? int ) as @pat: ? int)
//                  -> @uniq-depth@91;
//               ((@skip std/core/types/@None() : ? int ) as @pat@0: ? int)
//                  -> 0;
//             }), 1)))))));
//   };
// },Own)
fun @lift-convert@10146 : (depth : ? int, @uniq-xs@10131 : list<(string, std/jsextern/jsobject<any>)>) -> div list<(string, std/data/json/json)>
  = fn<div>(depth: ? int, @uniq-xs@10131: list<(string, std/jsextern/jsobject<any>)>){
    match (@uniq-xs@10131) {
      ((std/core/types/Nil() : list<(string, std/jsextern/jsobject<any>)> ) as @uniq-pat@0@10133: (list<(string, std/jsextern/jsobject<any>)>))
         -> std/core/types/Nil;
      (@uniq-pat@10134: (list<(string, std/jsextern/jsobject<any>)>))
         -> examples/async/x/@lift-convert@10147(depth, @uniq-xs@10131);
    };
  };
// lifted local: @lift-convert@10144, convert, @spec-x10129
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10124, using:
// @uniq-f@10124 = (fn<(div :: X)>(x: (std/jsextern/jsobject :: V -> V)<_149>){
//   examples/async/x/convert<_a>(x, (std/core/types/@Optional<int>((std/core/int/int-add((match (depth) {
//         ((std/core/types/@Optional((@uniq-depth@91: int) : int) : ? int ) as @pat: ? int)
//            -> @uniq-depth@91;
//         ((@skip std/core/types/@None() : ? int ) as @pat@0: ? int)
//            -> 0;
//       }), 1)))));
// },Own)
fun @lift-convert@10145 : forall<_a> (depth : ? int, @uniq-xs@10123 : list<std/jsextern/jsobject<_a>>) -> div list<std/data/json/json>
  = forall<_a> fn<div>(depth: ? int, @uniq-xs@10123: list<std/jsextern/jsobject<_a>>){
    (match (@uniq-xs@10123) {
      ((std/core/types/Cons((@uniq-x@10126: std/jsextern/jsobject<_a>), (@uniq-xx@10127: list<std/jsextern/jsobject<_a>>)) : list<std/jsextern/jsobject<_a>> ) as @uniq-pat@10125: (list<std/jsextern/jsobject<_a>>))
         -> std/core/types/Cons((examples/async/x/convert(@uniq-x@10126, (std/core/types/@Optional((std/core/int/int-add((match (depth) {
                ((std/core/types/@Optional((@uniq-depth@91: int)) : ? int ) as @pat: ? int)
                   -> @uniq-depth@91;
                ((@skip std/core/types/@None() : ? int ) as @pat@0: ? int)
                   -> 0;
              }), 1)))))), (examples/async/x/@lift-convert@10145(depth, @uniq-xx@10127)));
      ((@skip std/core/types/Nil() : list<std/jsextern/jsobject<_a>> ) as @uniq-pat@0@10128: (list<std/jsextern/jsobject<_a>>))
         -> std/core/types/Nil;
    });
  };
// lifted local: @lift-convert@10146, convert, @spec-x10142
// specialized: std/core/list/@unroll-map@10010, on parameters @uniq-f@10137, using:
// @uniq-f@10137 = (fn<(div :: X)>(@pat-x41_15: (string, (std/jsextern/jsobject :: V -> V)<any>)){
//   match (@pat-x41_15) {
//     ((@skip std/core/types/Tuple2((k: string) : string, (v: (std/jsextern/jsobject :: V -> V)<any>) : (std/jsextern/jsobject :: V -> V)<any>) : (string, (std/jsextern/jsobject :: V -> V)<any>) ) as @pat@11@0: (string, (std/jsextern/jsobject :: V -> V)<any>))
//        -> std/core/types/Tuple2<string,std/data/json/json>(k, (examples/async/x/convert<any>(v, (std/core/types/@Optional<int>((std/core/int/int-add((match (depth) {
//               ((std/core/types/@Optional((@uniq-depth@91: int) : int) : ? int ) as @pat: ? int)
//                  -> @uniq-depth@91;
//               ((@skip std/core/types/@None() : ? int ) as @pat@0: ? int)
//                  -> 0;
//             }), 1)))))));
//   };
// },Own)
fun @lift-convert@10147 : (depth : ? int, @uniq-xs@10136 : list<(string, std/jsextern/jsobject<any>)>) -> div list<(string, std/data/json/json)>
  = fn<div>(depth@0: ? int, @uniq-xs@10136: list<(string, std/jsextern/jsobject<any>)>){
    match (@uniq-xs@10136) {
      ((std/core/types/Cons((@uniq-x@10139: (string, std/jsextern/jsobject<any>)), (@uniq-xx@10140: list<(string, std/jsextern/jsobject<any>)>)) : list<(string, std/jsextern/jsobject<any>)> ) as @uniq-pat@10138: (list<(string, std/jsextern/jsobject<any>)>))
         -> std/core/types/Cons((match (@uniq-x@10139) {
            ((@skip std/core/types/Tuple2((k: string), (v: std/jsextern/jsobject<any>)) : (string, std/jsextern/jsobject<any>) ) as @pat@11@0: (string, std/jsextern/jsobject<any>))
               -> std/core/types/Tuple2(k, (examples/async/x/convert(v, (std/core/types/@Optional((std/core/int/int-add((match (depth@0) {
                      ((std/core/types/@Optional((@uniq-depth@91@0: int)) : ? int ) as @pat@12: ? int)
                         -> @uniq-depth@91@0;
                      ((@skip std/core/types/@None() : ? int ) as @pat@0@1: ? int)
                         -> 0;
                    }), 1)))))));
          }), (examples/async/x/@lift-convert@10147(depth@0, @uniq-xx@10140)));
      ((@skip std/core/types/Nil() : list<(string, std/jsextern/jsobject<any>)> ) as @uniq-pat@0@10141: (list<(string, std/jsextern/jsobject<any>)>))
         -> std/core/types/Nil;
    };
  };
pub fun convert : forall<a> (input : std/jsextern/jsobject<a>, depth : ? int) -> div std/data/json/json
  = forall<a> fn<div>(input: std/jsextern/jsobject<a>, depth@1: ? int){
    (match ((std/jsextern/any/is-array((match (input) {
      ((@skip std/jsextern/Jsobject((@x: any)) : std/jsextern/jsobject<a> ) as @pat@1: (std/jsextern/jsobject<a>))
         -> @x;
    })))) {
      ((std/core/types/True() : bool ) as @pat@1@0: bool)
         -> val @uniq-xs@10118@10150 : list<std/jsextern/jsobject<_b>>
                  = std/jsextern/objarr/list((std/jsextern/Jsarray((match (input) {
                    ((@skip std/jsextern/Jsobject((@x@0: any)) : std/jsextern/jsobject<a> ) as @pat@2: (std/jsextern/jsobject<a>))
                       -> @x@0;
                  }))));
        std/data/json/JSList((examples/async/x/@lift-convert@10144(depth@1, @uniq-xs@10118@10150)));
      ((@skip std/core/types/False() : bool ) as @pat@2@0: bool)
         -> (match ((std/jsextern/ext/is-string((match (input) {
          ((@skip std/jsextern/Jsobject((@x@1: any)) : std/jsextern/jsobject<a> ) as @pat@3: (std/jsextern/jsobject<a>))
             -> @x@1;
        })))) {
          ((std/core/types/True() : bool ) as @pat@3@0: bool)
             -> std/data/json/JSString((std/jsextern/ext/unsafe-as-string((match (input) {
              ((@skip std/jsextern/Jsobject((@x@2: any)) : std/jsextern/jsobject<a> ) as @pat@4: (std/jsextern/jsobject<a>))
                 -> @x@2;
            }))));
          ((@skip std/core/types/False() : bool ) as @pat@4@0: bool)
             -> (match ((std/jsextern/ext/is-int((match (input) {
              ((@skip std/jsextern/Jsobject((@x@3: any)) : std/jsextern/jsobject<a> ) as @pat@5: (std/jsextern/jsobject<a>))
                 -> @x@3;
            })))) {
              ((std/core/types/True() : bool ) as @pat@5@0: bool)
                 -> std/data/json/JSInt((std/jsextern/ext/unsafe-as-int((match (input) {
                  ((@skip std/jsextern/Jsobject((@x@4: any)) : std/jsextern/jsobject<a> ) as @pat@6: (std/jsextern/jsobject<a>))
                     -> @x@4;
                }))));
              ((@skip std/core/types/False() : bool ) as @pat@6@0: bool)
                 -> (match ((std/jsextern/ext/is-num((match (input) {
                  ((@skip std/jsextern/Jsobject((@x@5: any)) : std/jsextern/jsobject<a> ) as @pat@7: (std/jsextern/jsobject<a>))
                     -> @x@5;
                })))) {
                  ((std/core/types/True() : bool ) as @pat@7@0: bool)
                     -> std/data/json/JSNum((std/jsextern/ext/unsafe-as-float((match (input) {
                      ((@skip std/jsextern/Jsobject((@x@6: any)) : std/jsextern/jsobject<a> ) as @pat@8: (std/jsextern/jsobject<a>))
                         -> @x@6;
                    }))));
                  ((@skip std/core/types/False() : bool ) as @pat@8@0: bool)
                     -> (match ((std/jsextern/ext/is-bool((match (input) {
                      ((@skip std/jsextern/Jsobject((@x@7: any)) : std/jsextern/jsobject<a> ) as @pat@9: (std/jsextern/jsobject<a>))
                         -> @x@7;
                    })))) {
                      ((std/core/types/True() : bool ) as @pat@9@0: bool)
                         -> std/data/json/JSBool((std/jsextern/ext/unsafe-as-bool((match (input) {
                          ((@skip std/jsextern/Jsobject((@x@8: any)) : std/jsextern/jsobject<a> ) as @pat@10: (std/jsextern/jsobject<a>))
                             -> @x@8;
                        }))));
                      ((@skip std/core/types/False() : bool ) as @pat@10@0: bool)
                         -> val entries : std/jsextern/jsarray<std/jsextern/jsarray<std/jsextern/jsobject<any>>>
                              = std/jsextern/Jsarray((std/jsextern/ext/entries((match (input) {
                                ((@skip std/jsextern/Jsobject((@x@9: any)) : std/jsextern/jsobject<a> ) as @pat@11: (std/jsextern/jsobject<a>))
                                   -> @x@9;
                              }))));
                            val len : int
                              = std/jsextern/ext/length((match (entries) {
                                ((@skip std/jsextern/Jsarray((@x@0@0: any)) : std/jsextern/jsarray<std/jsextern/jsarray<std/jsextern/jsobject<any>>> ) as @pat@0@0: (std/jsextern/jsarray<std/jsextern/jsarray<std/jsextern/jsobject<any>>>))
                                   -> @x@0@0;
                              }));
                            val @uniq-xs@10406@10450 : list<int>
                              = std/core/list/range/list(0, (std/core/int/int-sub(len, 1)));
                            val @uniq-xs@10131@10151 : list<(string, std/jsextern/jsobject<any>)>
                              = (match (@uniq-xs@10406@10450) {
                                ((std/core/types/Nil() : list<int> ) as @uniq-pat@0@10408: (list<int>))
                                   -> std/core/types/Nil;
                                (@uniq-pat@10409: (list<int>))
                                   -> std/jsextern/obj/@lift-entries@10434(entries, @uniq-xs@10406@10450);
                              });
                        std/data/json/JSObj((examples/async/x/@lift-convert@10146(depth@1, @uniq-xs@10131@10151)));
                    });
                });
            });
        });
    });
  };
pub fun parse : (input : string) -> div std/data/json/json
  = fn<div>(input: string){
    examples/async/x/convert((examples/async/x/do_parse(input)), std/core/types/@None);
  };
// monadic lift
fun @mlift-main@10180 : forall<_a,_b> (@y-x10156 : std/jsextern/jsobject<_a>) -> std/async/async/asyncx ()
  = forall<_a,_b> fn<std/async/async/asyncx>(@y-x10156: std/jsextern/jsobject<_a>){
    val w : hnd/evv<<std/async/async/async,exn,ndet>>
      = std/core/hnd/evv-swap-create0();
    val x : string
      = std/jsextern/ext/unsafe-as-string((match (@y-x10156) {
        ((@skip std/jsextern/Jsobject((@x@0: any)) : std/jsextern/jsobject<_a> ) as @pat@4: (std/jsextern/jsobject<_a>))
           -> @x@0;
      }));
    val keep : ()
      = std/core/hnd/evv-set(w);
    val w@0 : hnd/evv<<div,std/async/async/async,exn,ndet>>
      = std/core/hnd/evv-swap-create0();
    val x@0 : std/data/json/json
      = examples/async/x/convert((examples/async/x/do_parse(x)), std/core/types/@None);
    val keep@0 : ()
      = std/core/hnd/evv-set(w@0);
    val w@1 : hnd/evv<<div,std/async/async/async,exn,ndet>>
      = std/core/hnd/evv-swap-create0();
    val x@1 : ()
      = (match ((std/core/types/ref/(!)(std/core/debug/trace-enabled, std/core/types/@Hnodiv))) {
        ((std/core/types/True() : bool ) as @pat@5: bool)
           -> std/core/debug/xtrace("json loaded");
        ((@skip std/core/types/False() : bool ) as @pat@0@3: bool)
           -> std/core/types/Unit;
      });
    val keep@1 : ()
      = std/core/hnd/evv-set(w@1);
    x@1;
  };
pub fun main : () -> <std/async/async/async,div,ndet> ()
  = fn<<std/async/async/async,div,ndet>>(){
    std/core/exn/exn/@handle((std/core/exn/@Hnd-exn(0, (forall<a> std/core/hnd/Clause1((fn<<std/async/async/async,div,ndet>>(m: hnd/marker<<std/async/async/async,div,ndet>,()>, @_wildcard-x653_16: hnd/ev<exn>, x: exception){
          (std/core/hnd/yield-to-final(m, (fn<<std/async/async/async,div,ndet>>(@_wildcard-x653_45: (hnd/resume-result<a,()>) -> <std/async/async/async,div,ndet> ()){
              val w : (hnd/evv<<std/async/async/async,div,ndet>>)
                = (std/core/hnd/evv-swap-create0());
              val keep : ()
                = (std/core/hnd/evv-set(w));
              val @x-x1@10171 : string
                = (std/core/types/(++)("Error occurred ", (match (x) {
                    ((@skip std/core/exn/Exception((@x: string), (@pat@0@0: exception-info)) : exception ) as @pat@1: exception)
                       -> @x;
                  })));
              val w@0 : (hnd/evv<<std/async/async/async,div,ndet>>)
                = (std/core/hnd/evv-swap-create0());
              val x@1 : ()
                = (match ((std/core/types/ref/(!)(std/core/debug/trace-enabled, std/core/types/@Hnodiv))) {
                  ((std/core/types/True() : bool ) as @pat: bool)
                     -> std/core/debug/xtrace(@x-x1@10171);
                  ((@skip std/core/types/False() : bool ) as @pat@0: bool)
                     -> std/core/types/Unit;
                });
              val keep@0 : ()
                = (std/core/hnd/evv-set(w@0));
              x@1;
            })));
        }))))), (fn<<std/async/async/async,div,ndet>>(@res: ()){
        @res;
      }), (fn<<exn,std/async/async/async,div,ndet>>(){
        val w@1 : (hnd/evv<<std/async/async/async,div,exn,ndet>>)
          = (std/core/hnd/evv-swap-create0());
        val x@2 : ()
          = (match ((std/core/types/ref/(!)(std/core/debug/trace-enabled, std/core/types/@Hnodiv))) {
            ((std/core/types/True() : bool ) as @pat@2: bool)
               -> std/core/debug/xtrace("Loading...");
            ((@skip std/core/types/False() : bool ) as @pat@0@1: bool)
               -> std/core/types/Unit;
          });
        val keep@1 : ()
          = (std/core/hnd/evv-set(w@1));
        val w@2 : (hnd/evv<<std/async/async/async,div,exn,ndet>>)
          = (std/core/hnd/evv-swap-create0());
        val x@3 : ()
          = (match ((std/core/types/ref/(!)(std/core/debug/trace-enabled, std/core/types/@Hnodiv))) {
            ((std/core/types/True() : bool ) as @pat@3: bool)
               -> std/core/debug/xtrace("loading json...");
            ((@skip std/core/types/False() : bool ) as @pat@0@2: bool)
               -> std/core/types/Unit;
          });
        val keep@2 : ()
          = (std/core/hnd/evv-set(w@2));
        val w@3 : (hnd/evv<<std/async/async/async,exn,ndet>>)
          = (std/core/hnd/evv-swap-create0());
        val x@4 : any
          = (examples/async/x/do_fetch("data/index.json"));
        val keep@3 : ()
          = (std/core/hnd/evv-set(w@3));
        val x@4@10200 : (std/jsextern/jsobject<_a>)
          = (std/jsextern/js-promise/wrap((std/jsextern/Jspromise(x@4))));
        (match ((std/core/hnd/yielding())) {
          ((std/core/types/True() : bool ) as @pat@4: bool)
             -> std/core/hnd/yield-extend((fn<(std/async/async/asyncx == 1 <std/async/async/async,exn,ndet>)>(@y-x10156: std/jsextern/jsobject<_42>){
              (examples/async/x/@mlift-main@10180(@y-x10156));
            }));
          ((@skip std/core/types/False() : bool ) as @pat@0@3: bool)
             -> examples/async/x/@mlift-main@10180(x@4@10200);
        });
      }));
  };
extern @extern-do_fetch : (url : string) -> any {
  js inline "fetch(#1).then(r => r.ok ? r.text() : Promise.reject(r.statusText))";
};
extern @extern-do_parse : forall<a> (input : string) -> std/jsextern/jsobject<a> {
  js inline "JSON.parse(#1)";
};
module examples/async/x/@main
import std/num/int32 = std/num/int32 pub = "";
import std/time/date = std/time/date pub = "";
import std/os/env = std/os/env pub = "";
import std/text/parse = std/text/parse pub = "";
import std/os/dir = std/os/dir pub = "";
import std/time/duration = std/time/duration pub = "";
import std/time/timestamp = std/time/timestamp pub = "";
import std/num/int64 = std/num/int64 pub = "";
import std/pretty/printer = std/pretty/printer pub = "";
import std/os/path = std/os/path pub = "";
import std/os/file = std/os/file pub = "";
import std/core-extras = std/core-extras pub = "";
import std/async/timer = std/async/timer pub = "";
import std/core/undiv = std/core/undiv pub = "";
import std/pretty/pprint = std/pretty/pprint pub = "";
import async = async pub = "";
import std/core/types = std/core/types pub = "";
import std/core/hnd = std/core/hnd pub = "";
import std/core/exn = std/core/exn pub = "";
import std/core/bool = std/core/bool pub = "";
import std/core/order = std/core/order pub = "";
import std/core/char = std/core/char pub = "";
import std/core/int = std/core/int pub = "";
import std/core/vector = std/core/vector pub = "";
import std/core/string = std/core/string pub = "";
import std/core/sslice = std/core/sslice pub = "";
import std/core/list = std/core/list pub = "";
import std/core/maybe = std/core/maybe pub = "";
import std/core/maybe2 = std/core/maybe2 pub = "";
import std/core/either = std/core/either pub = "";
import std/core/tuple = std/core/tuple pub = "";
import std/core/lazy = std/core/lazy pub = "";
import std/core/show = std/core/show pub = "";
import std/core/debug = std/core/debug pub = "";
import std/core/delayed = std/core/delayed pub = "";
import std/core/console = std/core/console pub = "";
import std/data/json = std/data/json pub = "";
import std/jsextern = std/jsextern pub = "";
import std/num/ddouble = std/num/ddouble pub = "";
import std/num/float64 = std/num/float64 pub = "";
import std/core = std/core = "";
import examples/async/x = examples/async/x = "";
import std/async/async = std/async/async = "";
// Stateful functions can manipulate heap `:h` using allocations, reads and writes.
local alias st<(h :: H)> :: H -> E = <(read :: H -> X)<(h :: H)>,(write :: H -> X)<(h :: H)>,(alloc :: H -> X)<(h :: H)>> = 1;
pub fun @expr : () -> <std/async/async/async,div,ndet> ()
  = fn<<std/async/async/async,div,ndet>>(){
    examples/async/x/main();
  };
pub fun @main : () -> <st<global>,console/console,div,fsys,ndet,net,ui> ()
  = fn<io-noexn>(){
    std/async/async/async/handle(examples/async/x/main);
  };
linking : examples/async/x/@main
created : .koka/v3.2.2/js-drelease-48dfe2/index.html
