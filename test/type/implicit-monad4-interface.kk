// PROBLEM WITHOUT INTERFACES - ambiguity in implicit parameters

fun test1()
  // previously ambiguous: `monad_maybe` or `monad_monadplus(monadplus_maybe)`
  // Ambiguity resolved if monadplus is a extended type of the monad interface 
  //   - We could use the base, since we don't need additional fields
  //     - might be tricky since is the refinement introducing different behavior or just new fields?
  //     - refined type might be more efficient if using proposal V3
  //     - still able to manually resolve to a different instance using explicit parameters
  //     - Can provide hover information on which instance is being used at any particular call site, or inlay hints
  match [Just(1), Just(2)].sequence(?monad=monad_maybe)  
    Just(xs) -> xs.show
    Nothing  -> "Nothing"


// -------------------------------------------
// Interfaces V1
// -------------------------------------------
open type monad<m>
  interface Monad
    // All extensions of the monad<m> type must have these required fields
    // Accessors are generated for these fields since they are required (and will always be present)
    //  - This means that runtime will have to have a table lookup or agree on layout
    //  - This proposal does not support multiple interfaces / mixins to avoid that problem (can just use layout as first fields)

    // Should there be an interface keyword for the constructor, or should the fields just be marked as required?
    pure : forall<a> a -> m<a>
    bind : forall<a,b> (m<a>, a -> m<b>) -> m<b>

extend type monad<m>
  Monadplus
    // Mixes in the monad fields since they are required
    //
    // Questions? 
    //   - Should the mixed in fields be automatically added or should they be required to be explicitly added?
    //   - Can we just allow the names of the fields?
    //   - Can a mixed in field be overridden? (to a refinement of an interface type?)
    plus  : forall<a> (m<a>,m<a>) -> m<a>

// PROS:
//  - No runtime overhead for accessing fields
//  - Consistent runtime layout
//  - Little change to the surface syntax
//  - No change to typechecking

// CONS:
//  - No support for multiple interfaces / mixins
//  - What happens if there are multiple constructors defined in the interface type?


// -------------------------------------------
// Interfaces V2 - V1 with alternate syntax
// -------------------------------------------
interface type monad-base<m>
  pure : forall<a> a -> m<a>
  bind : forall<a,b> (m<a>, a -> m<b>) -> m<b>
  // Desugars to the above (just limiting to a single set of fields)

extend type monad-base<m>
  Monad() // Doesn't add anything to monad-base

extend type monad-base<m>
  MonadPlus(plus: forall<a> (m<a>,m<a>) -> m<a>)

// PROS: 
//  - Same as above
//  - More explicit syntax for interfaces, supporting only a single set of fields without types

// CONS:
//  - More verbose for a constructable base type 
//    - Not terrible though unless you have to repeat fields 
//        (should at least support omitting types for inherited fields)
//  - Still no support for multiple interfaces / mixins

// -------------------------------------------
// Interfaces V3 - Support for multiple interfaces / mixins
// -------------------------------------------

open type monad<m> // Or the alternate syntax from V2
   interface Monad
      // All extensions of monad<m> must have these required fields
      pure : forall<a> a -> m<a>
      bind : forall<a,b> (m<a>, a -> m<b>) -> m<b>

type monadplus<m> // Not defining an extension type here!
  Monadplus implements monad<m> // Constructors can implement multiple interfaces
    // Mixes in the monad params since they are required
    plus  : forall<a> (m<a>,m<a>) -> m<a>
    // Also generates an extension to the monad<m> type called ".monad_monadplus"
    //   with a constructor by the name Monadplus (yes it is ambiguous)
    // Typechecking of the constructor always determines that it is the more specific type (monadplus)
    //   but inserts a runtime coercion in two places:
    //   - to the general monad<m> type 
    //     - when passed to a function expecting that type or expecting an implicit parameter of the general type
    //     - it unifies if in a match statement with other monad<m> types, but not monadplus<m> types
    //   - from the general monad<m> type to the more specific
    //     - when in a match statement and the constructor is matched against
    //     - i.e.
    //       match m
    //         Monadplus(pure, bind, plus) -> m is promoted/runtime coerced to monadplus<m> in this body

// PROS:
//  - This approach allows for multiple interfaces / multiple mixins
//  - No runtime overhead for accessing fields - coercion is where you pay the cost
//  - Constructors individually can choose what they implement

// CONS:
//  - Runtime overhead in match statements / function calls
//    - Could be alleviated: 
//        make them isomorphic in field memory layout if there is a single interface 
//        only pay the coercion cost when:
//          - a single type has constructors that implement different interfaces 
//          - a single constructor implements several interfaces