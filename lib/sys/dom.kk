/*----------------------------------------------------------------------------
   Copyright 2012-2021, Microsoft Research, Daan Leijen.

   Licensed under the Apache License, Version 2.0 ("The Licence"). You may not
   use this file except in compliance with the License. A copy of the License
   can be found in the LICENSE file at the root of this distribution.
----------------------------------------------------------------------------*/

// Utility function to access the DOM inside a browser.
module sys/dom
import sys/dom/types

inline extern applyWindow( action: (window) -> <dom|e> () ): <dom|e> bool
  js inline "(typeof window !== 'undefined' ? (function(){ (#1)(window); return true; })() : false)"

// Execute an action that gains access to the global ":window" object.
pub fun withWindow( action: (window) -> <dom|e> () ): <dom|e> ()
  val success = applyWindow(action)
  if (!success) then throw("this application can only run inside a browser") else ()


// Execute an action after a specified time out.
pub inline extern timeout( msecs: int, action: () -> <dom|e> () ): <dom|e> ()
  js inline "window.setTimeout(#2,#1)"

// Execute an action on a specified interval.
pub inline extern interval( msecs: int, action: () -> <dom|e> () ): <dom|e> ()
  js inline "window.setInterval(#2,#1)"
