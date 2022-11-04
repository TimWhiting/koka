/*----------------------------------------------------------------------------
   Copyright 2012-2021, Microsoft Research, Daan Leijen.

   Licensed under the Apache License, Version 2.0 ("The Licence"). You may not
   use this file except in compliance with the License. A copy of the License
   can be found in the LICENSE file at the root of this distribution.
----------------------------------------------------------------------------*/

// Utility function to access the DOM inside a browser.
module std/sys/dom

pub import std/sys/dom/anonXmlHttpRequest
pub import std/sys/dom/attr
pub import std/sys/dom/booleanArray
pub import std/sys/dom/byteArray
pub import std/sys/dom/caretPosition
pub import std/sys/dom/characterData
pub import std/sys/dom/comment
pub import std/sys/dom/document
pub import std/sys/dom/documentFragment
pub import std/sys/dom/documentType
pub import std/sys/dom/domElementMap
pub import std/sys/dom/domImplementation
pub import std/sys/dom/domSettableTokenList
pub import std/sys/dom/domStringList
pub import std/sys/dom/domStringMap
pub import std/sys/dom/domTokenList
pub import std/sys/dom/doubleArray
pub import std/sys/dom/element
pub import std/sys/dom/floatArray
pub import std/sys/dom/formData
pub import std/sys/dom/longArray
pub import std/sys/dom/longLongArray
pub import std/sys/dom/node
pub import std/sys/dom/nodeList
pub import std/sys/dom/octetArray
pub import std/sys/dom/processingInstruction
pub import std/sys/dom/shortArray
pub import std/sys/dom/text
pub import std/sys/dom/types
pub import std/sys/dom/unsignedByteArray
pub import std/sys/dom/unsignedLongArray
pub import std/sys/dom/unsignedLongLongArray
pub import std/sys/dom/unsignedShortArray
pub import std/sys/dom/xmlHttpRequest
pub import std/sys/dom/xmlHttpRequestEventTarget
pub import std/sys/dom/xmlHttpRequestUpload
pub import std/sys/dom/html/window
pub import std/sys/dom/html/htmlElement
pub import std/sys/dom/html/htmlCanvasElement
pub import std/sys/dom/html/canvasRenderingContext2d
pub import std/sys/dom/html/htmlDivElement
pub import std/sys/dom/html/htmlSpanElement
pub import std/sys/dom/html/htmlInputElement
pub import std/sys/dom/html/htmlTextAreaElement
pub import std/sys/dom/html/htmlTableElement
pub import std/sys/dom/html/htmlTableRowElement
pub import std/sys/dom/html/htmlTableDataCellElement
pub import std/sys/dom/css/cssStyleDeclaration

// Execute an action that gains access to the global ":window" object.
pub fun withWindow( action: (window) -> <dom|e> () ) : <dom|e> ()
{
  val success = applyWindow(action);
  if (!success) then throw("this application can only run inside a browser")
  else () 
}

extern applyWindow : forall<e> ( action: (window) -> <dom|e> () ) -> <dom|e> bool {
  js inline "(typeof window !== 'undefined' ? (function(){ (#1)(window); return true; })() : false)"
  c inline "false"
}


// Execute an action after a specified time out.
pub extern timeout : forall<e>( msecs: int, action: () -> <dom|e> () ) -> <dom|e> ()
{
  js inline "window.setTimeout(#2,#1)"
  c inline ""
}

// Execute an action on a specified interval.
pub extern interval : forall<e>( msecs: int, action: () -> <dom|e> () ) -> <dom|e> ()
{
  js inline "window.setInterval(#2,#1)"
  c inline ""
}

