module web/wasm

extern import
  c  file "wasm-inline.c"

value struct jsObject
  h: int32

value struct window
  pub obj: jsObject

pub fun getWindow(): window
  Window(getStatic("window"))

value struct console
  pub obj: jsObject

pub fun console(): console
  Console(getStatic("console"))

pub extern logObject(js: jsObject): ()
  c inline "logObject(#1.h)"

pub fun log(c: console, js: jsObject): jsFunction
  jsFunctionCall1(getJsObjectField(c.obj, "log"), js)

pub alias jsFunction = jsObject

pub inline extern jsFunctionCall0(f: jsFunction): jsObject
  c inline "jsFunctionCall0(#1, kk_context())"

pub inline extern jsFunctionCall1(f: jsFunction, x: jsObject): jsObject
  c inline "kk_lib_web_wasm__new_JsObject(kk_js_function_call_1(#1.h, #2.h, kk_context()), kk_context())"

pub inline extern jsFunctionCall2(f: jsFunction, x: jsObject, y: jsObject): jsObject
  c inline "jsFunctionCall2(#1, #2, #3, kk_context())"

pub inline extern jsFunctionCall3(f: jsFunction, x: jsObject, y: jsObject, z: jsObject): jsObject
  c inline "jsFunctionCall3(#1, #2, #3, #4, kk_context())"

pub inline extern jsFunctionCall4(f: jsFunction, x: jsObject, y: jsObject, z: jsObject, w: jsObject): jsObject
  c inline "jsFunctionCall4(#1, #2, #3, #4, #5, kk_context())"

pub inline extern jsFunctionCall5(f: jsFunction, x: jsObject, y: jsObject, z: jsObject, w: jsObject, v: jsObject): jsObject
  c inline "jsFunctionCall5(#1, #2, #3, #4, #5, #6, kk_context())"

pub inline fip extern unsafeJsCast( v: jsObject ): a 
  inline "#1"

extern setObjField(obj: jsObject, field: string, x: x): ()
  c inline "setObjectField(#1, #2, #3, kk_context())"

extern getObjField(obj: jsObject, field: string): x
  c inline "getObjectField(#1, #2, kk_context())"

extern setStatic(field: string, x: x): ()
  c inline "setStaticField(#1, #2, kk_context())"

extern getStatic(field: string): x
  c inline "getStaticField(#1, kk_context())"

pub inline fun setJsObjectField(obj: jsObject, field: string, x: x): ()
  setObjField(obj, field, x)

pub inline fun getJsObjectField(obj: jsObject, field: string): x
  unsafeJsCast(getObjField(obj, field))

pub inline fun setJsStaticField(field: string, x: x): ()
  setStatic(field, x)

pub inline fun getJsStaticField(field: string): x
  unsafeJsCast(getStatic(field))

pub inline extern jsOperation0(s: string): jsObject
  c inline "jsOperation(#1, kk_context())"

pub inline extern jsOperation1(obj: jsObject, s: string): jsObject
  c inline "jsOperation(#1, #2, kk_context())"

pub inline extern jsOperation2(obj: jsObject, s: string, x: jsObject): jsObject
  c inline "jsOperation(#1, #2, #3, kk_context())"

pub inline extern jsOperation3(obj: jsObject, s: string, x: jsObject, y: jsObject): jsObject
  c inline "jsOperation(#1, #2, #3, #4, kk_context())"

pub inline extern jsOperation4(obj: jsObject, s: string, x: jsObject, y: jsObject, z: jsObject): jsObject
  c inline "jsOperation(#1, #2, #3, #4, #5, kk_context())"

pub inline extern getConstant(name: string): x
  c inline "getConstant(#1, kk_context())"

pub inline extern newJsObject(): jsObject
  c inline "newJsObject(kk_context())"

pub inline extern newJsClass0(name: string): jsObject
  c inline "newJsObject(#1, kk_context())"

pub inline extern newJsClass1(name: string, x: jsObject): jsObject
  c inline "newJsObject(#1, #2, kk_context())"

pub inline extern newJsClass2(name: string, x1: jsObject, x2: jsObject): jsObject
  c inline "newJsObject(#1, #2, #3, kk_context())"

pub inline extern newJsClass3(name: string, x1: jsObject, x2: jsObject, x3: jsObject): jsObject
  c inline "newJsObject(#1, #2, #3, #4, kk_context())"

pub inline extern newJsClass4(name: string, x1: jsObject, x2: jsObject, x3: jsObject, x4: jsObject): jsObject
  c inline "newJsObject(#1, #2, #3, #4, #5, kk_context())"

pub inline extern newJsClass5(name: string, x1: jsObject, x2: jsObject, x3: jsObject, x4: jsObject, x5: jsObject): jsObject
  c inline "newJsObject(#1, #2, #3, #4, #5, #6, kk_context())"

pub inline extern newJsClass6(name: string, x1: jsObject, x2: jsObject, x3: jsObject, x4: jsObject, x5: jsObject, x6: jsObject): jsObject
  c inline "newJsObject(#1, #2, #3, #4, #5, #6, #7, kk_context())"

pub inline extern newJsClass7(name: string, x1: jsObject, x2: jsObject, x3: jsObject, x4: jsObject, x5: jsObject, x6: jsObject, x7: jsObject): jsObject
  c inline "newJsObject(#1, #2, #3, #4, #5, #6, #7, #8, kk_context())"

pub inline extern newJsClass8(name: string, x1: jsObject, x2: jsObject, x3: jsObject, x4: jsObject, x5: jsObject, x6: jsObject, x7: jsObject, x8: jsObject): jsObject
  c inline "newJsObject(#1, #2, #3, #4, #5, #6, #7, #8, #9, kk_context())"