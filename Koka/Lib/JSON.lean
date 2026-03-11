/-
  Ported from Haskell Koka:
  File:   src/Lib/JSON.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00

  NOTE: Koka's compiler mainly uses Lib.JSON to parse `package.json` files for
  NPM style packages in `src/Compile/Package.hs`. This wrapper could potentially
  be completely replaced by Lean's native `Lean.Data.Json` without wrapping everything
  in `JsValue`, when porting over `Compile.Package`.
-/
import Lean
import Lean.Data.Json

namespace Koka.Lib.JSON

open Lean

-----------------------------------------------------------
-- JSON data
-----------------------------------------------------------

-- | JSON values
inductive JsValue
  | JsNull
  | JsBool (b : Bool)
  | JsInt (i : Int)
  | JsDouble (d : Float)
  | JsString (s : String)
  | JsArray (a : List JsValue)
  | JsObject (o : List (String × JsValue))
  deriving Inhabited

open JsValue

-- | Convert a JSON value to a string (leaving string values unquoted)
partial def toString (v : JsValue) : String :=
  match v with
  | JsString s => s
  | JsNull => "null"
  | JsBool b => if b then "true" else "false"
  | JsInt i => s!"{i}"
  | JsDouble d => s!"{d}"
  | JsArray vs => "[" ++ String.intercalate ", " (vs.map toString) ++ "]"
  | JsObject ms => "{ " ++ String.intercalate ",\n  " (ms.map fun (k, val) => s!"{repr k}: {toString val}") ++ "}"

instance : ToString JsValue := ⟨toString⟩

-- | Lookup a JSON value by giving a path of name strings.
-- The name strings can either refer to attributes in an object, or be indexes in an array.
partial def jsLookup (v : JsValue) : List String → JsValue
  | [] => v
  | (p :: ps) =>
    match v with
    | JsObject ms =>
      match ms.lookup p with
      | some val => jsLookup val ps
      | none => JsNull
    | JsArray vs =>
      if p.all Char.isDigit then
        let idx := p.toNat!
        match vs.toArray[idx]? with
        | some val => jsLookup val ps
        | none => JsNull
      else
        JsNull
    | _ => JsNull

-- | Lookup a JSON value using a default value if it cannot be found.
def jsFind (v def_val : JsValue) (path : List String) : JsValue :=
  match jsLookup v path with
  | JsNull => def_val
  | val => val

-----------------------------------------------------------
-- Conversion from Lean's native Json
-----------------------------------------------------------
partial def fromLeanJson (j : Lean.Json) : JsValue :=
  match j with
  | Json.null => JsNull
  | Json.bool b => JsBool b
  | Json.num n =>
    if n.exponent == 0 then
      JsInt n.mantissa
    else
      -- Lean 4 JsonNumber doesn't readily expose a float parse without stringifying it,
      -- but `toFloat` might be available, otherwise we convert to float string
      JsDouble (n.toFloat)
  | Json.str s => JsString s
  | Json.arr a => JsArray (a.toList.map fromLeanJson)
  | Json.obj kvs => JsObject (kvs.foldl (fun acc k v => (k, fromLeanJson v) :: acc) []).reverse

-----------------------------------------------------------
-- Parse
-----------------------------------------------------------

-- | Parse JSON from a given string, using FilePath for parse error messages.
-- | On Error, return a 'JsNull' value.
def readJSON (_fname : String) (xs : String) : JsValue :=
  match Lean.Json.parse xs with
  | Except.error _ => JsNull
  | Except.ok j => fromLeanJson j

-- | Parse JSON given a file path and input. The FilePath is used for error messages.
-- Returns either an error message or a 'JsValue'
def parseJSON (_source : String) (xs : String) : Except String JsValue :=
  match Lean.Json.parse xs with
  | Except.error err => Except.error err
  | Except.ok j => Except.ok (fromLeanJson j)

-- | Read a JSON value from a file, return 'JsNull' on errors.
def readJSONFromFile (fname : String) : IO JsValue := do
  try
    let txt ← IO.FS.readFile fname
    pure (readJSON fname txt)
  catch _ =>
    pure JsNull

-- | Parse a JSON value from a file.
def parseJSONFromFile (fname : String) : IO (Except String JsValue) := do
  try
    let txt ← IO.FS.readFile fname
    pure (parseJSON fname txt)
  catch e =>
    pure (Except.error e.toString)

end Koka.Lib.JSON
