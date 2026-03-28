/-
  Ported from Haskell Koka:
  File:   src/Compile/Package.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00

  NOTE: Currently uses Koka.Lib.JSON for `package.json` parsing. Wait, actually I'll just use it directly.
-/
import Koka.Lib.PPrint
import Koka.Platform.Config
import Koka.Common.Failure
import Koka.Common.File
import Koka.Lib.Trace
import Koka.Lib.JSON

namespace Koka.Compile.Package

open Koka.Lib.PPrint
open Koka.Platform.Config
open Koka.Common.Failure
open Koka.Common.File
open Koka.Lib.Trace
open Koka.Lib.JSON

abbrev PackageName := String

structure Package where
  pkgDir : String      -- /x/node_modules/A/lib
  pkgQualName : PackageName -- A/B/C
  pkgLocal : String    -- lib
  pkgSub : List Package
  deriving Repr, BEq, Inhabited

structure Packages where
  packages : List Package
  roots : List String
  deriving Repr, BEq, Inhabited

def packagesEmpty : Packages :=
  { packages := [], roots := [] }

def pkgName (pkg : Package) : PackageName :=
  match splitPath pkg.pkgQualName |>.getLast? with
  | some n => n
  | none => ""

def isFileSafe (path : String) : IO Bool := do
  try
    let isD ← System.FilePath.isDir path
    if isD then return false
    System.FilePath.pathExists path
  catch _ => return false

def isDirSafe (path : String) : IO Bool := do
  try
    System.FilePath.isDir path
  catch _ => return false

---------------------------------------------------------------
-- search packages
----------------------------------------------------------------

def node_modules : String := "node_modules"
def node_path : String := "NODE_PATH"
def package_json : String := "package.json"

def startsWith (s prefixStr : String) : Bool :=
  s.startsWith prefixStr

def packageBase (pkgpath : String) : String :=
  let parts := (splitPath pkgpath).reverse
  let trimmed := parts.dropWhile (· != node_modules)
  match trimmed with
  | _ :: base => joinPaths base.reverse
  | [] => pkgpath

partial def visiblePackages_pkgs (ccurrent : String) (pkgs : List Package) : List Package :=
  let isVisible (pkg : Package) := ccurrent.startsWith (packageBase pkg.pkgDir)
  let isVisibleSubs : List Package → Bool
    | [] => false
    | pkg :: _ => isVisible pkg
  let visible := pkgs.dropWhile (not ∘ isVisible)
  match visible.filter (isVisibleSubs ∘ Package.pkgSub) with
  | [] => visible
  | pkg :: _ => visiblePackages_pkgs ccurrent pkg.pkgSub ++ visible

def visiblePackages (pkgs : Packages) (ccurrent : String) : List Package :=
  visiblePackages_pkgs ccurrent pkgs.packages

def packageFromDir (pkgs0 : Packages) (dir : String) : Option Package :=
  let pkgs := visiblePackages pkgs0 dir
  match pkgs.filter (fun pkg => pkg.pkgDir == dir) with
  | pkg :: _ => some pkg
  | [] => none

def packageInfoFromDir (pkgs : Packages) (dir : String) : String × String :=
  match packageFromDir pkgs dir with
  | none => ("", "")
  | some pkg => (pkg.pkgQualName, pkg.pkgLocal)

partial def searchIn (pkgs : List Package) (name : String) : IO (Option String) :=
  match pkgs with
  | [] => return none
  | pkg :: rest => do
    let path := joinPath pkg.pkgDir name
    let exist ← isFileSafe path
    if exist then return some path
    else searchIn rest name

def searchPackages (pkgs : Packages) (current pkgname name : String) : IO (Option String) := do
  let ccurrent ← try
      let p ← IO.FS.realPath (if current.isEmpty then "." else current)
      pure p.toString
    catch _ => pure current
  let toSearch := visiblePackages pkgs ccurrent
  let toSearch := if pkgname.isEmpty then toSearch else toSearch.filter (fun pkg => pkgName pkg == pkgname)
  searchIn toSearch name

---------------------------------------------------------------
-- discover packages
----------------------------------------------------------------

def joinPkgs (ps : List String) : String :=
  let forwardSlash (s : String) := s.map (fun c => if c == '/' || c == '\\' then '/' else c)
  forwardSlash (joinPaths ps)

def joinPkg (p1 p2 : String) : String :=
  joinPkgs [p1, p2]

partial def readSubPackages (n : Nat) (pname path : String) : IO (List Package) := do
  let exist ← isDirSafe path
  if not exist then return []
  let contents ← System.FilePath.readDir path
  let children := contents.map (·.fileName) |>.filter (fun c => not c.isEmpty && c.front != '.')
  let childrenSorted := children.qsort (· < ·) |>.toList
  let cpkgs ← childrenSorted.mapM (readPackage pname path n)
  return cpkgs.filter (not ∘ String.isEmpty ∘ Package.pkgDir)
where
  readPackage (pname path : String) (n : Nat) (cname : String) : IO Package := do
    let jsonpath := joinPaths [path, cname, package_json]
    let exist ← isFileSafe jsonpath
    if not exist then return Package.mk "" "" "" []
    let json ← readJSONFromFile jsonpath
    let keywords := match jsLookup json ["keywords"] with
      | .JsArray elems => elems.map (fun e => toString e |>.toLower)
      | _ => []
    let isKokaPkg := cname.startsWith "koka" || keywords.contains "koka"
    let localVal := Koka.Lib.JSON.toString (jsFind json (.JsString (if isKokaPkg then "lib" else "")) ["directories", "lib"])
    let pkglocal := joinPaths (splitPath localVal |>.dropWhile (· == "."))
    let pkgdir := joinPaths [path, cname, pkglocal]
    let pkgname := joinPkgs [if n == 0 then "" else toString n, pname, cname]
    let pkgs ← readSubPackages n (joinPkg pname cname) (joinPaths [path, cname, node_modules])
    return Package.mk pkgdir pkgname pkglocal pkgs

partial def discoverPackages_walk_ps (n : Nat) (acc : List Package) (ps : List String) : IO (List Package) := do
  let cpkgs ← readSubPackages n "" (joinPaths (ps ++ [node_modules]))
  if ps.length > 0 then
    discoverPackages_walk_ps (if cpkgs.isEmpty then n else n + 1) (acc ++ cpkgs) (ps.dropLast)
  else
    return acc ++ cpkgs

def getHomeDirectory : IO String := do
  match ← IO.getEnv "HOME" with
  | some h => return h
  | none =>
    match ← IO.getEnv "USERPROFILE" with
    | some u => return u
    | none => return "."

def discoverPackages_walk_roots (n : Nat) (acc : List Package) : IO Packages := do
  let eroots ← getEnvPaths node_path
  let homedir ← getHomeDirectory
  let hroots := [joinPath homedir ".node_modules", joinPath homedir ".node_libraries"]
  let roots := hroots ++ eroots
  let mut _pkgss : List (List Package) := []
  let indexedRoots := (List.range roots.length |>.map (· + n)).zip roots
  let pkgss ← indexedRoots.mapM (fun (idx, p) => readSubPackages idx "" p)
  return Packages.mk (acc ++ pkgss.flatten) roots

def discoverPackages (root : String) : IO Packages := do
  let croot ← try
      let p ← IO.FS.realPath root
      pure p.toString
    catch _ => pure root
  discoverPackages_walk_ps 0 [] (splitPath croot) >>= fun acc => discoverPackages_walk_roots 0 acc

---------------------------------------------------------------
-- show packages
----------------------------------------------------------------

partial def ppPackages (ps : List Package) : Doc :=
  let atmost n s := if s.length > n then "..." ++ (s.drop (s.length - n)).toString else s
  let justify n s := if s.length < n then s ++ String.ofList (List.replicate (n - s.length) ' ') else s
  let ppPackage (pkg : Package) : Doc :=
    textP (justify 20 (pkg.pkgQualName ++ ": ") ++ atmost 50 pkg.pkgDir) <.>
    (if pkg.pkgSub.isEmpty then empty else line <.> nest 2 (ppPackages pkg.pkgSub))
  vcat (ps.map ppPackage)

instance : Pretty Package where
  pretty pkg := ppPackages [pkg]

instance : ToString Package where
  toString pkg := displayS (renderCompact (Pretty.pretty pkg))

end Koka.Compile.Package
