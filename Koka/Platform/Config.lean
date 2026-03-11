/-
  Ported from Haskell Koka:
  File:   src/Platform/cpp/Platform/Config.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
import Lean

namespace Koka.Platform.Config

def programName : String := "koka"

def version : String := "3.0.0"

def compilerBuildVariant : String := "lean"

def compiler : String := "lean4"

-- Note: Much of this can be replaced by native Lean 4 features during refactoring.
-- For example, `exeExtension` and path delimiters can often be avoided by using `System.FilePath`
-- which normalizes paths automatically across platforms.

def exeExtension : String := if System.Platform.isWindows then ".exe" else ""
def dllExtension : String := if System.Platform.isWindows then ".dll" else if System.Platform.isOSX then ".dylib" else ".so"
def objExtension : String := if System.Platform.isWindows then ".obj" else ".o"
def libExtension : String := if System.Platform.isWindows then ".lib" else ".a"
def libPrefix    : String := if System.Platform.isWindows then "" else "lib"
def pathSep      : Char   := if System.Platform.isWindows then '\\' else '/'
def pathDelimiter: Char   := if System.Platform.isWindows then ';' else ':'

def sourceExtension : String := ".kk"

def buildDate : String := "2026-03-06"
def buildTime : String := "12:00:00 2026-03-06"

end Koka.Platform.Config
