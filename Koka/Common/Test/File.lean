import Koka.Common.File

open Koka.Common.File

#guard findMaximalPrefixPath ["/a/b/c", "/a/b/d"] "/a/b/c/foo/bar.lean" == some ("/a/b/c", "foo/bar.lean")

def main : IO Unit := do
  IO.println "Testing Koka.Common.File (IO)"

  -- Test realPath and relative path tools
  let cwd ← getCwd
  if cwd.isEmpty then IO.println "Fail: getCwd empty" else IO.println s!"Pass: getCwd -> {cwd}"

  let envPath ← getEnvPaths "PATH"
  if envPath.isEmpty then IO.println "Fail: PATH empty" else IO.println "Pass: getEnvPaths"
