/-
  Ported from Haskell Koka:
  File:   src/Common/File.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
namespace Koka.Common.File

def startsWith (s : String) (pre : String) : Bool :=
  s.startsWith pre

def endsWith (s : String) (post : String) : Bool :=
  s.endsWith post

def splitOn (pred : Char → Bool) (xs : String) : List String :=
  xs.split pred |>.toList |>.map (·.toString)

def trim (s : String) : String :=
  s.trimAscii.toString

abbrev FileName := String

def isPathSep (c : Char) : Bool :=
  c == '/' || c == '\\'

def isPathDelimiter (c : Char) : Bool :=
  c == ';' || c == ':'

def normalizeWith (newSep : Char) (path : String) : String :=
  let rec norm (acc : List Char) (chars : List Char) : List Char :=
    match chars with
    | [] => acc.reverse
    | '\\' :: c :: cs => if c.isWhitespace then norm (c :: '\\' :: acc) cs else
                         if isPathSep '\\' then norm (newSep :: acc) (c :: cs) else norm ('\\' :: acc) (c :: cs)
    | c :: cs =>
      if isPathSep c then norm (newSep :: acc) cs
      else norm (c :: acc) cs
  String.ofList (norm [] path.toList)

def normalize (path : String) : String :=
  let npath := normalizeWith '/' path
  match npath.toList with
  | c :: ':' :: '/' :: rest => String.ofList (c.toLower :: ':' :: '/' :: rest)
  | _ => npath

def splitPath (fdir : String) : List String :=
  let split (f : String) := splitOn isPathSep f
  match normalize fdir |>.toList with
  | [] => [""]
  | '/' :: '/' :: fs => "//" :: split (String.ofList fs)
  | '/' :: fs => "/" :: split (String.ofList fs)
  | _ => split (normalize fdir)

def joinPaths (dirs : List String) : String :=
  let rec resolveDot (ps : List String) : List String :=
    match ps with
    | [] => []
    | p :: "." :: rest => resolveDot (p :: rest)
    | p :: ".." :: rest =>
      if p == "." then resolveDot (".." :: rest)
      else if p == ".." then p :: resolveDot (".." :: rest)
      else resolveDot rest
    | p :: rest => p :: resolveDot rest

  -- flatMap
  let splitDirs := dirs.filter (!·.isEmpty) |>.flatMap splitPath
  let resolved := resolveDot splitDirs
  let joined := resolved.intersperse "/" |>.foldl (· ++ ·) ""
  let final := joined.replace "//" "/"
  if joined.startsWith "//" then "/" ++ final else final

def joinPath (p1 p2 : String) : String :=
  joinPaths [p1, p2]

def dirname (fname : String) : String :=
  joinPaths (splitPath fname |>.dropLast)

def notdir (fname : String) : String :=
  splitPath fname |>.getLastD ""

def extname (fname : String) : String :=
  let rbase := notdir fname |>.toList.reverse
  let (post, pre) := rbase.span (· ≠ '.')
  if pre.isEmpty then ""
  else "." ++ String.ofList post.reverse

def basename (fname : String) : String :=
  let rbase := notdir fname |>.toList.reverse
  let trimmed := rbase.dropWhile (· ≠ '.')
  match trimmed with
  | '.' :: rest => String.ofList rest.reverse
  | _ => notdir fname

def notext (fname : String) : String :=
  let extLen := extname fname |>.length
  fname.dropEnd extLen |>.toString

def noexts (fname : String) : String :=
  joinPaths [dirname fname, notdir fname |>.takeWhile (· ≠ '.') |>.toString]

def ensureExt (fname : String) (ext : String) : String :=
  if extname fname == ext then fname else fname ++ ext

def isAbsolute (fpath : String) : Bool :=
  match fpath.toList with
  | _ :: ':' :: c :: _ => isPathSep c
  | c :: _ => isPathSep c
  | _ => false

def commonPathPrefix (s1 s2 : String) : String :=
  let pairs := (splitPath s1).zip (splitPath s2)
  let common := pairs.takeWhile (fun (a, b) => a == b) |>.map Prod.fst
  joinPaths common

def getCwd : IO String := do
  let d ← IO.currentDir
  pure d.toString

def runSystemRaw (command : String) : IO Unit := do
  let _ ← IO.Process.run { cmd := "sh", args := #["-c", command] }
  pure ()

def runSystem (command : String) : IO Unit := runSystemRaw command

def runCmd (cmd : String) (args : List String) : IO Unit := do
  let _ ← IO.Process.run { cmd := cmd, args := args.toArray }
  pure ()

def runCmdRead (extraEnv : List (String × String)) (cmd : String) (args : List String) : IO (String × String) := do
  let child ← IO.Process.spawn { cmd := cmd, args := args.toArray, env := extraEnv.map (fun (k, v) => (k, some v)) |>.toArray, stdout := .piped, stderr := .piped }
  let out ← child.stdout.readToEnd
  let err ← child.stderr.readToEnd
  let exitCode ← child.wait
  if exitCode != 0 then
    throw <| IO.userError s!"command failed (exit code {exitCode})"
  pure (out, err)

def runCmdEnv (extraEnv : List (String × String)) (cmd : String) (args : List String) : IO Unit := do
  let _ ← IO.Process.run { cmd := cmd, args := args.toArray, env := extraEnv.map (fun (k, v) => (k, some v)) |>.toArray }
  pure ()

def getFileTime (fname : String) : IO IO.FS.SystemTime := do
  let md ← System.FilePath.metadata fname
  pure md.modified

def fileTimeCompare (fname1 fname2 : String) : IO Ordering := do
  let time1 ← getFileTime fname1
  let time2 ← getFileTime fname2
  if time1.sec < time2.sec then pure .lt
  else if time1.sec > time2.sec then pure .gt
  else if time1.nsec < time2.nsec then pure .lt
  else if time1.nsec > time2.nsec then pure .gt
  else pure .eq

def maxFileTime (t1 t2 : IO.FS.SystemTime) : IO.FS.SystemTime :=
  if t1.sec > t2.sec || (t1.sec == t2.sec && t1.nsec > t2.nsec) then t1 else t2

def maxFileTimes (times : List IO.FS.SystemTime) : IO.FS.SystemTime :=
  times.foldl maxFileTime ⟨0, 0⟩

def doesFileExistAndNotEmpty (fpath : String) : IO Bool := do
  try
    let md ← System.FilePath.metadata fpath
    pure (md.byteSize > 0)
  catch _ =>
    pure false

def readTextFile (fpath : String) : IO (Option String) := do
  try
    let content ← IO.FS.readFile fpath
    pure (some content)
  catch _ =>
    pure none

def writeTextFile (fpath : String) (content : String) : IO Unit :=
  IO.FS.writeFile fpath content

def copyTextFile (src dest : String) : IO Unit := do
  try
    IO.FS.createDirAll (dirname dest)
    let content ← IO.FS.readFile src
    IO.FS.writeFile dest content
  catch e => throw e

def copyTextFileWith (src dest : String) (transform : String → String) : IO Unit := do
  try
    IO.FS.createDirAll (dirname dest)
    let content ← IO.FS.readFile src
    IO.FS.writeFile dest (transform content)
  catch e => throw e

def copyBinaryFile (src dest : String) : IO Unit := do
  try
    IO.FS.createDirAll (dirname dest)
    let content ← IO.FS.readBinFile src
    IO.FS.writeBinFile dest content
  catch e => throw e

def copyBinaryIfNewer (always : Bool) (srcName outName : String) : IO Unit := do
  if srcName == outName then pure ()
  else if always then copyBinaryFile srcName outName
  else
    try
      let ord ← fileTimeCompare srcName outName
      if ord == .gt then copyBinaryFile srcName outName
    catch _ =>
      copyBinaryFile srcName outName

def copyTextIfNewer (always : Bool) (srcName outName : String) : IO Unit := do
  if srcName == outName then pure ()
  else if always then copyTextFile srcName outName
  else
    try
      let ord ← fileTimeCompare srcName outName
      if ord == .gt then copyTextFile srcName outName
    catch _ =>
      copyTextFile srcName outName

def copyTextIfNewerWith (always : Bool) (srcName outName : String) (transform : String → String) : IO Unit := do
  if srcName == outName then pure ()
  else if always then copyTextFileWith srcName outName transform
  else
    try
      let ord ← fileTimeCompare srcName outName
      if ord == .gt then copyTextFileWith srcName outName transform
    catch _ =>
      copyTextFileWith srcName outName transform

def removeFileIfExists (fname : String) : IO Unit := do
  try IO.FS.removeFile fname catch _ => pure ()

def getProgramPath : IO String := do
  let p ← IO.appPath
  pure p.toString

def getEnvVar (name : String) : IO String := do
  let val ← IO.getEnv name
  pure (val.getD "")

def getEnvPaths (name : String) : IO (List String) := do
  let xs ← getEnvVar name
  let paths := splitOn (fun c => isPathDelimiter c) xs
  pure (paths.filter (!·.isEmpty))

def realPath (fpath : String) : IO String := do
  try
    let p ← IO.FS.realPath fpath
    pure p.toString
  catch _ => pure fpath

def findMaximalPrefixPath (roots : List String) (p : String) : Option (String × String) :=
  let rels := roots.filterMap (fun r =>
    if p.startsWith r then
      let rel := String.ofList (p.drop r.length |>.toString.toList.dropWhile isPathSep)
      some (r, rel)
    else none)
  rels.head?

def getMaximalPrefixPath (roots : List String) (p : String) : String × String :=
  match findMaximalPrefixPath roots p with
  | some res => res
  | none => ("", p)

def makeRelativeToPaths (paths : List String) (fname : String) : String × String :=
  match findMaximalPrefixPath paths fname with
  | some (root, rpath) => (root, rpath)
  | none => (dirname fname, notdir fname)

end Koka.Common.File
