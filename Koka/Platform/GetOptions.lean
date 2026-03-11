/-
  Ported from Haskell Koka:
  File:   src/Platform/cpp/Platform/GetOptions.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
namespace Koka.Platform.GetOptions

inductive ArgOrder a
  | RequireOrder
  | Permute
  | ReturnInOrder (f : String → a)

inductive ArgDescr a
  | NoArg (v : a)
  | ReqArg (f : String → a) (name : String)
  | OptArg (f : Option String → a) (name : String)

structure OptDescr a where
  mk ::
  shortOpt : List Char
  longOpt  : List String
  argDescr : ArgDescr a
  help     : String

def usageInfo {a : Type} (header : String) (options : List (OptDescr a)) : String :=
  let ds := options.map fun opt =>
    let shorts := String.intercalate ", " (opt.shortOpt.map fun c => s!"-{c}")
    let longs  := String.intercalate ", " (opt.longOpt.map fun s => s!"--{s}")
    let argStr := match opt.argDescr with
      | ArgDescr.NoArg _ => ""
      | ArgDescr.ReqArg _ name => s!"={name}"
      | ArgDescr.OptArg _ name => s!"[={name}]"
    let both := if shorts.isEmpty then s!"    {longs}{argStr}" else s!"{shorts}, {longs}{argStr}"
    s!"  {both.pushn ' ' (max 0 (30 - both.length))}{opt.help}"
  header ++ "\n" ++ String.intercalate "\n" ds

-- A very basic getOpt implementation that parses POSIX-style arguments.
-- Note: This is a simplified port that covers standard option parsing.
partial def getOpt {a : Type} (order : ArgOrder a) (options : List (OptDescr a)) (args : List String) : (List a × List String × List String) :=
  let rec go (args : List String) (opts : List a) (nonOpts : List String) (errs : List String) :=
    match args with
    | [] => (opts.reverse, nonOpts.reverse, errs.reverse)
    | "--" :: rest => (opts.reverse, nonOpts.reverse ++ rest, errs.reverse)
    | arg :: rest =>
      if arg.startsWith "--" && arg != "--" then
        let nameAndVal := (arg.drop 2 |>.toString).splitOn "="
        let name := nameAndVal.head!
        let valOpt := if nameAndVal.length > 1 then some (String.intercalate "=" nameAndVal.tail!) else none
        let matchOpt := options.find? (fun o => o.longOpt.contains name)
        match matchOpt with
        | none => go rest opts nonOpts (s!"unrecognized option `{arg}`" :: errs)
        | some o =>
          match o.argDescr, valOpt with
          | ArgDescr.NoArg v, none => go rest (v :: opts) nonOpts errs
          | ArgDescr.NoArg _, some _ => go rest opts nonOpts (s!"option `{arg}` doesn't allow an argument" :: errs)
          | ArgDescr.ReqArg f _, some v => go rest (f v :: opts) nonOpts errs
          | ArgDescr.ReqArg f _, none =>
            match rest with
            | [] => go rest opts nonOpts (s!"option `{arg}` requires an argument" :: errs)
            | nextArg :: nextRest => go nextRest (f nextArg :: opts) nonOpts errs
          | ArgDescr.OptArg f _, v => go rest (f v :: opts) nonOpts errs
      else if arg.startsWith "-" && arg != "-" then
        let chars := (arg.drop 1 |>.toString).toList
        let rec goShorts (cs : List Char) (restArgs : List String) (optsAcc : List a) (errsAcc : List String) :=
          match cs with
          | [] => go restArgs optsAcc nonOpts errsAcc
          | c :: cs' =>
            let matchOpt := options.find? (fun o => o.shortOpt.contains c)
            match matchOpt with
            | none => goShorts cs' restArgs optsAcc (s!"unrecognized option `-{c}`" :: errsAcc)
            | some o =>
              match o.argDescr with
              | ArgDescr.NoArg v => goShorts cs' restArgs (v :: optsAcc) errsAcc
              | ArgDescr.ReqArg f _ =>
                if !cs'.isEmpty then
                  go restArgs (f (String.ofList cs') :: optsAcc) nonOpts errsAcc
                else
                  match restArgs with
                  | [] => go restArgs optsAcc nonOpts (s!"option `-{c}` requires an argument" :: errsAcc)
                  | nextArg :: nextRest => go nextRest (f nextArg :: optsAcc) nonOpts errsAcc
              | ArgDescr.OptArg f _ =>
                if !cs'.isEmpty then
                  go restArgs (f (some (String.ofList cs')) :: optsAcc) nonOpts errsAcc
                else
                  go restArgs (f none :: optsAcc) nonOpts errsAcc
        goShorts chars rest opts errs
      else
        match order with
        | ArgOrder.RequireOrder =>
          (opts.reverse, nonOpts.reverse ++ (arg :: rest), errs.reverse)
        | ArgOrder.Permute =>
          go rest opts (arg :: nonOpts) errs
        | ArgOrder.ReturnInOrder f =>
          go rest (f arg :: opts) nonOpts errs
  go args [] [] []

end Koka.Platform.GetOptions
