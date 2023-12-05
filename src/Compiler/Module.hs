-----------------------------------------------------------------------------
-- Copyright 2012-2021, Microsoft Research, Daan Leijen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-
    Main module.
-}
-----------------------------------------------------------------------------
module Compiler.Module( Module(..), Modules, moduleNull
                      , Loaded(..), ModStatus(..), initialLoaded
                      , loadedImportModule
                      , loadedName
                      , loadedLatest
                      , addOrReplaceModule, removeModule
                      , modPackageName -- , modPackageQName
                      , modPackagePath, modPackageQPath
                      , modLexemes
                      , PackageName
                      , loadedMatchNames
                      ) where

import Lib.Trace
import Lib.PPrint
import Data.Char              ( isAlphaNum )
import Common.Range           ( Range )
import Common.Name            ( Name, newName, unqualify, isHiddenName, showPlain)
import Common.Error
import Common.File            ( FileTime, fileTime0, maxFileTimes, splitPath )

import Syntax.Syntax
import Syntax.Lexeme
import Static.FixityResolve   ( Fixities, fixitiesEmpty, fixitiesNew, fixitiesCompose )

import Kind.ImportMap
import Kind.Synonym           ( Synonyms, synonymsEmpty, synonymsCompose, extractSynonyms )
import Kind.Newtypes          ( Newtypes, newtypesEmpty, newtypesCompose, extractNewtypes )
import Kind.Constructors      ( Constructors, constructorsEmpty, constructorsCompose, extractConstructors )
import Kind.Assumption        ( KGamma, kgammaInit, extractKGamma, kgammaUnion )

import Type.Assumption        ( Gamma, gammaInit, gammaUnion, extractGamma, gammaNames, gammaPublicNames)
import Type.Type              ( DataInfo )
import Core.Inlines           ( Inlines, inlinesNew, inlinesEmpty, inlinesExtends )
import Core.Borrowed          ( Borrowed, borrowedEmpty, borrowedExtendICore )

import Syntax.RangeMap
import Compiler.Package       ( PackageName, joinPkg )
import qualified Core.Core as Core
import Data.Maybe (fromJust)
import Compiler.Options (Flags)

{--------------------------------------------------------------------------
  Compilation
--------------------------------------------------------------------------}
type Modules = [Module]

data ModStatus =
  LoadedIface
  | LoadedSource
  | NotLoaded
  deriving (Eq, Ord, Show)

data Module  = Module{ modName        :: Name
                     , modPath        :: FilePath          -- interface file
                     , modSourcePath  :: FilePath          -- maybe empty
                     , modPackageQName:: FilePath          -- A/B/C
                     , modPackageLocal:: FilePath          -- lib
                     , modStatus      :: ModStatus
                     , modWarnings    :: [(Range,Doc)]
                     , modProgram     :: Maybe (Program UserType UserKind) -- not for interfaces
                     , modCore        :: Core.Core
                     , modCoreNoOpt   :: Core.Core
                     , modInlines     :: Either (Gamma -> Error () [Core.InlineDef]) ([Core.InlineDef])
                     , modCompiled    :: Bool
                     , modRangeMap    :: Maybe RangeMap
                     , modTime        :: FileTime
                     }

data Loaded = Loaded{ loadedGamma       :: Gamma
                    , loadedKGamma      :: KGamma
                    , loadedSynonyms    :: Synonyms
                    , loadedNewtypes    :: Newtypes
                    , loadedConstructors:: Constructors
                    , loadedFixities    :: Fixities
                    , loadedImportMap   :: ImportMap
                    , loadedUnique      :: Int
                    , loadedModule      :: Module
                    , loadedModules     :: [Module]
                    , loadedInlines     :: Inlines
                    , loadedBorrowed    :: Borrowed
                    }

instance Show Loaded where
  show ld
    = show (map modName $ loadedModules ld)

loadedLatest :: Loaded -> FileTime
loadedLatest loaded
  = maxFileTimes (map modTime (loadedModules loaded))

initialLoaded :: Loaded
initialLoaded
  = Loaded gammaInit
           kgammaInit
           synonymsEmpty
           newtypesEmpty
           constructorsEmpty
           fixitiesEmpty
           importsEmpty
           0
           (moduleNull (newName "Interactive"))
           []
           inlinesEmpty
           borrowedEmpty

moduleNull :: Name -> Module
moduleNull modName
  = Module (modName) "" "" "" "" NotLoaded [] Nothing (Core.coreNull modName) (Core.coreNull modName) (Left (\g -> return [])) False Nothing fileTime0 

loadedName :: Loaded -> Name
loadedName ld
  = modName (loadedModule ld)

modPackageName :: Module -> PackageName
modPackageName mod
  = last (splitPath (modPackageQName mod))

modPackagePath :: Module -> PackageName
modPackagePath mod
  = joinPkg (modPackageName mod) (modPackageLocal mod)

modPackageQPath :: Module -> PackageName
modPackageQPath mod
  = joinPkg (modPackageQName mod) (modPackageLocal mod)

modLexemes :: Module -> [Lexeme]
modLexemes mod = case modProgram mod of
                   Just program -> programLexemes program
                   _            -> []

loadedNames :: Loaded -> [Name]
loadedNames l
  = gammaNames (loadedGamma l)

loadedMatchNames :: Loaded -> [String]
loadedMatchNames l
  = map (showPlain . unqualify) $ gammaPublicNames (loadedGamma l)
  where
    -- good (c:_) = (c /= '.')


{---------------------------------------------------------------

---------------------------------------------------------------}


loadedImportModule :: (DataInfo -> Bool) -> Loaded -> Module -> Range -> Name -> (Loaded,[ErrorMessage])
loadedImportModule isValue (Loaded gamma1 kgamma1 syns1 data1 cons1 fix1 imps1 unique1 mod1 imp1 inlines1 borrowed1) mod range impName
  = let core = modCore mod
        (imps2,errs)
          = case importsExtend impName (modName mod) imps1 of
              Nothing   -> (imps1,[errorMessageKind ErrGeneral range (text "Module" <+> pretty impName <+> text "is already imported")])
              Just imps -> (imps,[])
        loaded
          = Loaded (gammaUnion gamma1 (extractGamma isValue False core))
                (kgammaUnion kgamma1 (extractKGamma core))
                (synonymsCompose syns1 (extractSynonyms core))
                (newtypesCompose data1 (extractNewtypes core))
                (constructorsCompose cons1 (extractConstructors core))
                (fixitiesCompose fix1 (extractFixities core))
                imps2
                unique1
                mod1
                (addOrReplaceModule mod imp1)
                inlines1
                (borrowedExtendICore core borrowed1)
    in -- trace ("loadedImport: " ++ show impName ++ " = " ++ show (modName mod) ++ " into " ++ show [mod | mod <- importsList imps2]) $
       (loaded,errs)

addOrReplaceModule :: Module -> Modules -> Modules
addOrReplaceModule mod []
  = [mod]
addOrReplaceModule mod (m:ms)
  = if modPath mod == modPath m
     then mod:ms
     else m : addOrReplaceModule mod ms

removeModule :: Name -> Modules -> Modules
removeModule name modules
  = filter (\m -> modName m /= name) modules

extractFixities :: Core.Core -> Fixities
extractFixities core
  = fixitiesNew [(name,fix) | Core.FixDef name fix <- Core.coreProgFixDefs core]
