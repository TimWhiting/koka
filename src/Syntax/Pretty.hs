------------------------------------------------------------------------------
-- Copyright 2024, Microsoft Research, Tim Whiting.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

module Syntax.Pretty(
  ppValBinder,
  ppPatBinder,
  ppArg,
  ppSyntaxDef,
  ppSyntaxExpr,
  ppSyntaxBranch,
  ppSyntaxPattern,
  ppSyntaxExtern,
  ppLit
  ) where

import Data.List( partition, intersperse )
import Common.NamePrim( nameTpOptional, nameEffectEmpty, nameEffectExtend, nameOpExpr, nameTrue, isNameTuple )
import Common.Name hiding (qualify)
import Common.Range
import Lib.PPrint
import qualified Common.NameSet as S
import Syntax.Syntax as S
import Type.Pretty (ppName, ppType, defaultEnv)
import Common.Syntax (DefSort(..))

allDefs :: S.DefGroup UserType -> [S.Def UserType]
allDefs defs =
  case defs of
    S.DefNonRec d -> [d]
    S.DefRec ds   -> ds

ppLit :: S.Lit -> String
ppLit (S.LitInt i range) = show i
ppLit (S.LitFloat f range) = show f
ppLit (S.LitChar c range) = show c
ppLit (S.LitString s range) = show s

ppSyntaxDef :: S.Def UserType -> Doc
ppSyntaxDef (S.Def binder range vis sort inline doc)
  = ppDefBinder sort binder

ppDefBinder DefVal binder =
  text "val" <+> text (nameStem (binderName binder)) <+> text "=" <+> ppSyntaxExpr (binderExpr binder)
ppDefBinder DefVar binder =
  text "var" <+> text (nameStem (binderName binder)) <+> text ":=" <+> ppSyntaxExpr (binderExpr binder)
ppDefBinder (DefFun _ _) binder =
  text "fun" <+> text (nameStem (binderName binder)) <.> ppParams binder

ppParams :: ValueBinder () (S.Expr UserType) -> Doc
ppParams (ValueBinder _ _ (S.Lam pars expr range) _ _)
  = tupled (map ppValBinder pars) <--> indent 2 (ppSyntaxExpr expr)
ppParams (ValueBinder _ _ (S.Ann (S.Lam pars expr range) _ _) _ _)
  = tupled (map ppValBinder pars) <--> indent 2 (ppSyntaxExpr expr)

ppSyntaxExtern :: S.External -> Doc
ppSyntaxExtern e = text "extern" <+> ppName defaultEnv (extName e)

ppValBinder :: ValueBinder (Maybe UserType) (Maybe (S.Expr UserType)) -> Doc
ppValBinder (ValueBinder name (Just tp) (Just expr) nameRange range)
  = text (nameStem name) <+> text "=" <+> ppSyntaxExpr expr
ppValBinder (ValueBinder name Nothing (Just expr) nameRange range)
  = text (nameStem name) <+> text "=" <+> ppSyntaxExpr expr
ppValBinder (ValueBinder name (Just tp) Nothing nameRange range)
  = text (nameStem name)
ppValBinder (ValueBinder name Nothing Nothing nameRange range)
  = text (nameStem name)

ppValEmptyBinder :: ValueBinder (Maybe UserType) () -> Doc
ppValEmptyBinder (ValueBinder name _ () nameRange range)
  = text (nameStem name)

ppPatBinder :: ValueBinder (Maybe UserType) (S.Pattern UserType) -> Doc
ppPatBinder (ValueBinder name _ (S.PatWild rng) nameRange range)
  = text $ nameStem name
ppPatBinder (ValueBinder name _ pat nameRange range)
  = text (nameStem name) <+> text "as" <+> ppSyntaxPattern pat

ppArg :: (Maybe (Name,Range),S.Expr UserType) -> Doc
ppArg (Nothing,expr) = ppSyntaxExpr expr
ppArg (Just (name,_),expr) = text (nameStem name) <+> text "=" <+> ppSyntaxExpr expr

ppSyntaxExpr :: S.Expr UserType -> Doc
ppSyntaxExpr (S.Lam pars expr range) =
  text "fn" <.> tupled (map ppValBinder pars) <--> indent 2 (ppSyntaxExpr expr)
ppSyntaxExpr (S.Let defs expr range) =
  vcat (map ppSyntaxDef (allDefs defs) ++ [ppSyntaxExpr expr])
ppSyntaxExpr (Bind def expr range) =
  vcat [ppSyntaxDef def, ppSyntaxExpr expr]
ppSyntaxExpr (S.App (S.Var name _ _) args range) | name == nameOpExpr =
  hcat (intersperse (text " ") (map ppArg args))
ppSyntaxExpr (S.App hnd@Handler{} [(_, a)] range)  =
  tupled [ppSyntaxExpr hnd] <.> tupled [ppSyntaxExpr a]
ppSyntaxExpr (S.App fun args range)  =
  ppSyntaxExpr fun <.> tupled (map ppArg args)
ppSyntaxExpr (S.Var name isop range) = text $ nameStem name
ppSyntaxExpr (S.Lit lit)             = text $ ppLit lit
ppSyntaxExpr (Ann expr tp range)   = ppSyntaxExpr expr
ppSyntaxExpr (S.Case expr branches lazy range) =
  text "match" <+> ppSyntaxExpr expr <--> indent 2 (vcat (map ppSyntaxBranch branches))
ppSyntaxExpr (Parens expr name _ range) =
  ppSyntaxExpr expr
ppSyntaxExpr (Inject tp expr behind range) =
  text "mask<" <.> text (show tp) <.> text ">{" <--> indent 2 (ppSyntaxExpr expr) <--> text "}"
ppSyntaxExpr (Handler sort scope override allowmask eff pars reinit ret final branches drange range) =
  text "handler" <--> indent 2 (vcat (ppMaybeExpr ret: ppMaybeExpr reinit : ppMaybeExpr final : map ppHandlerBranch branches))

ppHandlerBranch :: S.HandlerBranch UserType -> Doc
ppHandlerBranch (HandlerBranch nm pars expr sort nmRng patRng) =
  pretty (show sort) <+> text (show nm) <.> tupled (map ppValEmptyBinder pars) <--> indent 2 (ppSyntaxExpr expr)

ppMaybeExpr :: Maybe (Expr UserType) -> Doc
ppMaybeExpr (Just expr) = ppSyntaxExpr expr
ppMaybeExpr Nothing = empty

ppSyntaxBranch :: S.Branch UserType -> Doc
ppSyntaxBranch (S.Branch pat [S.Guard (S.Var n _ _) body]) | nameTrue == n
  = ppSyntaxPattern pat <+> text "->" <--> indent 2 (ppSyntaxExpr body)
ppSyntaxBranch (S.Branch pat [guard])
  = ppSyntaxPattern pat <+> text "|" <+> ppSyntaxGuard guard
ppSyntaxBranch b = text $ show b

ppSyntaxPattern :: S.Pattern UserType -> Doc
ppSyntaxPattern (S.PatWild range) = text "_"
ppSyntaxPattern (S.PatVar binder) = ppPatBinder binder
ppSyntaxPattern (PatAnn pat tp range) = ppSyntaxPattern pat
ppSyntaxPattern (S.PatCon name args nameRng range) =
  if isNameTuple name then tupled (map ppPatternArg args)
  else if null args then text (nameStem name)
  else text (nameStem name) <.> tupled (map ppPatternArg args)
ppSyntaxPattern (PatParens pat range) = tupled [ppSyntaxPattern pat]
ppSyntaxPattern (S.PatLit lit) = text $ ppLit lit

ppPatternArg :: (Maybe (Name,Range), S.Pattern UserType) -> Doc
ppPatternArg (Nothing,pat) = ppSyntaxPattern pat
ppPatternArg (Just (name,_),S.PatWild rng) = text $ nameStem name
ppPatternArg (Just (name,_),pat) = text (nameStem name) <+> text "=" <+> ppSyntaxPattern pat

ppSyntaxGuard :: S.Guard UserType -> Doc
ppSyntaxGuard (S.Guard guard body)
  = ppSyntaxExpr guard <+> text "->" <--> indent 2 (ppSyntaxExpr body)
