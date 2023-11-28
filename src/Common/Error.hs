-----------------------------------------------------------------------------
-- Copyright 2012-2021, Microsoft Research, Daan Leijen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-
    Internal error monad.
-}
-----------------------------------------------------------------------------
module Common.Error( Error, ErrorMessage(..), errorMsg, ok
                   , catchError, checkError, checkPartial, transformPartial, warningMsg, addWarnings, addPartialResult, ignoreWarnings
                   , ppErrorMessage, errorWarning, prettyWarnings ) where

import Control.Monad
import Control.Monad.Fail
import Control.Applicative
import Lib.PPrint
import Common.Range
import Common.ColorScheme
import Common.Message

{--------------------------------------------------------------------------
  Errors
--------------------------------------------------------------------------}
-- | Error monad
data Error b a    = Error !ErrorMessage ![(Range,Doc)] (Maybe b) -- B is a partial result
                | Ok !a ![(Range,Doc)]


-- | Error messages
data ErrorMessage = ErrorGeneral !Range !Doc
                  | ErrorParse   !Range !Doc
                  | ErrorStatic  [(Range,Doc)]  
                  | ErrorKind    [(Range,Doc)] 
                  | ErrorType    [(Range,Doc)] 
                  | ErrorWarning [(Range,Doc)] ErrorMessage   -- ^ warnings can be followed by errors
                  | ErrorIO      Doc
                  | ErrorZero
                  deriving (Show)

-- | Check an 'Error' 
checkError :: Error b a -> Either ErrorMessage (a,[(Range,Doc)])
checkError err
  = case err of
      Error msg w m -> Left (errorWarning w msg)
      Ok x w      -> Right (x,w)

checkPartial :: Error b a -> Either (ErrorMessage, Maybe b) (a,[(Range,Doc)])
checkPartial err
  = case err of
      Error msg w m -> Left (errorWarning w msg,m)
      Ok x w      -> Right (x,w)

transformPartial :: (b -> Maybe c) -> Error b a -> Error c a
transformPartial f err
  = case err of
      Error msg w m -> Error msg w (m >>= f)
      Ok x w      -> Ok x w

catchError :: Error b a -> (ErrorMessage -> Error b a) -> Error b a
catchError err handle
  = case err of
      Error msg w m -> addWarnings w (handle msg)
      Ok x w      -> Ok x w

ok :: a -> Error b a
ok x    = Ok x []

errorMsg :: ErrorMessage -> Error b a
errorMsg msg = Error msg [] Nothing

warningMsg :: (Range,Doc) -> Error b ()
warningMsg w
  = Ok () [w]

addWarnings :: [(Range,Doc)] -> Error b a -> Error b a
addWarnings [] err  = err
addWarnings ws err
  = case err of
      Error msg ws2 m -> Error msg (ws ++ ws2) m
      Ok x ws2      -> Ok x (ws ++ ws2)

addPartialResult :: Error b a -> Maybe b -> Error b a
addPartialResult err m
  = case err of
      Error msg ws _ -> Error msg ws m
      _                    -> err

errorWarning :: [(Range,Doc)] -> ErrorMessage -> ErrorMessage
errorWarning [] msg                                 = msg
errorWarning warnings (ErrorWarning warnings0 msg)  = errorWarning (warnings ++ warnings0) msg
errorWarning warnings msg                           = ErrorWarning warnings msg

errorMerge :: ErrorMessage -> ErrorMessage -> ErrorMessage
errorMerge err1 err2
  = let (ws1,msg1) = unwarn err1
        (ws2,msg2) = unwarn err2
    in errorWarning (ws1++ws2) $
       case (msg1,msg2) of
        (ErrorStatic errs1,ErrorStatic errs2) -> ErrorStatic (errs1 ++ errs2)
        (ErrorKind errs1,ErrorKind errs2)     -> ErrorKind (errs1 ++ errs2)
        (ErrorType errs1,ErrorType errs2)     -> ErrorType (errs1 ++ errs2)
        (ErrorZero,_) -> msg2
        _             -> msg1
  where
    unwarn (ErrorWarning warnings msg) = (warnings, msg)
    unwarn msg                         = ([],msg)
       
ignoreWarnings :: Error b a -> Error b a
ignoreWarnings (Error (ErrorWarning _ err) _ m)  = Error err [] m
ignoreWarnings (Error err _ m)                   = Error err [] m
ignoreWarnings (Ok x _)                        = Ok x []

{--------------------------------------------------------------------------
  pretty
--------------------------------------------------------------------------}  
instance Pretty ErrorMessage where
  pretty msg  = ppErrorMessage False defaultColorScheme msg

ppErrorMessage endToo cscheme msg
  = case msg of
      ErrorGeneral r doc    -> err (r,doc)
      ErrorParse r doc      -> err (r,doc)
      ErrorStatic es        -> vcat (map err es)
      ErrorKind ks          -> err (head ks)
      ErrorType es          -> err (head es)
      ErrorWarning  ws m    | null ws   -> ppErrorMessage endToo cscheme m
                            | otherwise -> prettyWarnings endToo cscheme ws <-> 
                                            (case m of ErrorZero -> Lib.PPrint.empty
                                                       _         -> ppErrorMessage endToo cscheme m)
      ErrorIO doc           -> color (colorError cscheme) doc
      ErrorZero             -> hang 1 (color (colorError cscheme) (text "<unknown error>"))
  where
    err (r,doc) = hang 1 $ ppRange endToo cscheme r <.>
                  color (colorError cscheme) (colon <+> text "error:" <+> doc)

prettyWarnings :: Bool -> ColorScheme -> [(Range,Doc)] -> Doc
prettyWarnings endToo cscheme warnings
  = vcat (map warn warnings)
  where
    warn (r,doc)
      = hang 1 $ ppRange endToo cscheme r <.> color (colorWarning cscheme) (colon <+> text "warning:" <+> doc)

{--------------------------------------------------------------------------
  instances
--------------------------------------------------------------------------}  
instance Functor (Error b) where
  fmap f e      = case e of
                    Ok x w    -> Ok (f x) w
                    Error msg w m -> Error msg w m

instance Applicative (Error b) where
  pure x = Ok x []
  (<*>) = ap                    

instance Monad (Error b) where
  -- return = pure
  e >>= f       = case e of 
                    Ok x w   -> addWarnings w (f x)
                    Error msg w m -> Error msg w m

instance MonadFail (Error b) where
  fail s        = Error (ErrorGeneral rangeNull (text s)) [] Nothing

instance MonadPlus (Error b) where
  mzero         = Error ErrorZero [] Nothing
  mplus e1 e2   = case e1 of
                    Ok _ _   -> e1
                    Error m1 w1 m11 -> case e2 of
                                      Ok _ _   -> e2
                                      Error m2 w2 m12 -> Error (errorMerge m1 m2) (w1 ++ w2) (m11 `mplus` m12)


instance Alternative (Error b) where
  (<|>) = mplus
  empty = mzero

instance Ranged ErrorMessage where
  getRange msg
    = case msg of
        ErrorGeneral r doc    -> r
        ErrorParse r doc      -> r
        ErrorStatic es        -> fst (head es)
        ErrorKind ks          -> fst (head ks)
        ErrorType es          -> fst (head es)
        ErrorWarning ws ErrorZero | not (null ws)
                              -> fst (head ws)
        ErrorWarning ws m     -> getRange m
        ErrorZero             -> rangeNull
        ErrorIO doc           -> rangeNull
