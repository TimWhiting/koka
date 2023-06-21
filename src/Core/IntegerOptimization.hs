-----------------------------------------------------------------------------
-- Copyright 2012-2023, Microsoft Research, Daan Leijen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

module Core.IntegerOptimization(
  mkFreshAbstractInt,
  checkIntRange,
  IntKind(..),
  testIntZ3,
) where


import Control.Applicative
import Control.Monad ( join )
import Core.Core(Expr(..))
import Core.DemandAnalysis
import Data.Maybe
import Data.Set
import qualified Data.Traversable as T
import Z3.Monad
import Data.Map
import Control.Monad.Cont (liftIO)
import Debug.Trace (trace)
import Data.List
import Z3.Base (mkContext, mkConfig, mkOptimize)
import qualified Z3.Base as Base

data AbstractValue = AbstractValue {
   closSet :: Set ExprContext,
   intConstraints :: AbstractInt,
   other :: AbstractLattice
  }
  -- TODO: Add more types, since Z3 can reason about algebraic data types
newtype AbstractInt = AbstractInt (Set Constraint, UniqueId)
newtype UniqueId = UniqueId Integer

data Constraint = 
  Lt UniqueId
  | Le UniqueId
  | Eq UniqueId
  | Ge UniqueId
  | EqV UniqueId
  | EqC Integer
-- Merging abstract constraints might be rather difficult
-- We can't just take the union of the sets, since we need to check if the constraints are compatible
-- We need to relax the constraints?

data IntKind = Int8 | Int16 | Int32 | Int64 | UInt8 | UInt16 | UInt32 | UInt64 | IntOther
  deriving Show

checkIntRange :: Z3 AST -> IO IntKind
checkIntRange constraints = do
  b <- evalZ3 $ program optimizeMinimize
  t <- evalZ3 $ program optimizeMaximize
  -- let b1 = trace ("T " ++ show t ++ " B " ++ show b) b
  case (b, t) of
    (Just b, Just t) ->
      if b >= 0 then
        if t < (2^8) then
          return UInt8
        else if t < (2^16) then
          return UInt16
        else if t < (2^32) then
          return $ trace ("T " ++ show t ++ " B " ++ show b) UInt32
        else if t < (2^64) then
          return UInt64
        else
          return IntOther
      else
        if t < (2^7) && b >= (-2^7) then
          return Int8
        else if t < (2^15) && b >= (-2^15) then
          return Int16
        else if t < (2^31) && b >= (-2^31) then
          return Int32
        else if t < (2^63) && b >= (-2^63) then
          return Int64
        else
          return IntOther
    _ -> return IntOther
  where
    program :: (AST -> Z3 Int) -> Z3 (Maybe Integer)
    program optim = do
      v <- constraints
      optim v
      t <- mkTrue
      check <- optimizeCheck [t]
      case check of
        Sat -> do
          m <- optimizeGetModel
          x <- fromJust <$> modelEval m v False
          xx <- getInt x
          return $ Just xx
        _ -> return Nothing

mkFreshAbstractInt = do
  v <- mkFreshIntVar "i"
  optimizeAssert =<< mkGe v =<< mkInteger (-(2^65))
  optimizeAssert =<< mkLt v =<< mkInteger (2^65)
  return v

assertLt v v1 = do
  optimizeAssert =<< mkLt v v1
assertLe v v1 = do
  optimizeAssert =<< mkLe v v1
assertGt v v1 = do
  optimizeAssert =<< mkGt v v1
assertGe v v1 = do
  optimizeAssert =<< mkGe v v1
assertLtConst v c = do
  optimizeAssert =<< mkLt v =<< mkInteger c
assertGtConst v c = do
  optimizeAssert =<< mkGt v =<< mkInteger c
assertLeConst v c = do
  optimizeAssert =<< mkLe v =<< mkInteger c
assertGeConst v c = do
  optimizeAssert =<< mkGe v =<< mkInteger c



testIntZ3 :: IO ()
testIntZ3 = 
  do
    u32 <- checkIntRange u32Test
    u64 <- checkIntRange u64Test
    i8 <- checkIntRange i8Test
    i64 <- checkIntRange i64Test
    print $ show [u32, u64, i8, i64]
  where
    u32Test :: Z3 AST
    u32Test = do
      v <- mkFreshAbstractInt
      assertGtConst v 32
      assertLtConst v (2^32)
      return v
    u64Test :: Z3 AST
    u64Test = do
      v <- mkFreshAbstractInt
      assertLtConst v (2^63)
      u32 <- u32Test
      assertGt v u32
      return v
    i8Test :: Z3 AST
    i8Test = do
      v <- mkFreshAbstractInt
      assertLtConst v (-1)
      assertGtConst v (-10)
      return v
    i64Test :: Z3 AST
    i64Test = do
      v <- mkFreshAbstractInt
      assertLt v =<< i8Test
      assertGtConst v (-2^62)
      return v