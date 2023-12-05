-- -----------------------------------------------------------------------------
-- -- Copyright 2012-2023, Microsoft Research, Daan Leijen. Brigham Young University, Tim Whiting.
-- --
-- -- This is free software; you can redistribute it and/or modify it under the
-- -- terms of the Apache License, Version 2.0. A copy of the License can be
-- -- found in the LICENSE file at the root of this distribution.
-- -----------------------------------------------------------------------------

-- {-
--     Check if a constructor context is well formed, and create a context path
-- -}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}

module Core.FixpointMonad(
  SimpleLattice(..),
  BasicLattice(..),
  Lattice(..),
  Contains(..),
  memo,
  push,
  runFixAEnv,
  runFix,
  runFixWithCache,
  runExample,
  FixTS,
  FixT,
  FixTR,
                        ) where
import Debug.Trace (trace)
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import Data.Maybe (fromJust, fromMaybe)
import Control.Monad.Reader (lift, ReaderT (runReaderT))
import Control.Monad.Trans.Cont (ContT(runContT), resetT, shiftT, mapContT, evalContT, callCC)
import Control.Monad.State (StateT (..), MonadState (..))
import Control.Monad.Identity (IdentityT, Identity (..))
import Data.List (intercalate)
import Control.Monad (foldM, ap)

-- A type class for lattices
-- A lattice has a bottom value, a join operation, and a lte relation
class Lattice l where
  bottom :: l
  join :: l -> l -> l
  lte :: l -> l -> Bool

-- A simple lattice is a lattice where we just have bottom, top, and a singleton value
-- An abstract value of an integer can be represented using this. Top means any integer, bottom means no integers, and a singleton value means a single integer value.
-- lte is just equality and joining just goes to top if the values are different
-- 
-- The underlying type a just needs to implement Ord for this to work
data SimpleLattice a = LBottom
  | LSingle a
  | LTop deriving (Eq, Ord)

instance Show a => Show (SimpleLattice a) where
  show LBottom = "LBottom"
  show (LSingle a) = "LSingle " ++ show a
  show LTop = "LTop"

instance (Ord a) => Lattice (SimpleLattice a) where
  bottom = LBottom
  join a b =
    case (a, b) of
      (LBottom, x) -> x
      (x, LBottom) -> x
      (LSingle x, LSingle y) -> if x == y then LSingle x else LTop
      _ -> LTop
  lte LBottom _ = True
  lte _ LTop = True
  lte (LSingle m) (LSingle m') = m == m'
  lte _ _ = False

-- A type class to allow us to easily define lattices for types that can implement a contains relation
-- 
-- Sets are a good example of such lattices, which can also hold more than one value.
-- However, it is up to the user to ensure that the set is finite such that the fixpoint will not diverge.
class Contains a where
  contains :: a -> a -> Bool

-- A Basic Lattice just delegates to the underlying type assuming that the underlying type implements the Contains type class and is a Monoid
newtype BasicLattice a = BL a deriving (Eq, Ord)

-- The `bottom` value is just the monoid's `mempty` value, `join` is implemented with `mappend`, and the `contains` relation defines `subsumption` (i.e. `a` contains `b` if `a` is a superset of `b`)
instance (Contains a, Monoid a) => Lattice (BasicLattice a) where
  bottom = BL mempty
  join (BL a) (BL b) = BL $ a `mappend` b
  lte (BL m) (BL m') = m' `contains` m

instance Functor BasicLattice where
  fmap f (BL a) = BL $ f a

instance (Contains a) => Contains (BasicLattice a) where
  contains (BL a) (BL b) = a `contains` b
instance Show a => Show (BasicLattice a) where
  show (BL a) = show a

instance (Semigroup a) => Semigroup (BasicLattice a) where
  (BL a) <> (BL b) = BL $ a <> b

instance (Monoid a) => Monoid (BasicLattice a) where
  mempty = BL mempty
  mappend = (<>)

-- Simple implementation of a set lattice
instance Ord a => Lattice (S.Set a) where
  bottom = S.empty
  join = S.union
  lte sa sb = sa `S.isSubsetOf` sb

type FixTS e s i l a = FixT e s i (l a) a (l a)
type FixTR e s i l a = FixT e s i (l a) a
newtype ContX e s i l a x = ContX { c:: l -> FixT e s i l a l} -- ReaderT DEnv (StateT (M.Map i (S.Set o, [ContX i o a]), State) Identity) a 
instance Show (ContX e s i l a x) where
  show _ = ""

type FixT e s i l a = ContT l (ReaderT e (StateT (M.Map i (l, [ContX e s i l a l]), s) Identity))

-- instance MonadFail (FixT i l s e a) where
--   fail = error

-- Memoization function, memoizes a fixpoint computation by using a cache of previous results and continuations that depend on those results
memo :: (Ord i, Lattice (l a)) => i -> (i -> FixTS e s i l a) -> FixTS e s i l a
memo key f = do
  callCC (\k -> do
    (cache, state) <- get
    case M.lookup key cache of
      Just (xss, conts) -> do
        put (M.insert key (xss, ContX k:conts) cache, state)
        -- trace ("New dependant on " ++ show key ++ " calling with current state " ++ show xss) $ return ()
        k xss
      Nothing -> do
        put (M.insert key (bottom, [ContX k]) cache, state)
        x <- f key
        -- trace ("Got new result for " ++ show key ++ " " ++ show x) $ return ()
        push key x
    )

-- Adds a new result to the cache and calls all continuations that depend on that result
push :: (Ord i, Lattice (l a)) => i -> l a -> FixTS e s i l a
push key value = do
  -- trace ("Pushing new result for " ++ show key ++ " : " ++ show value) $ return ()
  (cache, state) <- get
  let cur = M.lookup key cache
  let (xs, conts) = fromMaybe (bottom, []) cur
  if lte value xs then do
    -- trace ("New result " ++ show value ++ " is already contained in " ++ show xs) $ return ()
    return xs
  else do
    -- trace ("Calling continuations for " ++ show key) $ return ()
    put (M.insert key (value `join` xs, conts) cache, state)
    foldM (\acc (ContX c) -> do
        x' <- c value
        return $ acc `join` x'
      ) (value `join` xs) conts

-- Runs a fixpoint computation with an environment and a state, and an input value
runFixAEnv :: (t  -> ContT a (ReaderT r (StateT (M.Map k (b1, b2), c) Identity)) a) -> t -> r -> c -> (a, M.Map k b1, c)
runFixAEnv f a e s =
  let (res, (cache, state)) = runIdentity (runStateT (runReaderT (runContT (f a) return) e) (M.empty, s))
  in (res, fmap fst cache, state)

-- Runs a fixpoint computation with an environment and state
runFix :: ContT a (ReaderT r (StateT (M.Map k (b1, b2), c) Identity)) a -> r -> c -> (a, M.Map k b1, c)
runFix f e s =
  let (res, (cache, state)) = runIdentity (runStateT (runReaderT (runContT f return) e) (M.empty, s))
  in (res, fmap fst cache, state)

-- Runs a fixpoint computation with an environment, state, and cache 
-- (this allows us to use prior results when those results would not have changed)
-- CAUTION: Results should be invalidated if any of the inputs to the computation change
runFixWithCache :: ContT a (ReaderT r (StateT (b, c) Identity)) a -> r -> b -> c -> (a, b, c)
runFixWithCache f e c s =
  let (res, (cache, state)) = runIdentity (runStateT (runReaderT (runContT f return) e) (c, s))
  in (res, cache, state)


------------------------------ EXAMPLE USAGE ---------------------------------
---- An Example of how to use the fixpoint interface -- used for testing

newtype State = State{
  unique :: Int
} deriving Show

-- Takes in an integer and returns a fixpoint computation representing the fibonacci function
-- The fixpoint memoizes based on a tuple of the function name and the input
-- The fixpoint computation threads through State
-- The fixpoint computation doesn't use any environment monad
-- The fixpoint computation returns an integer encapsulated in a SimpleLattice
fib :: Int -> FixTS () State (String, Int) SimpleLattice Int
fib n =
  -- memo using the key ("fib", n) 
  -- (note: "fib" is not actually required, but for mutual recursion you need some way of dispatching based on the function name)
  memo ("fib", n) $ \(_, n) ->
    if n == 0 || n == 1 then return (LSingle 1) else do
      incrementUnique
      x <- fib (n - 1)
      y <- fib (n - 2)
      return $ case (x, y) of
        (LSingle x, LSingle y) -> LSingle (x + y)
        _ -> LBottom

incrementUnique :: FixTR e State b c d ()
incrementUnique = do
  (cache, state) <- get
  put (cache, state{unique = unique state + 1})

runExample :: IO ()
runExample = do
  let comp = runFixWithCache (fib 6) () M.empty (State 0)
  trace (show comp) $ return ()