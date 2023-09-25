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
-- A lattice has a bottom value, a join operation, and a subsumption relation
class Lattice l a where
  bottom :: l a
  join :: l a -> l a -> l a
  sub :: l a -> l a -> Bool

-- A simple lattice is a lattice where we just have bottom, top, and a singleton value
-- An abstract value of an integer can be represented using this. Top means any integer, bottom means no integers, and a singleton value means a single integer value.
-- subsumption is just equality and joining just goes to top if the values are different
-- 
-- The underlying type a just needs to implement Ord for this to work
data SimpleLattice a = LBottom
  | LSingle a
  | LTop deriving (Eq, Ord)

instance Show a => Show (SimpleLattice a) where
  show LBottom = "LBottom"
  show (LSingle a) = "LSingle " ++ show a
  show LTop = "LTop"

instance (Ord a) => Lattice SimpleLattice a where
  bottom = LBottom
  join a b =
    case (a, b) of
      (LBottom, x) -> x
      (x, LBottom) -> x
      (LSingle x, LSingle y) -> if x == y then LSingle x else LTop
      _ -> LTop
  sub (LSingle m) (LSingle m') = m == m'
  sub m LTop = True
  sub _ LBottom = False

-- A type class to allow us to easily define lattices for types that can implement a contains relation
-- 
-- Sets are a good example of such lattices, which can also hold more than one value.
-- However, it is up to the user to ensure that the set is finite such that the fixpoint will not diverge.
class Contains a where
  contains :: a -> a -> Bool

-- A Basic Lattice just delegates to the underlying type assuming that the underlying type implements the Contains type class and is a Monoid
newtype BasicLattice a = BL a deriving (Eq, Ord)

instance Functor BasicLattice where
  fmap f (BL a) = BL (f a)

-- The `bottom` value is just the monoid's `mempty` value, `join` is implemented with `mappend`, and the `contains` relation defines `subsumption` (i.e. `a` contains `b` if `a` is a superset of `b`)
instance (Contains a, Monoid a) => Lattice BasicLattice a where
  bottom = BL mempty
  join (BL a) (BL b) = BL (a `mappend` b)
  sub (BL m) (BL m') = m' `contains` m

-- The instance itself defines a monoid, where `mempty` is `bottom` and `mappend` is `join`
instance (Contains a, Monoid a) => Semigroup (BasicLattice a) where
  (<>) = join

instance (Contains a, Monoid a) => Monoid (BasicLattice a) where
  mempty = bottom

-- Lift the contains relation
instance (Contains a) => Contains (BasicLattice a) where
  contains (BL a) (BL b) = a `contains` b

instance Show a => Show (BasicLattice a) where
  show (BL a) = show a

-- Simple implementation of a set lattice
instance Ord a => Lattice S.Set a where
  bottom = S.empty
  join = S.union
  sub sa sb = sa `S.isSubsetOf` sb

type FixTS i l s e a = FixT i l s e a (l a)
type FixTR i l s e a = FixT i l s e a
newtype ContX i l s e a x = ContX { c:: l a -> FixT i l s e a (l a)} -- ReaderT DEnv (StateT (M.Map i (S.Set o, [ContX i o a]), State) Identity) a 
instance Show (ContX i l s e a x) where
  show _ = ""

type FixT i l s e a = ContT (l a) (ReaderT e (StateT (M.Map i (l a, [ContX i l s e a s]), s) Identity))

-- instance MonadFail (FixT i l s e a) where
--   fail = error

-- Memoization function, memoizes a fixpoint computation by using a cache of previous results and continuations that depend on those results
memo :: (Show i, Ord i, Lattice l a, Show (l a)) => i -> (i -> ContT (l a) (ReaderT e (StateT (M.Map i (l a, [ContX i l x e a x]), x) Identity)) (l a)) -> ContT (l a) (ReaderT e (StateT (M.Map i (l a, [ContX i l x e a x]), x) Identity)) (l a)
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
push :: (Show k, Ord k, Lattice l a, Show (l a)) => k -> l a -> ContT (l a) (ReaderT e (StateT (M.Map k (l a, [ContX k l x e a x]), x) Identity)) (l a)
push key value = do
  -- trace ("Pushing new result for " ++ show key ++ " : " ++ show value) $ return ()
  (cache, state) <- get
  let cur = M.lookup key cache
  let (xs, conts) = fromMaybe (bottom, []) cur
  if sub value xs then do
    -- trace ("New result " ++ show value ++ " is already contained in " ++ show xs) $ return ()
    return bottom
  else do
    -- trace ("Calling continuations for " ++ show key) $ return ()
    put (M.insert key (value `join` xs, conts) cache, state)
    foldM (\acc (ContX c) -> do
        x' <- c value
        return $ acc `join` x'
      ) bottom conts

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
fib :: Int -> FixTS (String, Int) SimpleLattice State () Int
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

incrementUnique :: FixTR a b State c d ()
incrementUnique = do
  (cache, state) <- get
  put (cache, state{unique = unique state + 1})

runExample :: IO ()
runExample = do
  let comp = runFixWithCache (fib 6) () M.empty (State 0)
  trace (show comp) $ return ()