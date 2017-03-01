{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}

-- Silence orphan instance warning when declaring UpperSemiLattices to be
-- Monoids
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Language.Slicer.UpperSemiLattice (
    UpperSemiLattice(..)
  ) where

-- | Defines an upper semilattice.  Note that the lub function (least upper
-- bound, join) is partial, although this is not reflected in the type
-- signature.  The way we use it ensures that it should only be called with
-- arguments for which it is defined.
class Eq a => UpperSemiLattice a where
    bot  :: a
    lub  :: a -> a -> a
    leq  :: a -> a -> Bool

    lubs :: [a] -> a
    lubs = foldl lub bot

instance Eq a => UpperSemiLattice (Maybe a) where
    bot = Nothing

    lub Nothing  x        = x
    lub x        Nothing  = x
    lub (Just x) (Just y) | x == y = Just x
    lub _ _ = error "UpperSemiLattice Maybe: error taking lub"

    leq Nothing  _        = True
    leq _        Nothing  = False
    leq (Just x) (Just y) = x == y

instance UpperSemiLattice a => Monoid a where
    mempty  = bot
    mappend = lub
