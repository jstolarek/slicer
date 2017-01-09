module UpperSemiLattice (
    UpperSemiLattice(..)
  ) where

import           Control.Exception.Base ( assert )

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
    lub (Just x) (Just y) = assert (x == y) $ Just x

    leq Nothing  _        = True
    leq _        Nothing  = False
    leq (Just x) (Just y) = x == y
