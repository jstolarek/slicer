module LowerSemiLattice where

class Eq a => LowerSemiLattice a where
    bot :: a 
    lub :: a -> a -> a
    lubs :: [a] -> a 
    lubs = foldl lub bot
    leq :: a -> a -> Bool

instance Eq a => LowerSemiLattice (Maybe a) where
    bot = Nothing
    leq Nothing x = True
    leq (Just x) (Just y) = x == y
    leq _ Nothing = False
    lub Nothing x = x
    lub x Nothing = x
    lub (Just x) (Just y) | x == y = Just x
