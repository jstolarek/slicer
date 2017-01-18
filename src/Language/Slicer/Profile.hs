module Language.Slicer.Profile
    ( profile, profile2
    ) where

import           Language.Slicer.Core
import           Language.Slicer.TraceTree

import qualified Data.Map as Map

newtype Profile a = Profile {unProfile :: Map.Map a Int}
    deriving (Show, Eq, Ord)

empty :: Profile a
empty = Profile Map.empty

singleton :: a -> Int -> Profile a
singleton k i = Profile (Map.singleton k i)

merge :: Ord a => Profile a -> Profile a -> Profile a
merge (Profile p1) (Profile p2) = Profile (Map.unionWith (+) p1 p2)

merges :: Ord a => [Profile a] -> Profile a
merges ps = Profile (Map.unionsWith (+) (map unProfile ps))

profile :: Trace -> Profile Lab
profile trace = profiles' (to_tree trace)
    where profiles' ts               = merges (map profile' ts)
          profile' THole             = empty
          profile' (TTrue t t1)      = profiles' (t ++ t1)
          profile' (TFalse t t2)     = profiles' (t ++ t2)
          profile' (TInL t t1)       = profiles' (t ++ t1)
          profile' (TInR t t2)       = profiles' (t ++ t2)
          profile' (TCall k t1 t2 t) =
              let m = case funLabel k of
                        Nothing -> empty
                        Just lbl -> singleton lbl 1
              in profiles' (t ++ t1 ++ t2) `merge` m

profile2 :: Trace -> Profile (Lab, Lab)
profile2 trace = profiles' (mkL "_root") (to_tree trace)
    where profiles' parent ts               = merges (map (profile' parent) ts)
          profile' _ THole                  = empty
          profile' parent (TTrue t t1)      = profiles' parent (t ++ t1)
          profile' parent (TFalse t t2)     = profiles' parent (t ++ t2)
          profile' parent (TInL t t1)       = profiles' parent (t ++ t1)
          profile' parent (TInR t t2)       = profiles' parent (t ++ t2)
          profile' parent (TCall k t1 t2 t) =
              let (lbl,m) = case funLabel k of
                              Nothing -> (parent,empty)
                              Just lbl' -> (lbl',singleton (parent,lbl') 1)
              in profiles' parent (t1 ++ t2) `merge` profiles' lbl t `merge` m
