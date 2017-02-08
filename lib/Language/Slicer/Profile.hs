module Language.Slicer.Profile
    ( profile, profileDiff
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
profile trace = profiles' (toTree trace)
    where profiles' ts                = merges (map profile' ts)
          profile' TTHole             = empty
          profile' (TTTrue t t1)      = profiles' (t ++ t1)
          profile' (TTFalse t t2)     = profiles' (t ++ t2)
          profile' (TTInL t t1)       = profiles' (t ++ t1)
          profile' (TTInR t t2)       = profiles' (t ++ t2)
          profile' (TTCall k t1 t2 t) =
              let m = case k of
                        Nothing -> empty
                        Just lbl -> singleton lbl 1
              in profiles' (t ++ t1 ++ t2) `merge` m

profileDiff :: Trace -> Profile (Lab, Lab)
profileDiff trace = profiles' (mkL "_root") (toTree trace)
    where profiles' parent ts                = merges (map (profile' parent) ts)
          profile' _ TTHole                  = empty
          profile' parent (TTTrue t t1)      = profiles' parent (t ++ t1)
          profile' parent (TTFalse t t2)     = profiles' parent (t ++ t2)
          profile' parent (TTInL t t1)       = profiles' parent (t ++ t1)
          profile' parent (TTInR t t2)       = profiles' parent (t ++ t2)
          profile' parent (TTCall k t1 t2 t) =
              let (lbl,m) = case k of
                              Nothing -> (parent,empty)
                              Just lbl' -> (lbl',singleton (parent,lbl') 1)
              in profiles' parent (t1 ++ t2) `merge` profiles' lbl t `merge` m
