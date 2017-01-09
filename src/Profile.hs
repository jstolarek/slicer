module Profile where

import Trace
import TraceTree
import qualified Data.Map as Map



newtype Profile a = Profile {unProfile :: Map.Map a Int}
    deriving (Eq,Ord,Show)

empty = Profile Map.empty
singleton k i = Profile (Map.singleton k i)
merge (Profile p1) (Profile p2) = Profile (Map.unionWith (+) p1 p2)
merges ps = Profile (Map.unionsWith (+) (map unProfile ps))
diff (Profile p1) (Profile p2)
    = Profile (Map.differenceWith
               (\x y -> if y < x then Just (x - y) else Nothing) p1 p2)

incr (Profile p) x = Profile (Map.update (\x -> Just (x + 1)) x p)

-- Profiling
-- TODO: Accummulator versions.


profile :: Trace -> Profile Lab
profile t = profiles' (to_tree t)
    where profiles' ts = merges (map profile' ts)
          profile' THole = empty
          profile' (TTrue t t1) = profiles' (t ++ t1)
          profile' (TFalse t t2) = profiles' (t ++ t2)
          profile' (TInL t t1) = profiles' (t ++ t1)
          profile' (TInR t t2) = profiles' (t ++ t2)
          profile' (TCall k t1 t2 t) =
              let m = case label k
                      of Nothing -> empty
                         Just lbl -> singleton lbl 1
              in profiles' (t ++ t1 ++ t2) `merge` m

{-
profile :: Trace -> Profile Lab
profile t = fastprofile t empty
-}

fastprofile :: Trace -> Profile Lab -> Profile Lab
fastprofile t mu = fastprofiles' (to_tree t) mu
    where fastprofiles' [] = id
          fastprofiles' (t:ts) = fastprofile' t . fastprofiles' ts
          fastprofile' THole mu = mu
          fastprofile' (TTrue t t1) mu = fastprofiles' t (fastprofiles' t1 mu)
          fastprofile' (TFalse t t2) mu = fastprofiles' t (fastprofiles' t2 mu)
          fastprofile' (TInL t t1) mu = fastprofiles' t (fastprofiles' t1 mu)
          fastprofile' (TInR t t2) mu = fastprofiles' t (fastprofiles' t2 mu)
          fastprofile' (TCall k t1 t2 t) mu =
              let mu' = (fastprofiles' t . fastprofiles' t1 . fastprofiles' t2) mu
              in
              case label k
              of Nothing -> mu'
                 Just lbl -> incr mu' lbl


profile2 :: Trace -> Profile (Lab,Lab)
profile2 t = profiles' (mkL "_root") (to_tree t)
    where profiles' parent ts = merges (map (profile' parent) ts)
          profile' _ THole = empty
          profile' parent (TTrue t t1) = profiles' parent (t ++ t1)
          profile' parent (TFalse t t2) = profiles' parent (t ++ t2)
          profile' parent (TInL t t1) = profiles' parent (t ++ t1)
          profile' parent (TInR t t2) = profiles' parent (t ++ t2)
          profile' parent (TCall k t1 t2 t) =
              let (lbl,m) = case label k
                      of Nothing -> (parent,empty)
                         Just lbl' -> (lbl',singleton (parent,lbl') 1)
              in profiles' parent (t1 ++ t2) `merge` profiles' lbl t `merge` m

{-

profile Hole = empty
profile (Var x) = empty
profile Unit = empty
profile (CBool b) = empty
profile (CInt i) = empty
profile (Fun k) = empty
profile (Let x e1 e2) = (profile e1) `merge` (profile e2)
profile (Op f es) = merges (map profile es)
profile (Pair e1 e2) = (profile e1) `merge` (profile e2)
profile (Fst e) = (profile e)
profile (Snd e) = (profile e)
profile (InL e) = (profile e)
profile (InR e) = (profile e)
profile (Roll e) = (profile e)
profile (Unroll e) = (profile e)
--traces
profile (CaseL t m x t1) = (profile t) `merge` (profile t1)
profile (CaseR t m x t2) = profile t `merge` profile t2
profile (IfThen t e1 e2 t1) = (profile t) `merge` (profile t1)
profile (IfElse t e1 e2 t2) = (profile t) `merge` (profile t2)
profile (Call t1 t2 k t)
    = let m = case label k
              of Nothing -> empty
                 Just lbl -> singleton lbl 1
      in (profile t1) `merge` (profile t2) `merge` profile (body t) `merge` m
-}






