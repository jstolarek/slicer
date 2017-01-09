module TraceTree where

import Trace
import Util

data TraceTree = THole
               | TTrue TraceForest TraceForest
               | TFalse TraceForest TraceForest
               | TInL TraceForest TraceForest
               | TInR TraceForest TraceForest
               | TCall Code TraceForest TraceForest TraceForest
                 deriving (Show,Eq,Ord)

type TraceForest = [TraceTree]

treesize :: TraceTree -> Int
treesize THole = 1
treesize (TTrue ts ts') = forestsize ts + forestsize ts' + 1
treesize (TFalse ts ts') = forestsize ts + forestsize ts' + 1
treesize (TInL ts ts') = forestsize ts + forestsize ts' + 1
treesize (TInR ts ts') = forestsize ts + forestsize ts' + 1
treesize (TCall _ ts1 ts2 ts) = forestsize ts1 + forestsize ts2 + forestsize ts + 1

forestsize :: TraceForest -> Int
forestsize [] = 0
forestsize (t:ts) = treesize t + forestsize ts

{-
to_tree :: Trace -> TraceForest
to_tree Hole = [THole]
to_tree (Var x') = []
to_tree (Let x' t1 t2)
    = to_tree t1 ++ to_tree t2
to_tree Unit = []
to_tree (CBool b') = []
to_tree (IfThen t _ _ t1) = [TTrue (to_tree t) (to_tree t1)]
to_tree (IfElse t _ _ t2) = [TFalse (to_tree t) (to_tree t2)]
to_tree (CInt i') = []
to_tree (Op f' ts)
    = concat (map to_tree ts)
to_tree (Pair t1 t2)
    = to_tree t1 ++ to_tree t2
to_tree (Fst t) = to_tree t
to_tree (Snd t) = to_tree t
to_tree (InL t) = to_tree t
to_tree (InR t) = to_tree t
to_tree (CaseL t m x' t1)
    = [TInL (to_tree t) (to_tree t1)]
to_tree (CaseR t m y' t2)
    = [TInR (to_tree t) (to_tree t2)]
to_tree (Fun k') = []
to_tree (Call t1 t2 k t)
    = [TCall k (to_tree t1) (to_tree t2) (to_tree (body t))]
to_tree (Roll _ t) = to_tree t
to_tree (Unroll _ t) = to_tree t
to_tree t = error ("to_tree" ++ show t)
-}

to_tree t = to_tree_fast t []

to_tree_fast :: Trace -> TraceForest -> TraceForest
to_tree_fast Hole acc = THole:acc
to_tree_fast (Var x') acc = acc
to_tree_fast (Let x' t1 t2)  acc
    = (to_tree_fast t1 . to_tree_fast t2) acc
to_tree_fast Unit acc = acc
to_tree_fast (CBool b') acc = acc
to_tree_fast (IfThen t _ _ t1) acc = (TTrue (to_tree_fast t []) (to_tree_fast t1 [])):acc
to_tree_fast (IfElse t _ _ t2) acc = (TFalse (to_tree_fast t []) (to_tree_fast t2 [])):acc
to_tree_fast (CInt i') acc = acc
to_tree_fast (Op f' ts) acc
    = foldr to_tree_fast acc ts
to_tree_fast (Pair t1 t2) acc
    = (to_tree_fast t1 . to_tree_fast t2) acc
to_tree_fast (Fst t) acc = to_tree_fast t acc
to_tree_fast (Snd t) acc = to_tree_fast t acc
to_tree_fast (InL t) acc = to_tree_fast t acc
to_tree_fast (InR t) acc = to_tree_fast t acc
to_tree_fast (CaseL t m x' t1) acc
    = (TInL (to_tree_fast t []) (to_tree_fast t1 [])) : acc
to_tree_fast (CaseR t m y' t2) acc
    = (TInR (to_tree_fast t []) (to_tree_fast t2 [])) : acc
to_tree_fast (Fun k') acc  = acc
to_tree_fast (Call t1 t2 k t) acc
    = (TCall k (to_tree_fast t1 []) (to_tree_fast t2 []) (to_tree_fast (body t) [])):acc
to_tree_fast (Roll _ t) acc = to_tree_fast t acc
to_tree_fast (Unroll _ t) acc = to_tree_fast t acc
to_tree_fast t _ = error ("to_tree_fast" ++ show t)




from_tree :: Exp -> P TraceForest Trace
from_tree (Var x) = return (Var x)
from_tree (Let x e1 e2)  = do t1 <- from_tree e1
                              t2 <- from_tree e2
                              return (Let x t1 t2)
from_tree Unit = return Unit
from_tree (CBool b) = return (CBool b)
from_tree (If e e1 e2)
    = do c <- fetch
         case c of TTrue t t1 -> return (IfThen (from_tree' e t) e1 e2 (from_tree' e1 t1))
                   TFalse t t2 -> return (IfThen (from_tree' e t) e1 e2 (from_tree' e2 t2))
                   THole -> return Hole
from_tree (CInt i) = return (CInt i)
from_tree (Op f es) = do ts <- mapM from_tree es
                         return (Op f ts)
from_tree (Pair e1 e2) = do t1 <- from_tree e1
                            t2 <- from_tree e2
                            return (Pair t1 t2)
from_tree (Fst e) = do t <- from_tree e
                       return (Fst t)
from_tree (Snd e) = do t <- from_tree e
                       return (Snd t)
from_tree (InL e) = do t <- from_tree e
                       return (InL t)
from_tree (InR e) = do t <- from_tree e
                       return (InR t)
from_tree (Case e m)
    = let (Match (x,e1) (y,e2)) = m
      in do c <- fetch
            case c of TInL t t1 -> return (CaseL (from_tree' e t) m x (from_tree' e1 t1))
                      TInR t t2 -> return (CaseR (from_tree' e t) m y (from_tree' e1 t2))
                      THole -> return Hole
from_tree (Fun k) = return (Fun k)
from_tree (App e1 e2)
    = do c <- fetch
         case c of TCall k t1 t2 t ->
                       return (Call (from_tree' e1 t1)
                               (from_tree' e2 t2)
                               k
                               (Rec (fn k) (arg k) (from_tree' (body k) t) Nothing))
                   THole -> return Hole

from_tree (Roll tv e) = do t <- from_tree e
                           return (Roll tv t)
from_tree (Unroll tv e) = do t <- from_tree e
                             return (Unroll tv t)

from_tree' :: Exp -> TraceForest -> Trace
from_tree' e cs = let P f = from_tree e
                      (t,[]) = f cs
                  in t
