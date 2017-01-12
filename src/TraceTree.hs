module TraceTree
    ( TraceTree(..), to_tree, forestsize
    ) where

import           Trace

data TraceTree = THole
               | TTrue TraceForest TraceForest
               | TFalse TraceForest TraceForest
               | TInL TraceForest TraceForest
               | TInR TraceForest TraceForest
               | TCall Code TraceForest TraceForest TraceForest
                 deriving (Show, Eq, Ord)

type TraceForest = [TraceTree]

treesize :: TraceTree -> Int
treesize THole              = 1
treesize (TTrue   t1 t2   ) = forestsize t1 + forestsize t2 + 1
treesize (TFalse  t1 t2   ) = forestsize t1 + forestsize t2 + 1
treesize (TInL    t1 t2   ) = forestsize t1 + forestsize t2 + 1
treesize (TInR    t1 t2   ) = forestsize t1 + forestsize t2 + 1
treesize (TCall _ t1 t2 ts) = forestsize t1 + forestsize t2 + forestsize ts + 1

forestsize :: TraceForest -> Int
forestsize = sum . map treesize

to_tree :: Trace -> TraceForest
to_tree t = to_tree_fast t []

to_tree_fast :: Trace -> TraceForest -> TraceForest
to_tree_fast  Hole             acc = THole : acc
to_tree_fast (Var _)           acc = acc
to_tree_fast (Let _ t1 t2)     acc = (to_tree_fast t1 . to_tree_fast t2) acc
to_tree_fast  Unit             acc = acc
to_tree_fast (CBool _)         acc = acc
to_tree_fast (IfThen t _ _ t1) acc =
    (TTrue  (to_tree_fast t []) (to_tree_fast t1 [])):acc
to_tree_fast (IfElse t _ _ t2) acc =
    (TFalse (to_tree_fast t []) (to_tree_fast t2 [])):acc
to_tree_fast (CInt _)          acc = acc
to_tree_fast (Op _ ts)         acc = foldr to_tree_fast acc ts
to_tree_fast (Pair t1 t2)      acc = (to_tree_fast t1 . to_tree_fast t2) acc
to_tree_fast (Fst t)           acc = to_tree_fast t acc
to_tree_fast (Snd t)           acc = to_tree_fast t acc
to_tree_fast (InL t)           acc = to_tree_fast t acc
to_tree_fast (InR t)           acc = to_tree_fast t acc
to_tree_fast (CaseL t _ _ t1)  acc =
    (TInL (to_tree_fast t []) (to_tree_fast t1 [])) : acc
to_tree_fast (CaseR t _ _ t2)  acc =
    (TInR (to_tree_fast t []) (to_tree_fast t2 [])) : acc
to_tree_fast (Fun _)           acc = acc
to_tree_fast (Call t1 t2 k t)  acc =
    (TCall k (to_tree_fast t1 []) (to_tree_fast t2 [])
             (to_tree_fast (funBody t) [])) : acc
to_tree_fast (Roll   _ t)      acc = to_tree_fast t acc
to_tree_fast (Unroll _ t)      acc = to_tree_fast t acc
to_tree_fast t                 _   = error ("to_tree_fast" ++ show t)
