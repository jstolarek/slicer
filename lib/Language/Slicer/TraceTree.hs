module Language.Slicer.TraceTree
    ( TraceTree(..), toTree, forestsize
    ) where

import           Language.Slicer.Core

data TraceTree = TTHole
               | TTTrue TraceForest TraceForest
               | TTFalse TraceForest TraceForest
               | TTInL TraceForest TraceForest
               | TTInR TraceForest TraceForest
               | TTCall (Maybe Lab) TraceForest TraceForest TraceForest
                 deriving (Show, Eq, Ord)

type TraceForest = [TraceTree]

treesize :: TraceTree -> Integer
treesize TTHole              = 1
treesize (TTTrue   t1 t2   ) = forestsize t1 + forestsize t2 + 1
treesize (TTFalse  t1 t2   ) = forestsize t1 + forestsize t2 + 1
treesize (TTInL    t1 t2   ) = forestsize t1 + forestsize t2 + 1
treesize (TTInR    t1 t2   ) = forestsize t1 + forestsize t2 + 1
treesize (TTCall _ t1 t2 ts) = forestsize t1 + forestsize t2 + forestsize ts + 1

forestsize :: TraceForest -> Integer
forestsize = sum . map treesize

toTree :: ToTree a => a -> TraceForest
toTree t = toTreeFast t []

class ToTree a where
    toTreeFast :: a -> TraceForest -> TraceForest

instance ToTree a => ToTree (Syntax a) where
    toTreeFast  Hole            acc = TTHole : acc
    toTreeFast (Var _)          acc = acc
    toTreeFast (Let _ t1 t2)    acc = (toTreeFast t1 . toTreeFast t2) acc
    toTreeFast  Unit            acc = acc
    toTreeFast (CBool _)        acc = acc
    toTreeFast (CInt _)         acc = acc
    toTreeFast (CDouble _)      acc = acc
    toTreeFast (CString _)      acc = acc
    toTreeFast (Pair t1 t2)     acc = (toTreeFast t1 . toTreeFast t2) acc
    toTreeFast (Fst t)          acc = toTreeFast t acc
    toTreeFast (Snd t)          acc = toTreeFast t acc
    toTreeFast (InL t)          acc = toTreeFast t acc
    toTreeFast (InR t)          acc = toTreeFast t acc
    toTreeFast (Fun _)          acc = acc
    toTreeFast (Roll   _ t)     acc = toTreeFast t acc
    toTreeFast (Unroll _ t)     acc = toTreeFast t acc
    toTreeFast (Seq t1 t2)      acc = (toTreeFast t1 . toTreeFast t2) acc

instance ToTree Trace where
    toTreeFast (TExp t)           acc = toTreeFast t acc
    toTreeFast (TSlicedHole _ _)  acc = TTHole : acc
    toTreeFast (TOp _ _ ts)       acc = foldr toTreeFast acc ts
    toTreeFast (TIfThen t t1)     acc =
        (TTTrue  (toTree t) (toTree t1)):acc
    toTreeFast (TIfElse t t2)     acc =
        (TTFalse (toTree t) (toTree t2)):acc
    toTreeFast (TIfExn t)         acc = toTreeFast t acc
    toTreeFast (TCaseL t _ t1)    acc =
        (TTInL (toTree t) (toTree t1)) : acc
    toTreeFast (TCaseR t _ t2)    acc =
        (TTInR (toTree t) (toTree t2)) : acc
    toTreeFast (TCall t1 t2 k t)  acc =
        (TTCall k (toTree t1) (toTree t2)
                  (toTree (funBody t))) : acc
    toTreeFast (TCallExn t1 t2)   acc = (toTreeFast t1 . toTreeFast t2) acc
    -- references
    toTreeFast (TRef _ t)         acc = toTreeFast t acc
    toTreeFast (TDeref _ t)       acc = toTreeFast t acc
    toTreeFast (TAssign _ t1 t2)  acc = (toTreeFast t1 . toTreeFast t2) acc
    -- arrays
    toTreeFast (TArr _ t1 t2)     acc = (toTreeFast t1 . toTreeFast t2) acc
    toTreeFast (TArrGet _ t1 t2)  acc = (toTreeFast t1 . toTreeFast t2) acc
    toTreeFast (TArrSet _ t1 t2 t3) acc =
        (toTreeFast t1 . toTreeFast t2 . toTreeFast t3) acc
    -- loops
    toTreeFast (TWhileDone t)     acc = toTreeFast t acc
    toTreeFast (TWhileStep t1 t2 t3) acc =
        (toTreeFast t1 . toTreeFast t2 . toTreeFast t3) acc
    -- exceptions
    toTreeFast (TRaise  t)        acc = toTreeFast t acc
    toTreeFast (TTry    t)        acc = toTreeFast t acc
    toTreeFast (TTryWith t1 _ t2) acc = (toTreeFast t1 . toTreeFast t2) acc
