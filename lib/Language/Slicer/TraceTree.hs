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

treesize :: TraceTree -> Int
treesize TTHole              = 1
treesize (TTTrue   t1 t2   ) = forestsize t1 + forestsize t2 + 1
treesize (TTFalse  t1 t2   ) = forestsize t1 + forestsize t2 + 1
treesize (TTInL    t1 t2   ) = forestsize t1 + forestsize t2 + 1
treesize (TTInR    t1 t2   ) = forestsize t1 + forestsize t2 + 1
treesize (TTCall _ t1 t2 ts) = forestsize t1 + forestsize t2 + forestsize ts + 1

forestsize :: TraceForest -> Int
forestsize = sum . map treesize

toTree :: Trace -> TraceForest
toTree t = toTreeFast t []

toTreeFast :: Trace -> TraceForest -> TraceForest
toTreeFast  THole            acc = TTHole : acc
toTreeFast (TSlicedHole _ _) acc = TTHole : acc
toTreeFast (TVar _)          acc = acc
toTreeFast (TLet _ t1 t2)    acc = (toTreeFast t1 . toTreeFast t2) acc
toTreeFast  TUnit            acc = acc
toTreeFast (TBool _)         acc = acc
toTreeFast (TInt _)          acc = acc
toTreeFast (TString _)       acc = acc
toTreeFast (TOp _ ts)        acc = foldr toTreeFast acc ts
toTreeFast (TPair t1 t2)     acc = (toTreeFast t1 . toTreeFast t2) acc
toTreeFast (TFst t)          acc = toTreeFast t acc
toTreeFast (TSnd t)          acc = toTreeFast t acc
toTreeFast (TInL t)          acc = toTreeFast t acc
toTreeFast (TInR t)          acc = toTreeFast t acc
toTreeFast (TFun _)          acc = acc
toTreeFast (TRoll   _ t)     acc = toTreeFast t acc
toTreeFast (TUnroll _ t)     acc = toTreeFast t acc
toTreeFast (TIfThen t t1)    acc =
    (TTTrue  (toTreeFast t []) (toTreeFast t1 [])):acc
toTreeFast (TIfElse t t2)    acc =
    (TTFalse (toTreeFast t []) (toTreeFast t2 [])):acc
toTreeFast (TCaseL t _ t1)   acc =
    (TTInL (toTreeFast t []) (toTreeFast t1 [])) : acc
toTreeFast (TCaseR t _ t2)   acc =
    (TTInR (toTreeFast t []) (toTreeFast t2 [])) : acc
toTreeFast (TCall t1 t2 k t) acc =
    (TTCall k (toTreeFast t1 []) (toTreeFast t2 [])
              (toTreeFast (funBody t) [])) : acc
