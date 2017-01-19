{-# LANGUAGE NamedFieldPuns #-}

module Language.Slicer.TraceGraph
    ( visualizePDF, visualizeDiffPDF, visualizeSVG, visualizeDiffSVG
    ) where

import           Language.Slicer.Core ( Trace, Exp(..), Code(..), Match(..) )
import           Language.Slicer.PrettyPrinting

import           Data.GraphViz
import           Data.GraphViz.Attributes.Colors
import           Data.GraphViz.Attributes.Complete
import           Data.Text.Lazy ( pack )
import           Prelude hiding ( id )

data G a = G (Int -> DotGraph Int -> (Int,DotGraph Int,a))

instance Functor G where
    fmap f (G a) = G (\i g -> let (i', g', a') = a i g
                              in (i', g', f a'))

instance Applicative G where
    pure a = G (\i g -> (i, g, a))
    (G f) <*> (G a) = G (\i g -> let (i' , g' , f') = f i g
                                     (i'', g'', a') = a i' g'
                                 in (i'', g'', f' a'))

instance Monad G where
    return a = G (\i g -> (i, g, a))
    G x >>= y = G (\i g -> let (i',g',a) = x i g
                               G y' = y a
                           in y' i' g')

gensym :: G Int
gensym = G (\i g -> (i + 1, g, i))

addNode :: DotNode Int -> G ()
addNode n = G (\i -> \(DotGraph m d id (DotStmts atts sgs nodes edges)) ->
                       (i,DotGraph  m d id (DotStmts atts sgs (n:nodes) edges),()))

addEdge :: DotEdge Int -> G ()
addEdge e = G (\i -> \(DotGraph m d id (DotStmts atts sgs nodes edges)) ->
                       (i,DotGraph  m d id (DotStmts atts sgs nodes (e:edges)),()))

gNode :: Color -> String -> G Int
gNode clr lbl = do
  i <- gensym
  let n = DotNode i [ FontSize 36.0, Shape BoxShape, Style [SItem Filled []]
                    , FillColor [WC clr Nothing], Label (StrLabel (pack lbl))]
  addNode n
  return i

gHole :: G Int
gHole = do
  i <- gensym
  let n = DotNode i [FontSize 36.0, Shape BoxShape, Label (StrLabel (pack " "))]
  addNode n
  return i

gEdge :: Int -> Int -> G ()
gEdge m m' = addEdge (DotEdge m m' [FontSize 24.0])

trace2gv :: [GlobalAttributes] -> (String -> G Int) -> Trace -> DotGraph Int
trace2gv attribs node t = g
    where g0 = DotGraph True True (Just (Str (pack "G")))
               (DotStmts attribs [] [] [])
          G f = trace2gvG node gEdge t
          (_,g,_) = f 0 g0

trace2gvG :: (String -> G Int) -> (Int -> Int -> G ()) -> Trace -> G Int
trace2gvG node edge = buildGraph
    where buildGraph (Var x) = node (show (pp x))
          buildGraph (Let x e1 e2) = do i <- node ("let " ++ show x)
                                        i2 <- buildGraph e2
                                        edge i i2
                                        i1 <- buildGraph e1
                                        edge i i1
                                        return i
          buildGraph (Fun (Rec { funBody })) = buildGraph funBody
          buildGraph Unit = node "()"
          buildGraph (CBool b) = node (if b then "true" else "false")
          buildGraph (CInt  i) = node (show i)
          buildGraph (CString s) = node s
          buildGraph (Op f ts) = do i <- node (show (pp f))
                                    idxs <- mapM buildGraph (reverse ts)
                                    mapM_ (\j -> edge i j) idxs
                                    return i
          buildGraph (Pair t1 t2) = do i <- node "pair"
                                       i2 <- buildGraph t2
                                       edge i i2
                                       i1 <- buildGraph t1
                                       edge i i1
                                       return i
          buildGraph (Fst t) = do i <- node "fst"
                                  j <- buildGraph t
                                  edge i j
                                  return i
          buildGraph (Snd t) = do i <- node "snd"
                                  j <- buildGraph t
                                  edge i j
                                  return i
          buildGraph (InL t) = do i <- node "inl"
                                  j <- buildGraph t
                                  edge i j
                                  return i
          buildGraph (InR t) = do i <- node "inr"
                                  j <- buildGraph t
                                  edge i j
                                  return i
          buildGraph (If c e1 e2) = do
            -- Not constructing graph for condition, just printing
            i <- node ("if: " ++ show (pp c))
            k <- buildGraph e1
            edge i k
            j <- buildGraph e2
            edge i j
            return i
          buildGraph (IfThen t _ _ t1) = do i <- node "if/t"
                                            k <- buildGraph t1
                                            edge i k
                                            j <- buildGraph t
                                            edge i j
                                            return i
          buildGraph (IfElse t _ _ t2) = do i <- node "if/f"
                                            k <- buildGraph t2
                                            edge i k
                                            j <- buildGraph t
                                            edge i j
                                            return i
          buildGraph (Case e m) = do
            -- Not constructing graph for scrutinee, just printing
            i <- node ("case:" ++ show (pp e))
            k <- buildGraph (snd (inL m))
            edge i k
            j <- buildGraph (snd (inR m))
            edge i j
            return i
          buildGraph (CaseL t _ _ t1) = do i <- node "case/l"
                                           k <- buildGraph t1
                                           edge i k
                                           j <- buildGraph t
                                           edge i j
                                           return i
          buildGraph (CaseR t _ _ t2) = do i <- node "case/r"
                                           k <- buildGraph t2
                                           edge i k
                                           j <- buildGraph t
                                           edge i j
                                           return i
          buildGraph (Call t1 t2 _ t) = do i <- node "app"
                                           k <- buildGraph (funBody t)
                                           edge i k
                                           j2 <- buildGraph t2
                                           edge i j2
                                           j1 <- buildGraph t1
                                           edge i j1
                                           return i
          buildGraph (Roll   _ t) = buildGraph t
          buildGraph (Unroll _ t) = buildGraph t
          buildGraph Hole = gHole
          buildGraph (App e1 e2) = do i <- node "app"
                                      j2 <- buildGraph e2
                                      edge i j2
                                      j1 <- buildGraph e1
                                      edge i j1
                                      return i
          buildGraph (Trace t) = do i <- node "trace"
                                    j <- buildGraph t
                                    edge i j
                                    return i

-- Takes traces t1,t2
-- Visualize differences between traces:
-- Blue for shared part
-- Green for t2 only
-- Red for t1 only
traces2gv :: [GlobalAttributes]
          -> (String -> G Int, String -> G Int, String -> G Int)
          -> Exp -> Exp -> DotGraph Int
traces2gv attribs (node, node1, node2) t1 t2 = g

    where g0 = DotGraph True True (Just (Str (pack "G")))
                 (DotStmts attribs [] [] [])
          G f = traces2gvG (node, node1, node2) gEdge t1 t2
          (_,g,_) = f 0 g0

traces2gvG :: (String -> G Int, String -> G Int, String -> G Int)
           -> (Int -> Int -> G ()) -> Exp -> Exp -> G Int
traces2gvG (node, node1, node2) edge = buildGraph
    where buildGraph (Var x) (Var _) = node (show (pp x))
          buildGraph (Let x e1 e2) (Let _ e1' e2')
              = do i <- node ("let " ++ show x)
                   i2 <- buildGraph e2 e2'
                   edge i i2
                   i1 <- buildGraph e1 e1'
                   edge i i1
                   return i
          buildGraph (Fun _) (Fun _) = node "<fun>"
          buildGraph Unit Unit = node "()"
          buildGraph (CBool b) (CBool b')
              | b == b'
              = node (if b then "true" else "false")
          buildGraph (CInt i) (CInt i')
              | i == i'
              = node (show i)
          buildGraph (Op f ts) (Op f' ts')
              | f == f' && length ts == length ts'
                  = do i <- node (show (pp f))
                       idxs <- mapM (\(t1,t2) -> buildGraph t1 t2)
                                    (reverse (zip ts ts'))
                       mapM_ (\j -> edge i j) idxs
                       return i
          buildGraph (Pair t1 t2) (Pair t1' t2')
              = do i <- node "pair"
                   i2 <- buildGraph t2 t2'
                   edge i i2
                   i1 <- buildGraph t1 t1'
                   edge i i1
                   return i
          buildGraph (Fst t) (Fst t')
              = do i <- node "fst"
                   j <- buildGraph t t'
                   edge i j
                   return i
          buildGraph (Snd t) (Snd t')
              = do i <- node "snd"
                   j <- buildGraph t t'
                   edge i j
                   return i
          buildGraph (InL t) (InL t') =
              do i <- node "inl"
                 j <- buildGraph t t'
                 edge i j
                 return i
          buildGraph (InR t) (InR t')
              = do i <- node "inr"
                   j <- buildGraph t t';
                   edge i j
                   return i
          buildGraph (IfThen t _ _ t1) (IfThen t' _ _ t1')
              = do i <- node "if/t"
                   k <- buildGraph t1 t1'
                   edge i k
                   j <- buildGraph t t'
                   edge i j
                   return i
          buildGraph (IfElse t _ _ t2) (IfElse t' _ _ t2')
              = do i <- node "if/f"
                   k <- buildGraph t2 t2'
                   edge i k
                   j <- buildGraph t t'
                   edge i j
                   return i
          buildGraph (CaseL t _ _ t1) (CaseL t' _ _ t1')
              = do i <- node "case/l"
                   k <- buildGraph t1 t1'
                   edge i k
                   j <- buildGraph t t'
                   edge i j
                   return i
          buildGraph (CaseR t _ _ t2) (CaseR t' _ _ t2')
              = do i <- node "case/r"
                   k <- buildGraph t2 t2'
                   edge i k
                   j <- buildGraph t t'
                   edge i j
                   return i
          buildGraph (Call t1 t2 _ t) (Call t1' t2' _ t')
              = do i <- node "app"
                   k <- buildGraph (funBody t) (funBody t')
                   edge i k
                   j2 <- buildGraph t2 t2'
                   edge i j2
                   j1 <- buildGraph t1 t1'
                   edge i j1
                   return i
          buildGraph (App e1 e2) (App e1' e2')
              = do i <- node "app"
                   j2 <- buildGraph e2 e2'
                   edge i j2
                   j1 <- buildGraph e1 e1'
                   edge i j1
                   return i
          buildGraph (Roll tv t) (Roll tv' t')
              | tv == tv'
              = buildGraph t t'
          buildGraph (Unroll tv t) (Unroll tv' t')
              | tv == tv'
              = buildGraph t t'
          buildGraph t Hole = trace2gvG node1 edge t
          buildGraph Hole t = trace2gvG node2 edge t

          buildGraph _ _ = error "Not safe to throw an exception here..."



common_attrs :: [GlobalAttributes]
common_attrs = [GraphAttrs [RankDir FromTop,
                            Ratio (CompressRatio),
                            Size (GSize 7.5 (Just 10.0) False)]]

trace2gv_default :: Trace -> DotGraph Int
trace2gv_default t = trace2gv common_attrs (gNode (X11Color White)) t

traces2gv_default :: Exp -> Exp -> DotGraph Int
traces2gv_default t t' = traces2gv common_attrs (gNode (X11Color White),
                                       gNode (X11Color Gray),
                                       gNode (X11Color Black)) t t'

visualizePDF :: String -> Trace -> IO FilePath
visualizePDF fn t = runGraphvizCommand Dot (trace2gv_default t) Pdf fn

visualizeSVG :: String -> Trace -> IO FilePath
visualizeSVG fn t = runGraphvizCommand Dot  (trace2gv_default t) Svg fn

visualizeDiffPDF :: String -> Trace -> Trace -> IO FilePath
visualizeDiffPDF fn t t'
    = runGraphvizCommand Dot (traces2gv_default t t') Pdf fn

visualizeDiffSVG :: String -> Trace -> Trace -> IO FilePath
visualizeDiffSVG fn t t'
    = runGraphvizCommand Dot (traces2gv_default t t') Svg fn
