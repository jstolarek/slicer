module TraceGraph where

import Trace
import Data.GraphViz
import Util


data G a = G (Int -> DotGraph Int -> (Int,DotGraph Int,a)) 
instance Monad G where
    return a = G (\i -> \g -> (i,g,a))
    (G(x)) >>= y = 
        G(\i -> \g -> 
          let (i',g',a) = x i g in  
          let G(y') = y a in 
          y' i' g')

gensym :: G Int
gensym = G(\i -> \g -> (i+1,g,i))

addNode :: DotNode Int -> G ()
addNode n = G (\i -> \(DotGraph m d id (DotStmts atts sgs nodes edges)) -> 
                       (i,DotGraph  m d id (DotStmts atts sgs (n:nodes) edges),()))

addEdge :: DotEdge Int -> G ()
addEdge e = G (\i -> \(DotGraph m d id (DotStmts atts sgs nodes edges)) -> 
                       (i,DotGraph  m d id (DotStmts atts sgs nodes (e:edges)),()))

node :: Color -> String -> G Int
node color lbl = gensym >>= \i -> 
                 let n = DotNode i [FontSize 36.0,
                                    Shape BoxShape, 
                                    Style [SItem Filled []],
                                    FillColor color,
                                    Label (StrLabel lbl)]
                 in addNode n >> return i

hole :: G Int
hole = gensym >>= \i -> 
       let n = DotNode i [FontSize 36.0,
                          Shape BoxShape, 
                          Label (StrLabel " ")]
       in addNode n >> return i
                     
edge :: Int -> Int -> String -> G ()
edge m m' lbl = addEdge (DotEdge m m' True [FontSize 24.0])

oldedge :: Int -> Int -> String -> G ()
oldedge m m' lbl = addEdge (DotEdge m m' True [FontSize 24.0,
                                            Label (StrLabel lbl)])


--trace2gv :: [GlobalAttributes] -> Color -> Trace -> DotGraph Int
trace2gv attrs node t = g
    where g0 = DotGraph True True (Just (Str "G")) 
               (DotStmts attrs [] [] [])
          G (f) = trace2gvG node edge t
          (_,g,_) = f 0 g0

trace2gvG :: (String -> G Int) -> (Int -> Int -> String -> G ()) -> Trace -> G Int
trace2gvG node edge = traverse
    where traverse (Var x) = node (show (pp x))
          traverse (Let x e1 e2) = do i <- node ("let " ++ show x)
                                      i2 <- traverse e2
                                      edge i i2 "body"
                                      i1 <- traverse e1
                                      edge i i1 (show x)
                                      return i
          traverse (Fun k) = node "<fun>"
          traverse Unit = node "()"
          traverse (CBool b) = node (if b then "true" else "false")
          traverse (CInt i) = node (show i)
          traverse (Op f ts) = do i <- node (show (pp f))
                                  idxs <- mapM traverse (reverse ts)
                                  _ <- mapM (\j -> edge i j (show (j-i))) idxs
                                  return i
          traverse (Pair t1 t2) = do i <- node "pair"
                                     i2 <- traverse t2
                                     edge i i2 "snd"
                                     i1 <- traverse t1
                                     edge i i1 "fst"
                                     return i
          traverse (Fst t) = do i <- node "fst"
                                j <- traverse t
                                edge i j ""
                                return i
          traverse (Snd t) = do i <- node "snd"
                                j <- traverse t
                                edge i j ""
                                return i
          traverse (InL t) = do i <- node "inl"
                                j <- traverse t
                                edge i j ""
                                return i
          traverse (InR t) = do i <- node "inr"
                                j <- traverse t
                                edge i j ""
                                return i
          traverse (IfThen t _ _ t1) = do i <- node "if/t"
                                          k <- traverse t1
                                          edge i k "then"
                                          j <- traverse t 
                                          edge i j "test"
                                          return i
          traverse (IfElse t _ _ t2) = do i <- node "if/f"
                                          k <- traverse t2
                                          edge i k "else"
                                          j <- traverse t 
                                          edge i j "test"
                                          return i
          traverse (CaseL t _ x t1) = do i <- node "case/l"
                                         k <- traverse t1
                                         edge i k ("inl "++show x)
                                         j <- traverse t 
                                         edge i j "test"
                                         return i
          traverse (CaseR t _ x t2) = do i <- node "case/r"
                                         k <- traverse t2
                                         edge i k ("inr "++show x)
                                         j <- traverse t 
                                         edge i j "test"
                                         return i
          traverse (Call t1 t2 _ t) = do i <- node "app"
                                         k <- traverse (body t)
                                         edge i k "call"
                                         j2 <- traverse t2
                                         edge i j2 (show (arg t))
                                         j1 <- traverse t1
                                         edge i j1 (show (fn t))
                                         return i
          traverse (Roll _ t) = traverse t
          traverse (Unroll _ t) = traverse t
          -- I think there's a slight bug here.
          traverse Hole = hole -- node " "

          traverse (App e1 e2) = do i <- node "app"
                                    j2 <- traverse e2
                                    edge i j2 "NO IDEA WHAT..."
                                    j1 <- traverse e1
                                    edge i j1 "THESE STRINGS ARE FOR"
                                    return i
          traverse (t) = error "Not safe to throw an exception here..."




 
-- Takes traces t1,t2
-- Visualize differences between traces:
-- Blue for shared part
-- Green for t2 only
-- Red for t1 only
--traces2gv :: Attributes -> (Color,Color,Color) -> Trace -> Trace -> DotGraph Int
traces2gv attrs (node, node1, node2) t1 t2 = g

    where g0 = DotGraph True True (Just (Str "G")) 
                 (DotStmts attrs [] [] [])
          G (f) = traces2gvG (node,node1,node2) edge t1 t2
          (_,g,_) = f 0 g0

traces2gvG (node,node1,node2) edge = traverse
    where traverse (Var x) (Var x') = node (show (pp x))
          traverse (Let x e1 e2) (Let x' e1' e2') 
              = do i <- node ("let " ++ show x)
                   i2 <- traverse e2 e2'
                   edge i i2 "body"
                   i1 <- traverse e1 e1'
                   edge i i1 (show x)
                   return i
          traverse (Fun k) (Fun k') = node "<fun>"
          traverse Unit Unit = node "()"
          traverse (CBool b) (CBool b') 
              | b == b'
              = node (if b then "true" else "false")
          traverse (CInt i) (CInt i') 
              | i == i'
              = node (show i)
          traverse (Op f ts) (Op f' ts') 
              | f == f' && length ts == length ts'
                  = do i <- node (show (pp f))
                       idxs <- mapM (\(t1,t2) -> traverse t1 t2) (reverse (zip ts ts'))
                       _ <- mapM (\j -> edge i j (show (j-i))) idxs
                       return i
          traverse (Pair t1 t2) (Pair t1' t2')
              = do i <- node "pair"
                   i2 <- traverse t2 t2'
                   edge i i2 "snd"
                   i1 <- traverse t1 t1'
                   edge i i1 "fst"
                   return i
          traverse (Fst t) (Fst t')
              = do i <- node "fst"
                   j <- traverse t t'
                   edge i j ""
                   return i
          traverse (Snd t) (Snd t') 
              = do i <- node "snd"
                   j <- traverse t t'
                   edge i j ""
                   return i
          traverse (InL t) (InL t') = 
              do i <- node "inl"
                 j <- traverse t t'
                 edge i j ""
                 return i
          traverse (InR t) (InR t') 
              = do i <- node "inr"
                   j <- traverse t t';
                   edge i j ""
                   return i
          traverse (IfThen t _ _ t1) (IfThen t' _ _ t1')
              = do i <- node "if/t"
                   k <- traverse t1 t1'
                   edge i k "then"
                   j <- traverse t t'
                   edge i j "test"
                   return i
          traverse (IfElse t _ _ t2) (IfElse t' _ _ t2')
              = do i <- node "if/f"
                   k <- traverse t2 t2'
                   edge i k "else"
                   j <- traverse t t'
                   edge i j "test"
                   return i
          traverse (CaseL t _ x t1) (CaseL t' _ _ t1')
              = do i <- node "case/l"
                   k <- traverse t1 t1'
                   edge i k ("inl "++(show x))
                   j <- traverse t t'
                   edge i j "test"
                   return i
          traverse (CaseR t _ x t2) (CaseR t' _ _ t2')
              = do i <- node "case/r"
                   k <- traverse t2 t2'
                   edge i k ("inr "++show x)
                   j <- traverse t t'
                   edge i j "test"
                   return i
          traverse (Call t1 t2 _ t) (Call t1' t2' _ t')
              = do i <- node "app"
                   k <- traverse (body t) (body t')
                   edge i k "call"
                   j2 <- traverse t2 t2'
                   edge i j2 (show (arg t))
                   j1 <- traverse t1 t1'
                   edge i j1 (show (fn t))
                   return i

          traverse (App e1 e2) (App e1' e2')
              = do i <- node "app"
                   j2 <- traverse e2 e2'
                   edge i j2 "NO IDEA WHAT..."
                   j1 <- traverse e1 e1'
                   edge i j1 "THESE STRINGS ARE FOR"
                   return i

          traverse (Roll tv t) (Roll tv' t') 
              | tv == tv'
              = traverse t t'
          traverse (Unroll tv t) (Unroll tv' t') 
              | tv == tv' 
              = traverse t t'

          traverse t Hole = trace2gvG node1 edge t
          traverse Hole t = trace2gvG node2 edge t

          traverse t t' = error "Not safe to throw an exception here..."

          

common_attrs = [GraphAttrs [RankDir FromTop, 
                            Ratio (CompressRatio),
                            Size (Point 7.5 10.0 Nothing False)]]
trace2gv_default t = trace2gv common_attrs (node (X11Color White)) t
traces2gv_default t t' = traces2gv common_attrs (node (X11Color White),
                                       node (X11Color Gray),
                                       node (X11Color Black)) t t'
          
cmd = Dot

visualizePDF :: String -> Trace -> IO (Either String FilePath)
visualizePDF fn t = runGraphvizCommand cmd (trace2gv_default t) Pdf fn

visualizeSVG :: String -> Trace -> IO (Either String FilePath)
visualizeSVG fn t = runGraphvizCommand cmd  (trace2gv_default t) Svg fn

visualize :: Trace -> IO RunResult
visualize t = runGraphvizCanvas' (trace2gv_default t) Xlib

visualize2PDF :: String -> Trace -> Trace -> IO (Either String FilePath)
visualize2PDF fn t t' = runGraphvizCommand cmd (traces2gv_default t t') Pdf fn

visualize2SVG :: String -> Trace -> Trace -> IO (Either String FilePath)
visualize2SVG fn t t' = runGraphvizCommand cmd (traces2gv_default t t') Svg fn

visualize2 :: Trace -> Trace -> IO RunResult
visualize2 t t' = runGraphvizCanvas' (traces2gv_default t t') Xlib
