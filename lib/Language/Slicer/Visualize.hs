{-# LANGUAGE NamedFieldPuns #-}

module Language.Slicer.Visualize
    ( -- * Class of things that can be visualized
      Visualizable

    -- * Visualization functions
    , visualizePDF, visualizeDiffPDF, visualizeSVG, visualizeDiffSVG
    ) where

import           Language.Slicer.Core
import           Language.Slicer.Error
import           Language.Slicer.Monad
import           Language.Slicer.Monad.Visualize

import           Control.Monad.Except ( liftIO )
import           Data.GraphViz
import           Data.GraphViz.Attributes.Colors
import           Data.GraphViz.Attributes.Complete
import           Data.Text.Lazy ( pack )
import           Prelude hiding ( id )

-- | Predefined colours.  Used for plotting graph differences
emptyColor, leftColor, rightColor :: Color
emptyColor = X11Color White
leftColor  = X11Color MediumTurquoise
rightColor = X11Color PaleGreen

-- | Construct a new node with a given label and add it to graph
node :: String -> GraphM Int
node lbl = do
  i   <- genId
  clr <- getColor
  addNode ( DotNode i [ FontSize 36.0
                      , Shape BoxShape
                      , Style [SItem Filled []]
                      , FillColor [WC clr Nothing]
                      , Label (StrLabel (pack lbl))
                      ] )
  return i

-- | Create a hole and add it to graph
hole :: GraphM Int
hole = withColor emptyColor (node " ")

-- | Create new edge between nodes with given ids
edge :: Int -> Int -> GraphM ()
edge m m' = addEdge (DotEdge m m' [FontSize 24.0])

-- | Class of things that can be turned into a graph
class Visualizable a where
    -- | Visualize differences between two things.
    -- See Note [Single trace visualization]
    graphDiff :: a -> a -> GraphM Int

instance (Visualizable a, Show a) => Visualizable (Syntax a) where
    graphDiff Hole Hole       = hole
    graphDiff t    Hole       = withColor leftColor  (graphDiff t t)
    graphDiff Hole t          = withColor rightColor (graphDiff t t)
    graphDiff (Var x) (Var _) = node (show x)
    graphDiff Unit Unit       = node "()"
    graphDiff (CBool b) (CBool b')
        | b == b' = node (if b then "true" else "false")
    graphDiff (CInt i) (CInt i')
        | i == i' = node (show i)
    graphDiff (CString s) (CString s')
        | s == s' = node s
    graphDiff (Let x e1 e2) (Let x' e1' e2')
        | x == x' =
        do i  <- node ("let " ++ show x)
           i2 <- graphDiff e2 e2'
           edge i i2
           i1 <- graphDiff e1 e1'
           edge i i1
           return i
    graphDiff (Fun (Rec _ _ funBody _)) (Fun (Rec _ _ funBody' _)) =
        graphDiff funBody funBody'
    graphDiff (Op f ts) (Op f' ts')
        | f == f' =
        do i <- node (show f)
           idxs <- mapM (uncurry graphDiff) (reverse (zip ts ts'))
           mapM_ (edge i) idxs
           return i
    graphDiff (Pair t1 t2) (Pair t1' t2') =
        do i <- node "pair"
           i2 <- graphDiff t2 t2'
           edge i i2
           i1 <- graphDiff t1 t1'
           edge i i1
           return i
    graphDiff (Fst t) (Fst t') =
        do i <- node "fst"
           j <- graphDiff t t'
           edge i j
           return i
    graphDiff (Snd t) (Snd t') =
        do i <- node "snd"
           j <- graphDiff t t'
           edge i j
           return i
    graphDiff (InL t) (InL t') =
        do i <- node "inl"
           j <- graphDiff t t'
           edge i j
           return i
    graphDiff (InR t) (InR t') =
        do i <- node "inr"
           j <- graphDiff t t'
           edge i j
           return i
    graphDiff (Roll   _ t) (Roll   _ t') = graphDiff t t'
    graphDiff (Unroll _ t) (Unroll _ t') = graphDiff t t'
    graphDiff e e' =
        evalError ("Cannot visualize Syntax with different structure. e is "
                   ++ show e ++ " and e' is " ++ show e')

instance Visualizable Exp where
    graphDiff EHole EHole      = hole
    graphDiff t     EHole      = withColor leftColor  (graphDiff t t)
    graphDiff EHole t          = withColor rightColor (graphDiff t t)
    graphDiff (Exp e) (Exp e') = graphDiff e e'
    graphDiff (EApp e1 e2) (EApp e1' e2') = do
      i <- node "app"
      k <- graphDiff e1 e1'
      edge i k
      j <- graphDiff e2 e2'
      edge i j
      return i
    graphDiff (EIf c e1 e2) (EIf c' e1' e2') = do
      i <- node "if"
      l <- graphDiff c c'
      edge i l
      k <- graphDiff e1 e1'
      edge i k
      j <- graphDiff e2 e2'
      edge i j
      return i
    graphDiff (ECase e m) (ECase e' m') = do
      i <- node "case"
      l <- graphDiff e e'
      edge i l
      k <- graphDiff (snd (inL m)) (snd (inL m'))
      edge i k
      j <- graphDiff (snd (inR m)) (snd (inR m'))
      edge i j
      return i
    graphDiff (ETrace t) (ETrace t') = do
      i <- node "trace"
      j <- graphDiff t t'
      edge i j
      return i
    graphDiff e e' =
        evalError ("Cannot visualize Exps with different structure. e is "
                   ++ show e ++ " and e' is " ++ show e')

instance Visualizable Trace where
    graphDiff THole THole = hole
    graphDiff t     THole = withColor leftColor  (graphDiff t t)
    graphDiff THole t     = withColor rightColor (graphDiff t t)
    graphDiff (TExp e) (TExp e') = graphDiff e e'
    graphDiff (TIfThen t _ _ t1) (TIfThen t' _ _ t1') =
        do i <- node "if/t"
           k <- graphDiff t1 t1'
           edge i k
           j <- graphDiff t t'
           edge i j
           return i
    graphDiff (TIfElse t _ _ t2) (TIfElse t' _ _ t2')=
        do i <- node "if/f"
           k <- graphDiff t2 t2'
           edge i k
           j <- graphDiff t t'
           edge i j
           return i
    graphDiff (TCaseL t _ t1) (TCaseL t' _ t1') =
        do i <- node "case/l"
           k <- graphDiff t1 t1'
           edge i k
           j <- graphDiff t t'
           edge i j
           return i
    graphDiff (TCaseR t _ t2) (TCaseR t' _ t2') =
        do i <- node "case/r"
           k <- graphDiff t2 t2'
           edge i k
           j <- graphDiff t t'
           edge i j
           return i
    graphDiff (TCall t1 t2 _ t) (TCall t1' t2' _ t') =
        do i <- node "app"
           k <- graphDiff (funBody t) (funBody t')
           edge i k
           j2 <- graphDiff t2 t2'
           edge i j2
           j1 <- graphDiff t1 t1'
           edge i j1
           return i
    graphDiff t t' =
        evalError ("Cannot visualize Traces with different structure. t is "
                   ++ show t ++ " and t' is " ++ show t')

instance Visualizable Value where
    graphDiff VHole VHole = hole
    graphDiff v     VHole = withColor leftColor  (graphDiff v v)
    graphDiff VHole v     = withColor rightColor (graphDiff v v)
    graphDiff (VBool b) (VBool b')
        | b == b' = node (if b then "true" else "false")
    graphDiff (VInt i) (VInt i')
        | i == i' = node (show i)
    graphDiff (VString s) (VString s')
        | s == s' = node (show s)
    graphDiff VUnit VUnit = node "()"
    graphDiff (VPair v1 v2) (VPair v1' v2')
        = do i <- node "( , )"
             k <- graphDiff v2 v2'
             edge i k
             j <- graphDiff v1 v1'
             edge i j
             return i
    graphDiff (VInL v) (VInL v')
        = do i <- node "inl"
             j <- graphDiff v v'
             edge i j
             return i
    graphDiff (VInR v) (VInR v')
        = do i <- node "inr"
             j <- graphDiff v v'
             edge i j
             return i
    graphDiff (VRoll _ v) (VRoll _ v')
        = do i <- node "roll"
             j <- graphDiff v v'
             edge i j
             return i
    graphDiff (VClosure (Rec funName  _ funBody  _) _)
              (VClosure (Rec funName' _ funBody' _) _)
        | funName == funName'
        = do i <- node ("<closure> " ++ show funName)
             j <- graphDiff funBody funBody'
             edge i j
             return i
    graphDiff VStar VStar = withColor emptyColor (node "*")
    graphDiff (VExp e _) (VExp e' _)
        = graphDiff e e'
    graphDiff (VStoreLoc i) (VStoreLoc i')
        | i == i'
        = node ("<ref " ++ show i ++ ">")
    graphDiff (VTrace _ t _) (VTrace _ t' _)
        = graphDiff t t'
    graphDiff v v' =
        evalError ("Cannot visualize Values with different structure. v is "
                   ++ show v ++ " and v' is " ++ show v')

-- | Default attributes used for drawing graphs
graphAttrs :: [GlobalAttributes]
graphAttrs = [GraphAttrs [ RankDir FromTop
                         , Ratio CompressRatio
                         , Size (GSize 7.5 (Just 10.0) False)
                         ] ]

-- | Visualizes differences between two syntax trees.  Shared parts are
-- visualized in white.  Elements present only in left tree are visualized with
-- blue, those only in the right tree with green.
graphTraceDiff :: Visualizable a => a -> a -> SlMIO (DotGraph Int)
graphTraceDiff t1 t2 = do
  (ns, es) <- runGraph (graphDiff t1 t2)
  return (DotGraph True True (Just (Str (pack "G")))
                   (DotStmts graphAttrs [] ns es))

-- | Common visualization logic
visualize :: Visualizable a => GraphvizOutput -> String -> a -> a -> SlMIO ()
visualize format file t t' =
    do graph <- graphTraceDiff t t'
       _     <- liftIO (runGraphvizCommand Dot graph format file)
       return ()

-- | Visualize a trace to PDF.
visualizePDF :: Visualizable a => String -> a -> SlMIO ()
visualizePDF file t = visualize Pdf file t t

-- | Visualize a trace to SVG
visualizeSVG :: Visualizable a => String -> a -> SlMIO ()
visualizeSVG file t = visualize Svg file t t

-- | Visualize differences between two traces to PDF
visualizeDiffPDF :: Visualizable a => String -> a -> a -> SlMIO ()
visualizeDiffPDF file t t' = visualize Pdf file t t'

-- | Visualize differences between two traces to SVG
visualizeDiffSVG :: Visualizable a => String -> a -> a -> SlMIO ()
visualizeDiffSVG file t t' = visualize Svg file t t'

-- Note [Single trace visualization]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- When visualizing a single trace we piggyback on implementation of graphDiff
-- by passing it the same argument twice.  This will graph whole trace tree in
-- default color.
