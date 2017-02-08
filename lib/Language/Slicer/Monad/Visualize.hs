{-# LANGUAGE NamedFieldPuns #-}

module Language.Slicer.Monad.Visualize
    ( GraphM, runGraph, genId, getColor, withColor, addNode, addEdge

    ) where

import           Language.Slicer.Error ( SlicerError )
import           Language.Slicer.Monad ( SlMIO       )

import           Control.Monad.Except
import           Control.Monad.State.Strict
import           Data.GraphViz
import           Data.GraphViz.Attributes.Colors

-- | Convenient aliases to GraphViz types.  Nodes and edges are identified by an
-- Int.  Function that creates a node returns an id that is used when creating
-- edges between nodes
type Node  = DotNode Int
type Edge  = DotEdge Int

-- | State of graph-building monad
data GraphState = GraphState
    { nodes       :: [Node]
    , edges       :: [Edge]
    , counter     :: Int
    , activeColor :: Color
    }

-- | Empty initial state
emptyGraphState :: GraphState
emptyGraphState = GraphState [] [] 0 (X11Color White)

-- | Monad for building graphs
type GraphM = StateT GraphState (ExceptT SlicerError IO)

-- | Run monadic computations that construct a graph and return lists of
-- constructed nodes and edges
runGraph :: GraphM Int -> SlMIO ([Node], [Edge])
runGraph graph = do
    GraphState { nodes, edges } <- execStateT graph emptyGraphState
    return (nodes, edges)

-- | Generate a new unique id for node or edge
genId :: GraphM Int
genId = do
  st@( GraphState { counter } ) <- get
  put (st { counter = counter + 1 })
  return counter

-- | Retrieve active node color
getColor :: GraphM Color
getColor = do
  GraphState { activeColor } <- get
  return activeColor

-- | Set active node color
setColor :: Color -> GraphM ()
setColor clr = do
  st <- get
  put (st { activeColor = clr } )

-- | Add node to the graph
addNode :: Node -> GraphM ()
addNode n = do
  st@( GraphState { nodes } ) <- get
  put (st { nodes = n : nodes } )

-- | Add edge to the graph
addEdge :: Edge -> GraphM ()
addEdge e = do
  st@( GraphState { edges } ) <- get
  put (st { edges = e : edges } )

-- | Runs monadic graph building computations with altered node color
withColor :: Color -> GraphM a -> GraphM a
withColor clr thing = do
  oldClr <- getColor
  setColor clr
  result <- thing
  setColor oldClr
  return result

