{-# LANGUAGE DeriveAnyClass   #-}
{-# LANGUAGE DeriveGeneric    #-}

module Language.Slicer.Primitives
    ( -- * Built-in primitive operators and functions
      Primitive(..), isInfixOp
    ) where

import           Control.DeepSeq ( NFData  )
import           GHC.Generics    ( Generic )
import           Text.PrettyPrint.HughesPJClass

data Primitive
    -- Arithmetic operators
    = OpPlus | OpMinus | OpTimes | OpDiv | OpMod
    -- Integer and boolean comparisons
    | OpEq | OpNeq
    -- Integer comparisons
    | OpLt | OpGt | OpLeq | OpGeq
    -- Logical operators
    | OpAnd | OpOr | OpNot
    -- Builtin functions
    | PrimProfile | PrimProfileDiff | PrimBwdSlice | PrimTraceSlice
    | PrimTreeSize | PrimVal | PrimVisualize | PrimVisualizeDiff
    deriving (Eq, Ord, Generic, NFData)

instance Show Primitive where
    -- Arithmetic operators
    show OpPlus            = "+"
    show OpMinus           = "-"
    show OpTimes           = "*"
    show OpDiv             = "/"
    show OpMod             = "%"
    -- Integer and boolean comparisons
    show OpEq              = "="
    show OpNeq             = "/="
    -- Integer comparisons
    show OpLt              = "<"
    show OpGt              = ">"
    show OpLeq             = "<="
    show OpGeq             = ">="
    -- Logical operators
    show OpAnd             = "&&"
    show OpOr              = "||"
    show OpNot             = "not"
    -- Builtin functions
    show PrimProfile       = "profile"
    show PrimProfileDiff   = "profileDiff"
    show PrimBwdSlice      = "bwdSlice"
    show PrimTraceSlice    = "traceSlice"
    show PrimTreeSize      = "treesize"
    show PrimVal           = "read"
    show PrimVisualize     = "visualize"
    show PrimVisualizeDiff = "visualizeDiff"

instance Pretty Primitive where
    pPrint op = text (show op)

isInfixOp :: Primitive -> Bool
isInfixOp OpPlus  = True
isInfixOp OpMinus = True
isInfixOp OpTimes = True
isInfixOp OpDiv   = True
isInfixOp OpMod   = True
-- Integer and boolean comparisons
isInfixOp OpEq    = True
isInfixOp OpNeq   = True
-- Integer comparisons
isInfixOp OpLt    = True
isInfixOp OpGt    = True
isInfixOp OpLeq   = True
isInfixOp OpGeq   = True
-- Logical operators
isInfixOp OpAnd   = True
isInfixOp OpOr    = True
-- Logical negation and builtin functions
isInfixOp _       = False
