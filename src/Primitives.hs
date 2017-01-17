module Primitives
    ( -- * Built-in primitive operators and functions
      Primitive(..)
    ) where

import           PrettyPrinting

import           Text.PrettyPrint

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
    | PrimDep | PrimExpr | PrimProfile | PrimProfile2 | PrimPSlice
    | PrimSlice | PrimTreeSize | PrimVal | PrimVisualize | PrimVisualize2
    | PrimWhere
    deriving (Eq, Ord)

instance Show Primitive where
    -- Arithmetic operators
    show OpPlus         = "+"
    show OpMinus        = "-"
    show OpTimes        = "*"
    show OpDiv          = "/"
    show OpMod          = "%"
    -- Integer and boolean comparisons
    show OpEq           = "="
    show OpNeq          = "/="
    -- Integer comparisons
    show OpLt           = "<"
    show OpGt           = ">"
    show OpLeq          = "<="
    show OpGeq          = ">="
    -- Logical operators
    show OpAnd          = "&&"
    show OpOr           = "||"
    show OpNot          = "not"
    -- Builtin functions
    show PrimDep        = "dep"
    show PrimExpr       = "expr"
    show PrimProfile    = "profile"
    show PrimProfile2   = "profile2"
    show PrimPSlice     = "pslice"
    show PrimSlice      = "slice"
    show PrimTreeSize   = "treesize"
    show PrimVal        = "read"
    show PrimVisualize  = "visualize"
    show PrimVisualize2 = "visualize2"
    show PrimWhere      = "where"

instance PP Primitive where
    pp op = text (show op)
    pp_partial op op' | op == op' = pp op
    pp_partial op op' = error ("Error pretty-printing Op: op is " ++ show op ++
                               " and op' is " ++ show op')
