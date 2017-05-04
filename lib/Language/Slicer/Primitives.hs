{-# LANGUAGE DeriveAnyClass   #-}
{-# LANGUAGE DeriveGeneric    #-}

module Language.Slicer.Primitives
    ( -- * Built-in primitive operators and functions
      Primitive(..), isInfixOp, acceptsExns
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
    | PrimBwdSlice | PrimTraceSlice | PrimVal
    deriving (Eq, Ord, Generic, NFData)

instance Show Primitive where
    -- Arithmetic operators
    show OpPlus            = "+"
    show OpMinus           = "-"
    show OpTimes           = "*"
    show OpDiv             = "/"
    show OpMod             = "%"
    -- Integer and boolean comparisons
    show OpEq              = "=="
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
    show PrimBwdSlice      = "bwdSlice"
    show PrimTraceSlice    = "traceSlice"
    show PrimVal           = "read"

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

-- | Does operator accept exception values as arguments?
acceptsExns :: Primitive -> Bool
acceptsExns PrimBwdSlice      = True
acceptsExns PrimTraceSlice    = True
acceptsExns PrimVal           = True
acceptsExns _                 = False
