module Language.Slicer.API
    ( -- * Compiling and running the code
     parseDesugarEval, desugarEval, SlMIO, runSlMIO

    -- * REPL interface
    , ReplM, runRepl, parseAndEvalLine

    -- * Parsing result
    , ParseResult(..)

    -- * Pretty-printing
    , pp
    ) where

import           Language.Slicer.Repl
import           Language.Slicer.Run
import           Language.Slicer.PrettyPrinting
