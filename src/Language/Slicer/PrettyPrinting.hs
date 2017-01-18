module Language.Slicer.PrettyPrinting
    ( -- * Pretty-printing
      PP(..), sb
    ) where

import           Text.PrettyPrint

class PP a where
    pp :: a -> Doc
    pp a = pp_partial a a
    pp_partial :: a -> a -> Doc

sb :: Doc -> Doc
sb x =  brackets (text "|" <> x <> text "|")
