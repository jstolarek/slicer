module Language.Slicer.Eval
    ( evalOp
    )  where

import           Language.Slicer.Core       ( Value     )
import           Language.Slicer.Monad      ( SlM       )
import           Language.Slicer.Primitives ( Primitive )

evalOp :: Primitive -> [Value] -> SlM Value
