module Language.Slicer.Run
    ( parseDesugarEval, desugarEval

    -- * Re-export functions needed to run compilation
    , SlM, runSlM
    ) where

import           Language.Slicer.Absyn      ( Exp, TyCtx, emptyTyCtx    )
import           Language.Slicer.Core       ( Type, Outcome             )
import           Language.Slicer.Desugar    ( desugar                   )
import           Language.Slicer.Env        ( Env, emptyEnv             )
import           Language.Slicer.Eval       ( run                       )
import           Language.Slicer.Monad      ( SlM, runSlM               )
import           Language.Slicer.Monad.Eval ( EvalState, emptyEvalState )
import           Language.Slicer.Resugar    ( RExp, resugar             )
import           Language.Slicer.Parser     ( parseIn                   )

-- | Parse a program and evaluate it.  Return value, its resugaring, type and
-- data type context
parseDesugarEval :: String -> SlM (Outcome, RExp, Type, TyCtx)
parseDesugarEval s = do
  (tyctx, e) <- parseIn s emptyTyCtx
  (val, res, ty, _) <- desugarEval tyctx emptyEnv emptyEvalState e
  return (val, res, ty, tyctx)

desugarEval :: TyCtx -> Env Type -> EvalState -> Exp
            -> SlM (Outcome, RExp, Type, EvalState)
desugarEval tyCtx gamma evalS expr = do
  (dexpr, ty) <- desugar tyCtx gamma expr
  (val, st)   <- run evalS dexpr
  res         <- resugar tyCtx val
  return (val, res, ty, st)
