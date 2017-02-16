module Language.Slicer.Run
    ( parseDesugarEval, desugarEval

    -- * Re-export functions needed to run compilation
    , SlMIO, runSlMIO
    ) where

import           Language.Slicer.Absyn      ( Exp, TyCtx, emptyTyCtx    )
import           Language.Slicer.Core       ( Value, Type, Ctx          )
import           Language.Slicer.Desugar    ( desugar                   )
import           Language.Slicer.Env        ( Env, emptyEnv             )
import           Language.Slicer.Eval       ( run                       )
import           Language.Slicer.Monad      ( SlMIO, liftSlM, runSlMIO  )
import           Language.Slicer.Monad.Eval ( EvalState, emptyEvalState )
import           Language.Slicer.Resugar    ( RExp, resugar             )
import           Language.Slicer.Parser     ( parseIn                   )

-- | Parse a program and evaluate it.  Return value, its resugaring, type and
-- data type context
parseDesugarEval :: String -> SlMIO (Value, RExp, Type, TyCtx, EvalState, Ctx)
parseDesugarEval s = do
  (tyctx, e) <- liftSlM $ parseIn s emptyTyCtx
  (val, res, ty, st, gamma) <- desugarEval tyctx emptyEnv emptyEvalState e
  return (val, res, ty, tyctx, st, gamma)

desugarEval :: TyCtx -> Env Type -> EvalState -> Exp
            -> SlMIO (Value, RExp, Type, EvalState, Ctx)
desugarEval tyCtx gamma evalS expr = do
  (dexpr, ty, gamma') <- liftSlM (desugar tyCtx gamma expr)
  (val, st)           <- run evalS dexpr
  res                 <- liftSlM (resugar tyCtx val)
  return (val, res, ty, st, gamma')
