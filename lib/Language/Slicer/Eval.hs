{-# LANGUAGE FlexibleContexts #-}

module Language.Slicer.Eval
    ( -- * Evaluating TML expressions
      eval, run
    ) where

import           Language.Slicer.Core
import           Language.Slicer.Env
import           Language.Slicer.Error
import           Language.Slicer.Monad
import           Language.Slicer.Monad.Eval
import           Language.Slicer.Primitives
import           Language.Slicer.Profile
import           Language.Slicer.Slice
import           Language.Slicer.Visualize
import           Language.Slicer.TraceTree
import           Language.Slicer.UpperSemiLattice

import           Control.Exception
import           Control.Monad.Except
import           Data.Map  ( (!) )
import           System.FilePath.Posix

-- All monadic computations in this module will use environment of Values
type EvalMV = EvalM Value

run :: EvalState Value -> Exp -> SlMIO (Value, EvalState Value)
run env e = runEvalM env (evalM e)

eval :: Env Value -> Exp -> SlMIO Value
eval env e = evalEvalM env (evalM e)

evalM :: Exp -> EvalMV Value
evalM EHole           = return VHole
evalM (EVar x)        = do env <- getEnv
                           return (lookupEnv' env x)
evalM (ELet x e1 e2)  = do v <- evalM' e1
                           withBinder x v (evalM' e2)
evalM  EUnit          = return VUnit
evalM (EBool b)       = return (VBool b)
evalM (EIf e e1 e2)   = do cond <- evalM' e
                           evalIf cond e1 e2
evalM (EInt i)        = return (VInt i)
evalM (EString s)     = return (VString s)
evalM (EOp f exps)    = do exps' <- mapM evalM' exps
                           evalTraceOp f exps'
evalM (EPair e1 e2)   = do e1' <- evalM' e1
                           e2' <- evalM' e2
                           return (VPair e1' e2')
evalM (EFst e)        = do (VPair v1 _) <- evalM' e
                           return v1
evalM (ESnd e)        = do (VPair _ v2) <- evalM' e
                           return v2
evalM (EInL e)        = do e' <- evalM' e
                           return (VInL e')
evalM (EInR e)        = do e' <- evalM' e
                           return (VInR e')
evalM (ECase e m)     = do e' <- evalM' e
                           evalMatch e' m
evalM (EFun k)        = do env <- getEnv
                           return (VClosure k env)
evalM (EApp e1 e2)    = do e1' <- evalM' e1
                           e2' <- evalM' e2
                           evalCall e1' e2'
evalM (ERoll tv e)    = do e' <- evalM' e
                           return (VRoll tv e')
evalM (EUnroll tv e)  = do (VRoll tv' v) <- evalM' e
                           assert (tv == tv') (return v)
evalM (ETrace e)      = do env    <- getEnv
                           (v, t) <- trace e
                           return (VTrace v t env)
-- References
evalM (ERef e)        = do v <- evalM' e
                           newRef v
evalM (EDeref e)      = do v <- evalM' e
                           getRef v
evalM (EAssign e1 e2) = do e1' <- evalM' e1
                           e2' <- evalM' e2
                           updateRef e1' e2'
                           return VUnit
evalM (ESeq e1 e2)    = do VUnit <- evalM' e1
                           evalM' e2
-- Exceptions.  See Note [Evaluation of exceptions]
evalM (ERaise e)      = do v <- evalM' e
                           st <- getStore
                           raise v st
evalM (ECatch e x h)  = do st  <- getEvalState
                           res <- runSlMIO (run st e)
                           case res of
                             Right (v, st') ->
                                 do setEvalState st'
                                    return v
                             Left (Exception v st') ->
                                 do setStore st'
                                    withBinder x v (evalM' h)
                             Left err -> rethrow err
-- This will never happen because the above matches cover all cases.  But the
-- pattern exhaustiveness checker doesn't see that because we're using pattern
-- synonym.  See GHC bug #8779.  Hopefully GHC 8.2 will ship a fix.
evalM _ = error "Impossible happened in evalM"

-- | Evaluates an expression and forces the result before returning it.  Ensures
-- strict semantics.
evalM' :: Exp -> EvalMV Value
evalM' e = do v <- evalM e
              v `seq` return v

-- Note [Evaluation of exceptions]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- Evaluation of exceptions piggybacks on the fact, that our evaluation monad is
-- also an error monad.

-- When evaluating a "raise" construct we simply throw an exception.  Note that
-- thrown exception also carries the reference store so that changes made to the
-- store before the exception was thrown are not lost.
--
-- When evaluating the try-with block we run and fully unwrap the monadic
-- computations inside the block.  If the block did not raise an error we set
-- its return state as the current state and return normally.  If an exception
-- was raised by the program we restore the reference store passed in the
-- exception and evaluate the handler.  If interpreter raised evaluation error
-- we rethrow error so that it can be handled somewhere at the top level.
--
-- The upside of this approach is that the code responsible for evaluating
-- exceptions is fully enclosed inside two cases of `evalM`.  The downside is
-- that we conflate language exceptions and interpreter errors into one
-- representation, which is not very elegant conceptually.


evalCall :: Value -> Value -> EvalMV Value
evalCall v1@(VClosure k env0) v2 =
    do let envf  = bindEnv env0 (funName k) v1
           envfx = bindEnv envf (funArg k) v2
       withEnv envfx (evalM (funBody k))
evalCall _ _ = evalError "evalCall: cannot call non-VClosure values"

evalMatch :: Value -> Match -> EvalMV Value
evalMatch (VInL v) m
    = let (x, e) = inL m
      in maybeWithBinder x v (evalM' e)
evalMatch (VInR v) m
    = let (x, e) = inR m
      in maybeWithBinder x v (evalM' e)
evalMatch _ _
    = evalError "evalMatch: scrutinee does not reduce to a constructor"

evalIf :: Value -> Exp -> Exp -> EvalMV Value
evalIf (VBool True ) e1 _  = evalM' e1
evalIf (VBool False) _  e2 = evalM' e2
evalIf _ _ _ = evalError "evalIf: condition is not a VBool value"

evalTraceOp :: Primitive -> [Value] -> EvalMV Value
evalTraceOp PrimVal [VTrace v _ _] = return v
evalTraceOp PrimSlice [VTrace v t env, p]
    | p `leq` v
    = do let (t',penv) = bslice p t
             v'        = extract p v
             env'      = extract penv env
         v' `seq` t' `seq` env' `seq` return (VTrace v' t' env')
    | otherwise = evalError ("slice: criterion " ++ show p ++
                             " is not a prefix of output " ++ show v)
evalTraceOp PrimPSlice [VTrace v t _, p]
    | p `leq` v
    = do let (t',env') = pslice p t
         return (VExp t' env')
    | otherwise = evalError ("pslice: criterion "++ show p ++
                             " is not a prefix of output " ++ show v)
evalTraceOp PrimVisualize [VString s, v]
    = case takeExtension s of
        ".pdf" -> lift (visualizePDF s v) >> return VUnit
        ".svg" -> lift (visualizeSVG s v) >> return VUnit
        ext    -> evalError $ "visualizeDiff: unknown file extension : " ++ ext
evalTraceOp PrimVisualizeDiff [VString s, v1, v2]
    = case takeExtension s of
        ".pdf" -> lift (visualizeDiffPDF s v1 v2) >> return VUnit
        ".svg" -> lift (visualizeDiffSVG s v1 v2) >> return VUnit
        ext    -> evalError $ "visualizeDiff: unknown file extension : " ++ ext
evalTraceOp PrimTreeSize [VTrace _ t _] =
    return (VInt (forestsize (toTree t)))
evalTraceOp PrimProfile [VTrace _ t _]
    = do liftIO $ putStrLn (show (profile t))
         return VUnit
evalTraceOp PrimProfileDiff [VTrace _ t _]
    = do liftIO $ putStrLn (show (profileDiff t))
         return VUnit
evalTraceOp op vs = liftEvalM $ evalOp op vs

evalOp :: Primitive -> [Value] -> SlM Value
evalOp f [VInt    i, VInt    j] | isCommonOp  f = return ((commonOps ! f) (i,j))
evalOp f [VBool   i, VBool   j] | isCommonOp  f = return ((commonOps ! f) (i,j))
evalOp f [VString i, VString j] | isCommonOp  f = return ((commonOps ! f) (i,j))
evalOp f [VInt    i, VInt    j] | isIntBinOp  f = return ((intBinOps ! f) (i,j))
evalOp f [VInt    i, VInt    j] | isIntRelOp  f = return ((intRelOps ! f) (i,j))
evalOp f [VBool   i, VBool   j] | isBoolRelOp f = return ((boolRelOps! f) (i,j))
evalOp f [VBool   b]            | isBoolUnOp  f = return ((boolUnOps ! f) b)
evalOp _ vs                     | VHole `elem` vs = return VHole
evalOp _ vs                     | VStar `elem` vs = return VStar
evalOp f vs = evalError ("Op " ++ show f ++ " not defined for " ++ show vs)

-- Tracing as described in Section 4.2 of ICFP'12 paper
trace :: Exp -> EvalMV (Value, Trace)
trace EHole          = return (VHole, THole)
trace (EVar x)       = do env <- getEnv
                          return (lookupEnv' env x, TVar x)
trace (ELet x e1 e2) = do (v1, t1) <- trace' e1
                          (v2, t2) <- withBinder x v1 (trace' e2)
                          v1 `seq` return (v2, TLet x t1 t2)
trace  EUnit         = return (VUnit, TUnit)
trace (EBool b)      = return (VBool b, TBool b)
trace (EIf e e1 e2)  = do e' <- trace' e
                          traceIf e' e1 e2
trace (EInt i)       = return (VInt i, TInt i)
trace (EString s)    = return (VString s, TString s)
trace (EOp f exps)   = do vts <- mapM trace' exps
                          traceOp f vts
trace (EPair e1 e2)  = do (v1, t1) <- trace' e1
                          (v2, t2) <- trace' e2
                          return (VPair v1 v2, TPair t1 t2)
trace (EFst e)       = do (VPair v1 _, t) <- trace' e
                          return (v1, TFst t)
trace (ESnd e)       = do (VPair _ v2, t) <- trace' e
                          return (v2, TSnd t)
trace (EInL e)       = do (v, t) <- trace' e
                          return (VInL v, TInL t)
trace (EInR e)       = do (v, t) <- trace' e
                          return (VInR v, TInR t)
trace (ECase e m)    = do e' <- trace' e
                          traceMatch e' m
trace (EFun k)       = do env <- getEnv
                          return (VClosure k env, TFun k)
trace (EApp e1 e2)   = do e1' <- trace' e1
                          e2' <- trace' e2
                          traceCall e1' e2'
trace (ERoll tv e)   = do (v, t) <- trace' e
                          return (VRoll tv v, TRoll tv t)
trace (EUnroll tv e) = do (VRoll tv' v, t) <- trace' e
                          assert (tv == tv') (return (v, TUnroll tv t))
trace (ETrace _)     = evalError "Cannot trace a trace"
trace t =
   evalError $ "Cannot trace: " ++ show t

trace' :: Exp -> EvalMV (Value, Trace)
trace' e = do (v, t) <- trace e
              v `seq` return (v, t)

traceOp :: Primitive -> [(Value,Trace)] -> EvalMV (Value, Trace)
traceOp f vts = do let (vs,ts) = unzip vts
                   v <- evalTraceOp f vs
                   return (v, TOp f ts)

traceCall :: (Value, Trace) -> (Value, Trace) -> EvalMV (Value, Trace)
traceCall (v1@(VClosure k env0), t1) (v2, t2)
    = do let envf  = bindEnv env0 (funName k) v1
             envfx = bindEnv envf (funArg  k) v2
         (v,t) <- withEnv envfx (trace' (funBody k))
         return (v, TCall t1 t2 (funLabel k)
                         (Rec (funName k) (funArg k) t Nothing))
traceCall _ _ = evalError "traceCall: cannot call non-VClosure values"

traceMatch :: (Value, Trace) -> Match -> EvalMV (Value, Trace)
traceMatch (VInL v, t) m
    = do let (x, e) = inL m
         (v1,t1) <- maybeWithBinder x v (trace' e)
         return (v1, TCaseL t x t1)
traceMatch (VInR v, t) m
    = do let (x, e) = inR m
         (v2,t2) <- maybeWithBinder x v (trace' e)
         return (v2, TCaseR t x t2)
traceMatch _ _ =
    evalError "traceMatch: scrutinee does not reduce to a constructor"

traceIf :: (Value, Trace) -> Exp -> Exp -> EvalMV (Value, Trace)
traceIf (VBool True , t) e1 e2 = do (v1,t1) <- trace' e1
                                    return (v1, TIfThen t e1 e2 t1)
traceIf (VBool False, t) e1 e2 = do (v2,t2) <- trace' e2
                                    return (v2, TIfElse t e1 e2 t2)
traceIf _ _ _ = evalError "traceIf: condition is not a VBool value"