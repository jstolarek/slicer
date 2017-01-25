module Language.Slicer.Eval
    ( -- * Evaluating TML expressions
      eval, evalOp
    ) where

import           Language.Slicer.Annot
import           Language.Slicer.Core
import           Language.Slicer.Env
import           Language.Slicer.Error
import           Language.Slicer.Monad
import           Language.Slicer.Monad.Eval
import           Language.Slicer.PrettyPrinting
import           Language.Slicer.Primitives
import           Language.Slicer.Profile
import           Language.Slicer.Slice
import           Language.Slicer.TraceGraph
import           Language.Slicer.TraceTree
import           Language.Slicer.UpperSemiLattice

import           Control.Exception
import           Control.Monad.Except
import           Data.Map  ( (!) )
import           System.FilePath.Posix

-- All monadic computations in this module will use environment of Values
type EvalMV = EvalM Value

eval :: Env Value -> Exp -> SlMIO Value
eval env e = runEvalM env (evalM e)

evalM :: Exp -> EvalMV Value
evalM Hole          = return VHole
evalM (Var x)       = do env <- getEnv
                         return (lookupEnv' env x)
evalM (Let x e1 e2) = do v <- evalM' e1
                         withBinder x v (evalM' e2)
evalM (Unit)        = return VUnit
evalM (CBool b)     = return (VBool b)
evalM (If e e1 e2)  = do cond <- evalM' e
                         evalIf cond e1 e2
evalM (CInt i)      = return (VInt i)
evalM (CString s)   = return (VString s)
evalM (Op f exps)   = do exps' <- mapM evalM' exps
                         evalTraceOp f exps'
evalM (Pair e1 e2)  = do e1' <- evalM' e1
                         e2' <- evalM' e2
                         return (VPair e1' e2')
evalM (Fst e)       = do (VPair v1 _) <- evalM' e
                         return v1
evalM (Snd e)       = do (VPair _ v2) <- evalM' e
                         return v2
evalM (InL e)       = do e' <- evalM' e
                         return (VInL e')
evalM (InR e)       = do e' <- evalM' e
                         return (VInR e')
evalM (Case e m)    = do e' <- evalM' e
                         evalMatch e' m
evalM (Fun k)       = do env <- getEnv
                         return (VClosure k env)
evalM (App e1 e2)   = do e1' <- evalM' e1
                         e2' <- evalM' e2
                         evalCall e1' e2'
evalM (Roll tv e)   = do e' <- evalM' e
                         return (VRoll tv e')
evalM (Unroll tv e) = do (VRoll tv' v) <- evalM' e
                         assert (tv == tv') (return v)
evalM (Trace e)     = do env    <- getEnv
                         (v, t) <- trace e
                         return (VTrace v t env)
evalM (Ref e)       = do v <- eval' e
                         newRef v
evalM (Deref e)     = do v <- eval' e
                         getRef v
evalM (Assign x e1 e2) = do x'  <- eval' (Var x)
                            e1' <- eval' e1
                            updateRef x' e1'
                            eval' e2

--evalM e             = evalError ("Cannot eval: " ++ show e)

-- | Evaluates an expression and forces the result before returning it.  Ensures
-- strict semantics.
evalM' :: Exp -> EvalMV Value
evalM' e = do v <- evalM e
              v `seq` return v

evalCall :: Value -> Value -> EvalMV Value
evalCall v1@(VClosure k env0) v2 =
    do let envf  = bindEnv env0 (funName k) v1
           envfx = bindEnv envf (funArg k) v2
       withEnv envfx (evalM (funBody k))
evalCall _ _ = evalError "evalCall: cannot call non-VClosure values"

evalMatch :: Value -> Match -> EvalMV Value
evalMatch (VInL v) m
    = let (x, e) = inL m
      in withBinder x v (evalM' e)
evalMatch (VInR v) m
    = let (x, e) = inR m
      in withBinder x v (evalM' e)
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
         return (VTrace p t' env')
    | otherwise = evalError ("pslice: criterion "++ show p ++
                             " is not a prefix of output " ++ show v)
evalTraceOp PrimWhere [VTrace _ t env]
    = do let env' = fmap make_where env
         v' <- lift $ whr env' t
         liftIO $ putStrLn (show (pp v'))
         return $ erase_to_v v'
evalTraceOp PrimExpr [VTrace _ t env]
    = do let env' = fmap make_expr env
         v' <- lift $ expr env' t
         liftIO $ putStrLn (show (pp v'))
         return $ erase_to_v v'
evalTraceOp PrimDep [VTrace _ t env]
    = do let env' = fmap make_dep env
         v' <- lift $ dep env' t
         liftIO $ putStrLn (show ( pp v'))
         return $ erase_to_v v'
evalTraceOp PrimVisualize [VString s, VTrace _ t _]
    = do case takeExtension s of
           ".pdf" -> liftIO (visualizePDF s t) >> return VUnit
           ".svg" -> liftIO (visualizeSVG s t) >> return VUnit
           ext    -> evalError $ "visualize: unknown file extension : " ++ ext
evalTraceOp PrimVisualizeDiff [VString s, VTrace _ t1 _, VTrace _ t2 _]
    = do case takeExtension s of
           ".pdf" -> liftIO (visualizeDiffPDF s t1 t2) >> return VUnit
           ".svg" -> liftIO (visualizeDiffSVG s t1 t2) >> return VUnit
           ext    -> evalError $ "visualizeDiff: unknown file extension : " ++
                                 ext
evalTraceOp PrimTreeSize [VTrace _ t _] =
    return (VInt (forestsize (to_tree t)))
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
trace (Var x)       = do env <- getEnv
                         return (lookupEnv' env x, Var x)
trace (Let x e1 e2) = do (v1, t1) <- trace' e1
                         (v2, t2) <- withBinder x v1 (trace' e2)
                         v1 `seq` return (v2, Let x t1 t2)
trace (Unit)        = return (VUnit, Unit)
trace (CBool b)     = return (VBool b, CBool b)
trace (If e e1 e2)  = do e' <- trace' e
                         traceIf e' e1 e2
trace (CInt i)      = return (VInt i, CInt i)
trace (CString s)   = return (VString s, CString s)
trace (Op f exps)   = do vts <- mapM trace' exps
                         traceOp f vts
trace (Pair e1 e2)  = do (v1, t1) <- trace' e1
                         (v2, t2) <- trace' e2
                         return (VPair v1 v2, Pair t1 t2)
trace (Fst e)       = do (VPair v1 _, t) <- trace' e
                         return (v1, Fst t)
trace (Snd e)       = do (VPair _ v2, t) <- trace' e
                         return (v2, Snd t)
trace (InL e)       = do (v, t) <- trace' e
                         return (VInL v, InL t)
trace (InR e)       = do (v, t) <- trace' e
                         return (VInR v, InR t)
trace (Case e m)    = do e' <- trace' e
                         traceMatch e' m
trace (Fun k)       = do env <- getEnv
                         return (VClosure k env, Fun k)
trace (App e1 e2)   = do e1' <- trace' e1
                         e2' <- trace' e2
                         traceCall e1' e2'
trace (Roll tv e)   = do (v, t) <- trace' e
                         return (VRoll tv v, Roll tv t)
trace (Unroll tv e) = do (VRoll tv' v, t) <- trace' e
                         assert (tv == tv') (return (v, Unroll tv t))
-- replay cases
trace (IfThen t e1 e2 t1)
    = do tr <- trace' t
         case tr of
           (VBool True, t') -> do (v1, t1') <- trace' t1
                                  return (v1, IfThen t' e1 e2 t1')
           (v, t') -> traceIf (v, t') e1 e2
trace (IfElse t e1 e2 t2)
    = do tr <- trace' t
         case tr of
           (VBool False, t') -> do (v1, t2') <- trace' t2
                                   return (v1, IfElse t' e1 e2 t2')
           (v, t') -> traceIf (v, t') e1 e2
trace (CaseL t m x t1)
    = do tr <- trace' t
         case tr of
           (VInL v, t') -> do (v1, t1') <- withBinder x v (trace' t1)
                              return (v1, CaseL t' m x t1')
           v -> traceMatch v m
trace (CaseR t m x t2)
    = do tr <- trace' t
         case tr of
           (VInR v, t') -> do (v2, t2') <- withBinder x v (trace' t2)
                              return (v2, CaseR t' m x t2')
           v -> traceMatch v m
trace (Call t1 t2 _ _)
    = do (VClosure k' env0, t1') <- trace' t1
         (v2, t2')               <- trace' t2
         traceCall (VClosure k' env0, t1') (v2, t2')
trace (Trace e)
    = do env    <- getEnv
         (v, t) <- trace' e
         return (VTrace v t env, Trace t)
trace t =
   evalError $ "Cannot trace: " ++ show t

trace' :: Exp -> EvalMV (Value, Trace)
trace' e = do (v, t) <- trace e
              v `seq` return (v, t)

traceOp :: Primitive -> [(Value,Trace)] -> EvalMV (Value, Trace)
traceOp f vts = do let (vs,ts) = unzip vts
                   v <- evalTraceOp f vs
                   return (v, Op f ts)

traceCall :: (Value, Trace) -> (Value, Trace) -> EvalMV (Value, Exp)
traceCall (v1@(VClosure k env0), t1) (v2, t2)
    = do let envf  = bindEnv env0 (funName k) v1
             envfx = bindEnv envf (funArg  k) v2
         (v,t) <- withEnv envfx (trace' (funBody k))
         return (v, Call t1 t2 k (Rec (funName k) (funArg k) t Nothing))
traceCall _ _ = evalError "traceCall: cannot call non-VClosure values"

traceMatch :: (Value, Trace) -> Match -> EvalMV (Value, Exp)
traceMatch (VInL v, t) m
    = do let (x, e) = inL m
         (v1,t1) <- withBinder x v (trace' e)
         return (v1, CaseL t m x t1)
traceMatch (VInR v, t) m
    = do let (x, e) = inR m
         (v2,t2) <- withBinder x v (trace' e)
         return (v2, CaseR t m x t2)
traceMatch _ _ =
    evalError "traceMatch: scrutinee does not reduce to a constructor"

traceIf :: (Value, Trace) -> Exp -> Exp -> EvalMV (Value, Exp)
traceIf (VBool True , t) e1 e2 = do (v1,t1) <- trace' e1
                                    return (v1, IfThen t e1 e2 t1)
traceIf (VBool False, t) e1 e2 = do (v2,t2) <- trace' e2
                                    return (v2, IfElse t e1 e2 t2)
traceIf _ _ _ = evalError "traceIf: condition is not a VBool value"
