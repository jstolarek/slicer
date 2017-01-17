module Eval
    ( -- * Evaluating TML expressions
      eval
    ) where

import           Annot
import           Env
import           Monad
import           PrettyPrinting
import           Primitives
import           Profile
import           Slice
import           Trace
import           TraceGraph
import           TraceTree
import           UpperSemiLattice

import           Control.Exception
import           System.IO.Unsafe(unsafePerformIO)
import           System.FilePath.Posix

evalTraceOp :: Primitive -> [Value] -> SlM Value
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
         v' <- whr env' t
         System.IO.Unsafe.unsafePerformIO (putStrLn (show ( pp v')))
           `seq` erase_to_v v'
evalTraceOp PrimExpr [VTrace _ t env]
    = do let env' = fmap make_expr env
         v' <- expr env' t
         System.IO.Unsafe.unsafePerformIO (putStrLn (show ( pp v')))
           `seq` erase_to_v v'
evalTraceOp PrimDep [VTrace _ t env]
    = do let env' = fmap make_dep env
         v' <- dep env' t
         System.IO.Unsafe.unsafePerformIO (putStrLn (show ( pp v')))
           `seq` erase_to_v v'
evalTraceOp PrimVisualize [VString s, VTrace _ t _] =
    (case takeExtension s
     of ".pdf" -> System.IO.Unsafe.unsafePerformIO (visualizePDF s t)
        ".svg" -> System.IO.Unsafe.unsafePerformIO (visualizeSVG s t)
        ext    -> error $ "Unknown file extension : " ++ ext)
    `seq` return VUnit
evalTraceOp PrimVisualize2 [VString s, VTrace _ t1 _, VTrace _ t2 _] =
    (case takeExtension s
     of ".pdf" -> System.IO.Unsafe.unsafePerformIO (visualize2PDF s t1 t2)
        ".svg" -> System.IO.Unsafe.unsafePerformIO (visualize2SVG s t1 t2)
        ext    -> error $ "Unknown file extension : " ++ ext)
    `seq` return VUnit

evalTraceOp PrimTreeSize [VTrace _ t _] =
    return (VInt (forestsize (to_tree t)))

evalTraceOp PrimProfile [VTrace _ t _] =
    System.IO.Unsafe.unsafePerformIO (putStrLn (show (profile t)))
    `seq` return VUnit
evalTraceOp PrimProfile2 [VTrace _ t _] =
    System.IO.Unsafe.unsafePerformIO (putStrLn (show (profile2 t)))
    `seq` return VUnit
evalTraceOp op vs = evalOp op vs

eval :: Env Value -> Exp -> SlM Value
eval _   Hole              = return VHole
eval env (Var x)           = return (lookupEnv' env x)
eval env (Let x e1 e2)     = do v <- eval' env e1
                                eval' (bindEnv env x v) e2
eval _   (Unit)            = return VUnit
eval _   (CBool b)         = return (VBool b)
eval env (If e e1 e2)      = do cond <- eval' env e
                                evalIf env cond e1 e2
eval _   (CInt i)          = return (VInt i)
eval _   (CString s)       = return (VString s)
eval env (Op f exps)       = do exps' <- mapM (eval' env) exps
                                evalTraceOp f exps'
eval env (Pair e1 e2)      = do e1' <- eval' env e1
                                e2' <- eval' env e2
                                return (VPair e1' e2')
eval env (Fst e)           = do (VPair v1 _) <- eval' env e
                                return v1
eval env (Snd e)           = do (VPair _ v2) <- eval' env e
                                return v2
eval env (InL e)           = do e' <- eval' env e
                                return (VInL e')
eval env (InR e)           = do e' <- eval' env e
                                return (VInR e')
eval env (Case e m)        = do e' <- eval' env e
                                evalMatch env e' m
eval env (Fun k)           = return (VClosure k env)
eval env (App e1 e2)       = do e1' <- eval' env e1
                                e2' <- eval' env e2
                                evalCall e1' e2'
eval env (Roll tv e)       = do e' <- eval' env e
                                return (VRoll tv e')
eval env (Unroll tv e)     = do (VRoll tv' v) <- eval' env e
                                assert (tv == tv') (return v)
eval env (Trace e)         = do (v, t) <- trace env e
                                return (VTrace v t env)
eval _   e                 = evalError ("Cannot eval: " ++ show e)

eval' :: Env Value -> Exp -> SlM Value
eval' env e = do v <- eval env e
                 v `seq` return v

evalCall :: Value -> Value -> SlM Value
evalCall v1@(VClosure k env0) v2 =
    do let envf  = bindEnv env0 (funName k) v1
           envfx = bindEnv envf (funArg k) v2
       eval envfx (funBody k)
evalCall _ _ = evalError "evalCall: cannot call non-VClosure values"

evalMatch :: Env Value -> Value -> Match -> SlM Value
evalMatch env (VInL v) m
    = do let (x, e) = inL m
             env' = bindEnv env x v
         eval' env' e
evalMatch env (VInR v) m
    =  let (x, e) = inR m
           env'   = bindEnv env x v
       in eval' env' e
evalMatch _ _ _
    = evalError "evalMatch: scrutinee does not reduce to a constructor"

evalIf :: Env Value -> Value -> Exp -> Exp -> SlM Value
evalIf env (VBool True ) e1 _  = eval' env e1
evalIf env (VBool False) _  e2 = eval' env e2
evalIf _ _ _ _ = evalError "evalIf: condition is not a VBool value"


-- Tracing as described in Section 4.2 of ICFP'12 paper
trace :: Env Value -> Exp -> SlM (Value, Trace)
trace env (Var x)       = return (lookupEnv' env x,Var x)
trace env (Let x e1 e2) = do (v1, t1) <- trace' env e1
                             (v2, t2) <- trace' (bindEnv env x v1) e2
                             v1 `seq` return (v2, Let x t1 t2)
trace _   (Unit)        = return (VUnit, Unit)
trace _   (CBool b)     = return (VBool b, CBool b)
trace env (If e e1 e2)  = do e' <- trace' env e
                             traceIf env e' e1 e2
trace _   (CInt i)      = return (VInt i, CInt i)
trace _   (CString s)   = return (VString s, CString s)
trace env (Op f exps)   = do vts <- mapM (trace' env) exps
                             traceOp f vts
trace env (Pair e1 e2)  = do (v1, t1) <- trace' env e1
                             (v2, t2) <- trace' env e2
                             return (VPair v1 v2, Pair t1 t2)
trace env (Fst e)       = do (VPair v1 _, t) <- trace' env e
                             return (v1, Fst t)
trace env (Snd e)       = do (VPair _ v2, t) <- trace' env e
                             return (v2, Snd t)
trace env (InL e)       = do (v, t) <- trace' env e
                             return (VInL v, InL t)
trace env (InR e)       = do (v, t) <- trace' env e
                             return (VInR v, InR t)
trace env (Case e m)    = do e' <- trace' env e
                             traceMatch env e' m
trace env (Fun k)       = return (VClosure k env, Fun k)
trace env (App e1 e2)   = do e1' <- trace' env e1
                             e2' <- trace' env e2
                             traceCall e1' e2'
trace env (Roll tv e)   = do (v, t) <- trace' env e
                             return (VRoll tv v, Roll tv t)
trace env (Unroll tv e) = do (VRoll tv' v, t) <- trace' env e
                             assert (tv == tv') (return (v, Unroll tv t))
-- replay cases
trace env (IfThen t e1 e2 t1)
    = do tr <- trace' env t
         case tr of
           (VBool True, t') -> do (v1, t1') <- trace' env t1
                                  return (v1, IfThen t' e1 e2 t1')
           (v, t') -> traceIf env (v, t') e1 e2
trace env (IfElse t e1 e2 t2)
    = do tr <- trace' env t
         case tr of
           (VBool False, t') -> do (v1, t2') <- trace' env t2
                                   return (v1, IfElse t' e1 e2 t2')
           (v, t') -> traceIf env (v, t') e1 e2
trace env (CaseL t m x t1)
    = do tr <- trace' env t
         case tr of
           (VInL v, t') -> do (v1, t1') <- trace' (bindEnv env x v) t1
                              return (v1, CaseL t' m x t1')
           v -> traceMatch env v m
trace env (CaseR t m x t2)
    = do tr <- trace' env t
         case tr of
           (VInR v, t') -> do (v2, t2') <- trace' (bindEnv env x v) t2
                              return (v2, CaseR t' m x t2')
           v -> traceMatch env v m
trace env (Call t1 t2 _ _)
    = do (VClosure k' env0, t1') <- trace' env t1
         (v2, t2')               <- trace' env t2
         traceCall (VClosure k' env0, t1') (v2, t2')
trace env (Trace e)
    = do (v, t) <- trace' env e
         return (VTrace v t env, Trace t)
trace env t =
   evalError $ "Cannot trace: " ++ show t ++ " in environment " ++ show env

trace' :: Env Value -> Exp -> SlM (Value, Trace)
trace' env e = do (v, t) <- trace env e
                  v `seq` return (v, t)

traceOp :: Primitive -> [(Value,Trace)] -> SlM (Value, Trace)
traceOp f vts = do let (vs,ts) = unzip vts
                   v <- evalTraceOp f vs
                   return (v, Op f ts)

traceCall :: (Value, Trace) -> (Value, Trace) -> SlM (Value, Exp)
traceCall (v1@(VClosure k env0), t1) (v2, t2)
    = do let envf  = bindEnv env0 (funName k) v1
             envfx = bindEnv envf (funArg k) v2
         (v,t) <- trace' envfx (funBody k)
         return (v, Call t1 t2 k (Rec (funName k) (funArg k) t Nothing))
traceCall _ _ = evalError "traceCall: cannot call non-VClosure values"

traceMatch :: Env Value -> (Value, Trace) -> Match -> SlM (Value, Exp)
traceMatch env (VInL v, t) m
    = do let (x,e) = inL m
             env'  = bindEnv env x v
         (v1,t1) <- trace' env' e
         return (v1, CaseL t m x t1)
traceMatch env (VInR v, t) m
    = do let (x,e) = inR m
             env'  = bindEnv env x v
         (v2,t2) <- trace' env' e
         return (v2, CaseR t m x t2)
traceMatch _ _ _ =
    evalError "traceMatch: scrutinee does not reduce to a constructor"

traceIf :: Env Value -> (Value, Trace) -> Exp -> Exp -> SlM (Value, Exp)
traceIf env (VBool True , t) e1 e2 = do (v1,t1) <- trace' env e1
                                        return (v1, IfThen t e1 e2 t1)
traceIf env (VBool False, t) e1 e2 = do (v2,t2) <- trace' env e2
                                        return (v2, IfElse t e1 e2 t2)
traceIf _ _ _ _ = evalError "traceIf: condition is not a VBool value"
