module Eval
    ( -- * Evaluating TML expressions
      eval
    ) where

import           Annot
import           Env
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

evalTraceOp :: Primitive -> [Value] -> Value
evalTraceOp PrimVal [VTrace v _ _] = v
evalTraceOp PrimReplay [VTrace _ t env]
    =  let (v',t') = trace env t
       in VTrace v' t' env
evalTraceOp PrimSlice [VTrace v t env, p]
    | p `leq` v
    = let (t',penv) = bslice p t
          v' = extract p v
          env' = extract penv env
      in v' `seq` t' `seq` env' `seq` VTrace v' t' env'
    | otherwise = error ("slice: criterion "++ show p ++ " is not a prefix of output " ++ show v)
evalTraceOp PrimPSlice [VTrace v t _, p]
    | p `leq` v
    = let (t',env') = pslice p t
      in VTrace p t' env'
    | otherwise = error ("pslice: criterion "++ show p ++ " is not a prefix of output " ++ show v)
evalTraceOp PrimWhere [VTrace _ t env] =
    let env' = fmap (make_where ) env
        v' = whr env' t
    in System.IO.Unsafe.unsafePerformIO (putStrLn (show ( pp v')))
           `seq`  erase_to_v v'
evalTraceOp PrimExpr [VTrace _ t env] =
    let env' = fmap (make_expr ) env
        v' = expr env' t
    in System.IO.Unsafe.unsafePerformIO (putStrLn (show ( pp v')))
           `seq` erase_to_v v'
evalTraceOp PrimDep [VTrace _ t env] =
    let env' = fmap (make_dep ) env
        v' = dep env' t
    in System.IO.Unsafe.unsafePerformIO (putStrLn (show ( pp v')))
           `seq` erase_to_v v'
evalTraceOp PrimVisualize [VString s, VTrace _ t _] =
    (case takeExtension s
     of ".pdf" -> System.IO.Unsafe.unsafePerformIO (visualizePDF s t)
        ".svg" -> System.IO.Unsafe.unsafePerformIO (visualizeSVG s t)
        ext    -> error $ "Unknown file extension : " ++ ext)
    `seq` VUnit
evalTraceOp PrimVisualize2 [VString s, VTrace _ t1 _, VTrace _ t2 _] =
    (case takeExtension s
     of ".pdf" -> System.IO.Unsafe.unsafePerformIO (visualize2PDF s t1 t2)
        ".svg" -> System.IO.Unsafe.unsafePerformIO (visualize2SVG s t1 t2)
        ext    -> error $ "Unknown file extension : " ++ ext)
    `seq` VUnit

evalTraceOp PrimTreeSize [VTrace _ t _] =
    VInt (forestsize (to_tree t))

evalTraceOp PrimProfile [VTrace _ t _] =
    System.IO.Unsafe.unsafePerformIO (putStrLn (show (profile t)))
    `seq` VUnit
evalTraceOp PrimProfile2 [VTrace _ t _] =
    System.IO.Unsafe.unsafePerformIO (putStrLn (show (profile2 t)))
    `seq` VUnit
evalTraceOp op vs = evalOp op vs

eval :: Env Value -> Exp -> Value
eval _   Hole              = VHole
eval env (Var x)           = lookupEnv' env x
eval env (Let x e1 e2)     = let v = (eval env e1) in
                             v `seq` eval (bindEnv env x v) e2
eval _   (Unit)            = VUnit
eval _   (CBool b)         = VBool b
eval env (If e e1 e2)      = evalIf env (eval env e) e1 e2
eval _   (CInt i)          = VInt i
eval _   (CString s)       = VString s
eval env (Op f exps)       = evalTraceOp f (map (eval env) exps)
eval env (Pair e1 e2)      = VPair (eval env e1) (eval env e2)
eval env (Fst e)           = let (VPair v1 _) = eval env e
                             in v1
eval env (Snd e)           = let (VPair _ v2) = eval env e
                             in v2
eval env (InL e)           = VInL (eval env e)
eval env (InR e)           = VInR (eval env e)
eval env (Case e m)        = evalMatch env (eval env e) m
eval env (Fun k)           = VClosure k env
eval env (App e1 e2)       = evalCall (eval env e1) (eval env e2)
eval env (Roll tv e)       = VRoll tv (eval env e)
eval env (Unroll tv e)     = let (VRoll tv' v) = eval env e
                             in assert (tv == tv') v
eval env (Trace e)         = let (v,t) = trace env e
                             in VTrace v t env
eval _   e                 = error $ "Cannot eval: " ++ show e

evalCall :: Value -> Value -> Value
evalCall v1@(VClosure k env0) v2 =
    let envf  = bindEnv env0 (funName k) v1
        envfx = bindEnv envf (funArg k) v2
    in eval envfx (funBody k)
evalCall _ _ = error "evalCall: cannot call non-VClosure values"

evalMatch :: Env Value -> Value -> Match -> Value
evalMatch env (VInL v) m
    = let (x, e) = inL m
          env' = bindEnv env x v
      in eval env' e
evalMatch env (VInR v) m
    =  let (x, e) = inR m
           env'   = bindEnv env x v
       in eval env' e
evalMatch _ _ _ = error "evalMatch: scrutinee does not reduce to a constructor"

evalIf :: Env Value -> Value -> Exp -> Exp -> Value
evalIf env (VBool True ) e1 _ = eval env e1
evalIf env (VBool False) _  e2 = eval env e2
evalIf _ _ _ _ = error "evalIf: condition is not a VBool value"


-- Tracing as described in Section 4.2 of ICFP'12 paper
trace :: Env Value -> Exp -> (Value, Trace)
trace env (Var x)       = (lookupEnv' env x,Var x)
trace env (Let x e1 e2) = let (v1,t1) = trace env e1
                              (v2,t2) = trace (bindEnv env x v1) e2
                          in v1 `seq` (v2,Let x t1 t2)
trace _   (Unit)        = (VUnit, Unit)
trace _   (CBool b)     = (VBool b, CBool b)
trace env (If e e1 e2)  = traceIf env (trace env e) e1 e2
trace _   (CInt i)      = (VInt i, CInt i)
trace _   (CString s)   = (VString s, CString s)
trace env (Op f exps)   = let vts = map (trace env) exps
                          in traceOp f vts
trace env (Pair e1 e2)  = let (v1,t1) = trace env e1
                              (v2,t2) = trace env e2
                          in (VPair v1 v2, Pair t1 t2)
trace env (Fst e)       = let (VPair v1 _, t) = trace env e
                          in (v1, Fst t)
trace env (Snd e)       = let (VPair _ v2, t) = trace env e
                          in (v2, Snd t)
trace env (InL e)       = let (v,t) = trace env e
                          in (VInL v, InL t)
trace env (InR e)       = let (v,t) = trace env e
                          in (VInR v, InR t)
trace env (Case e m)    = traceMatch env (trace env e) m
trace env (Fun k)       = (VClosure k env, Fun k)
trace env (App e1 e2)   = traceCall (trace env e1) (trace env e2)
trace env (Roll tv e)   = let (v,t) = trace env e
                          in (VRoll tv v, Roll tv t)
trace env (Unroll tv e) = let (VRoll tv' v, t) = trace env e
                          in assert (tv == tv') (v, Unroll tv t)
-- replay cases
trace env (IfThen t e1 e2 t1)
    = case trace env t of
        (VBool True, t') -> let (v1, t1') = trace env t1
                            in (v1, IfThen t' e1 e2 t1')
        (v, t') -> traceIf env (v, t') e1 e2
trace env (IfElse t e1 e2 t2)
    = case trace env t of
        (VBool False, t') -> let (v1, t2') = trace env t2
                             in (v1, IfElse t' e1 e2 t2')
        (v, t') -> traceIf env (v, t') e1 e2
trace env (CaseL t m x t1)
    = case trace env t of
        (VInL v, t') -> let (v1, t1') = trace (bindEnv env x v) t1
                        in (v1, CaseL t' m x t1')
        v -> traceMatch env v m
trace env (CaseR t m x t2)
    = case trace env t of
        (VInR v, t') -> let (v2, t2') = trace (bindEnv env x v) t2
                        in (v2, CaseR t' m x t2')
        v -> traceMatch env v m
trace env (Call t1 t2 _ _)
    = let (v1, t1') = trace env t1
          (v2, t2') = trace env t2
          (VClosure k' env0) = v1
      in traceCall (VClosure k' env0, t1') (v2, t2')
trace env (Trace e)
    = let (v, t) = trace env e
      in (VTrace v t env, Trace t)
trace env t =
   error $ "Trace error: " ++ show env ++ show t

traceOp :: Primitive -> [(Value,Trace)] -> (Value, Trace)
traceOp f vts = let (vs,ts) = unzip vts
                in (evalTraceOp f vs, Op f ts)

traceCall :: (Value, Trace) -> (Value, Trace) -> (Value, Exp)
traceCall (v1@(VClosure k env0), t1) (v2, t2)
    = let envf  = bindEnv env0 (funName k) v1
          envfx = bindEnv envf (funArg k) v2
          (v,t) = trace envfx (funBody k)
      in (v, Call t1 t2 k (Rec (funName k) (funArg k) t Nothing))
traceCall _ _ = error "traceCall: cannot call non-VClosure values"

traceMatch :: Env Value -> (Value, Trace) -> Match -> (Value, Exp)
traceMatch env (VInL v, t) m
    = let (x,e)   = inL m
          env'    = bindEnv env x v
          (v1,t1) = trace env' e
      in (v1, CaseL t m x t1)
traceMatch env (VInR v, t) m
    = let (x,e)   = inR m
          env'    = bindEnv env x v
          (v2,t2) = trace env' e
      in (v2, CaseR t m x t2)
traceMatch _ _ _ = error "traceMatch: scrutinee does not reduce to a constructor"

traceIf :: Env Value -> (Value, Trace) -> Exp -> Exp -> (Value, Exp)
traceIf env (VBool True , t) e1 e2 = let (v1,t1) = trace env e1
                                     in  (v1, IfThen t e1 e2 t1)
traceIf env (VBool False, t) e1 e2 = let (v2,t2) = trace env e2
                                     in  (v2, IfElse t e1 e2 t2)
traceIf _ _ _ _ = error "traceIf: condition is not a VBool value"
