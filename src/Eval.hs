module Eval where

import Util
import Control.Exception
import Env
import UpperSemiLattice
import Trace
import Annot
import Slice(bslice,pslice)
import TraceGraph
import Profile
import System.IO.Unsafe(unsafePerformIO)
import System.FilePath.Posix
import TraceTree

evalTraceOp :: Op -> [Value] -> Value
evalTraceOp (O "val" _ _) [VTrace v t env] = v
evalTraceOp (O "replay" _ _) [VTrace _ t env]
    =  let (v',t') = trace' env t
       in VTrace v' t' env
evalTraceOp (O "slice" _ _) [VTrace v t env, p]
    | p `leq` v
    = let (t',penv) = bslice p t
          v' = extract p v
          env' = extract penv env
      in v' `seq` t' `seq` env' `seq` VTrace v' t' env'
evalTraceOp (O "pslice" _ _) [VTrace v t e, p]
    | p `leq` v
    = let (t',env') = pslice p t
      in VTrace p t' env'
evalTraceOp (O "where" _ _) [VTrace _ t env] =
    let env' = fmap (make_where ) env
        v' = whr env' t
    in System.IO.Unsafe.unsafePerformIO (putStrLn (show ( pp v')))
           `seq`  erase_to_v v'
evalTraceOp (O "expr" _ _) [VTrace _ t env] =
    let env' = fmap (make_expr ) env
        v' = expr env' t
    in System.IO.Unsafe.unsafePerformIO (putStrLn (show ( pp v')))
           `seq` erase_to_v v'
evalTraceOp (O "dep" _ _) [VTrace _ t env] =
    let env' = fmap (make_dep ) env
        v' = dep env' t
    in System.IO.Unsafe.unsafePerformIO (putStrLn (show ( pp v')))
           `seq` erase_to_v v'
evalTraceOp (O "visualize" _ _) [VString s, VTrace _ t _] =
    (case takeExtension s
     of ".pdf" -> System.IO.Unsafe.unsafePerformIO (visualizePDF s t)
        ".svg" -> System.IO.Unsafe.unsafePerformIO (visualizeSVG s t))
    `seq` VUnit
evalTraceOp (O "visualize2" _ _) [VString s, VTrace _ t1 _, VTrace _ t2 _] =
    (case takeExtension s
     of ".pdf" ->System.IO.Unsafe.unsafePerformIO (visualize2PDF s t1 t2)
        ".svg" -> System.IO.Unsafe.unsafePerformIO (visualize2SVG s t1 t2))
    `seq` VUnit

evalTraceOp (O "treesize" _ _) [VTrace _ t _] =
    VInt (forestsize (to_tree t))

evalTraceOp (O "profile" _ _) [VTrace _ t _] =
    System.IO.Unsafe.unsafePerformIO (putStrLn (show (profile t)))
    `seq` VUnit
evalTraceOp (O "profile2" _ _) [VTrace _ t _] =
    System.IO.Unsafe.unsafePerformIO (putStrLn (show (profile2 t)))
    `seq` VUnit
evalTraceOp op vs = evalOp op vs

eval :: Env Value -> Exp -> Value
eval env Hole                      =  VHole
eval env (Var x)                   =  lookupEnv' env x
eval env (Let x e1 e2)             =  let v = (eval' env e1) in
                                      v `seq` eval' (bindEnv env x v) e2
eval env (Unit)                    =  VUnit
eval env (CBool b)                 =  VBool b
eval env (If e e1 e2)              =  evalIf env (eval' env e) e1 e2
eval env (CInt i)                  =  VInt i
eval env (CString s)               =  VString s
eval env (Op f exps)               =  evalTraceOp f (map (eval' env) exps)
eval env (Pair e1 e2)              =  VPair (eval' env e1) (eval' env e2)
eval env (Fst e)                   =  let (VPair v1 v2) = eval' env e
                                      in v1
eval env (Snd e)                   =  let (VPair v1 v2) = eval' env e
                                      in v2
eval env (InL e)                   =  VInL (eval' env e)
eval env (InR e)                   =  VInR (eval' env e)
eval env (Case e m)                =  evalMatch env (eval' env e) m
eval env (Fun k)                   =  VClosure k env
eval env (App e1 e2)               =  evalCall (eval' env e1) (eval' env e2)
eval env (Roll tv e)               =  VRoll tv (eval' env e)
eval env (Unroll tv e)             =  let (VRoll tv' v) = eval' env e
                                      in assert (tv == tv') v
eval env (Trace e)                 =  let (v,t) = trace env e
                                      in VTrace v t env
eval env (TraceVar e x)            =  let VTrace _ _ env0 = eval' env e
                                      in lookupEnv' env0 x
eval env (TraceUpd e x e')         =  let VTrace v t env0 = eval' env e
                                          v' = eval' env e'
                                      in VTrace v t (updateEnv env0 x v')
eval env (Lab e l)                 =  VLabel (eval' env e) l
eval env (EraseLab e l)            =  erase_lab (eval' env e) l

eval' env e                        =  let v = unlabel (eval env e)
                                      in v `seq` v

evalCall (v1) (v2) =
    let VClosure k env0 = v1
        envf = bindEnv env0 (fn k) v1
        envfx = bindEnv envf (arg k) v2
    in eval envfx (body k)

evalMatch env (VInL v) m         =  let (x,e) = inL m
                                        env' = bindEnv env x v
                                    in eval' env' e
evalMatch env (VInR v) m         =  let (x,e) = inR m
                                        env' = bindEnv env x v
                                    in eval' env' e
evalIf env (VBool b) e1 e2       =  if b
                                    then eval' env e1
                                    else eval' env e2



traceOp :: Op -> [(Value,Trace)] -> (Value, Trace)
traceOp f vts = let (vs,ts) = unzip vts
                in (evalTraceOp f vs, Op f ts)

trace :: Env Value -> Exp -> (Value,Trace)
trace env (Var x)                   =  (lookupEnv' env x,Var x)
trace env (Let x e1 e2)             =  let (v1,t1) = trace' env e1
                                           (v2,t2) = trace' (bindEnv env x v1) e2
                                       in v1 `seq` (v2,Let x t1 t2)
trace env (Unit)                    =  (VUnit, Unit)
trace env (CBool b)                 =  (VBool b, CBool b)
trace env (If e e1 e2)              =  traceIf env (trace' env e) e1 e2
trace env (CInt i)                  =  (VInt i, CInt i)
trace env (CString s)               =  (VString s, CString s)
trace env (Op f exps)               =  let vts = map (trace' env) exps
                                       in traceOp f vts
trace env (Pair e1 e2)              =  let (v1,t1) = trace' env e1
                                           (v2,t2) = trace' env e2
                                       in (VPair v1 v2, Pair t1 t2)
trace env (Fst e)                   =  let (VPair v1 v2,t) = trace' env e
                                       in (v1, Fst t)
trace env (Snd e)                   =  let (VPair v1 v2,t) = trace' env e
                                       in (v2, Snd t)
trace env (InL e)                   =  let (v,t) = trace' env e
                                       in (VInL v, InL t)
trace env (InR e)                   =  let (v,t) = trace' env e
                                       in (VInR v, InR t)
trace env (Case e m)                =  traceMatch env (trace' env e) m
trace env (Fun k)                   =  (VClosure k env, Fun k)
trace env (App e1 e2)               =  traceCall (trace' env e1) (trace' env e2)
trace env (Roll tv e)               =  let (v,t) = trace' env e
                                       in (VRoll tv v, Roll tv t)
trace env (Unroll tv e)             =  let (VRoll tv' v,t) = trace' env e
                                       in assert (tv == tv')
                                          (v, Unroll tv t)
-- replay cases
trace env (IfThen t e1 e2 t1)       =  case trace' env t
                                       of (VBool True, t') ->
                                              let (v1,t1') = trace' env t1
                                              in (v1, IfThen t' e1 e2 t1')
                                          (v,t') -> traceIf env (v,t') e1 e2
trace env (IfElse t e1 e2 t2)       =  case trace' env t
                                       of (VBool False, t') ->
                                              let (v1,t2') = trace' env t2
                                              in (v1, IfElse t' e1 e2 t2')
                                          (v,t') -> traceIf env (v,t') e1 e2
trace env (CaseL t m x t1)          =  case trace' env t
                                       of (VInL v,t') ->
                                              let (v1,t1') = trace' (bindEnv env x v) t1
                                              in (v1,CaseL t' m x t1')
                                          v -> traceMatch env v m
trace env (CaseR t m x t2)          =  case trace' env t
                                       of (VInR v,t') ->
                                              let (v2,t2') = trace' (bindEnv env x v) t2
                                              in (v2,CaseR t' m x t2')
                                          v -> traceMatch env v m
trace env (Call t1 t2 k t)          =    let (v1, t1') = trace' env t1
                                             (v2, t2') = trace' env t2
                                             (VClosure k' env0) = v1
                                         in if False
                                            then let envf = bindEnv env0 (fn t) v1
                                                     envfx = bindEnv envf (arg t) v2
                                                     (v,t') = trace' envfx (body t)
                                                 in (v, Call t1' t2' k' (Rec (fn t) (arg t) t' Nothing))
                                            else traceCall (VClosure k' env0, t1') (v2,t2')
trace env (Trace e)
    =  let (v,t) = trace' env e
       in (VTrace v t env, Trace t)
trace env (TraceVar e x)
    =  let (VTrace _ _ env0,t) = trace' env e
       in (lookupEnv' env0 x, TraceVar t x)
trace env (TraceUpd e x e')
    =  let (VTrace v0 t0 env0,t)  = trace' env e
           (v',t') = trace env e'
       in (VTrace v0 t0 (updateEnv env0 x v'), TraceUpd t x t')
trace env (Lab e l)
    = let (v,t) = trace' env e
      in (VLabel v l, Lab t l)
trace env (EraseLab e l)
    =  let (v,t) = trace' env e
       in (erase_lab v l, EraseLab t l)
trace env t =
   error $ show env ++ show t
trace' env e = let (v,t) = trace env e
               in v `seq` (unlabel v, t)


traceCall (v1,t1) (v2,t2) =
    let VClosure k env0 = v1
        envf = bindEnv env0 (fn k) v1
        envfx = bindEnv envf (arg k) v2
        (v,t) = trace' envfx (body k)
    in (v, Call t1 t2 k (Rec (fn k) (arg k) t Nothing))

traceMatch env (VInL v,t) m         =  let (x,e) = inL m
                                           env' = bindEnv env x v
                                           (v1,t1) = trace' env' e
                                       in (v1, CaseL t m x t1)
traceMatch env (VInR v,t) m         =  let (x,e) = inR m
                                           env' = bindEnv env x v
                                           (v2,t2) = trace' env' e
                                       in (v2, CaseR t m x t2)
traceIf env (VBool b,t) e1 e2       =  if b
                                       then
                                           let (v1,t1) = trace' env e1
                                           in  (v1, IfThen t e1 e2 t1)
                                       else
                                           let (v2,t2) = trace' env e2
                                           in  (v2, IfElse t e1 e2 t2)
