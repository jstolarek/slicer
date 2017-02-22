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

import           Control.Monad.Except
import           Data.Map  ( (!)  )
import           Data.List ( find )
import           System.FilePath.Posix

run :: EvalState -> Exp -> SlMIO (Value, EvalState)
run st e = runEvalM st (evalM e)

eval :: Env Value -> Exp -> SlMIO Value
eval env e = evalEvalM env (evalM e)

evalM :: Exp -> EvalM Value
evalM EHole           = return VHole
evalM (EVar x)        = do env <- getEnv
                           return (lookupEnv' env x)
evalM (ELet x e1 e2)  = do v <- evalM' e1
                           withExn v (withBinder x v (evalM' e2))
evalM  EUnit          = return VUnit
evalM (EBool b)       = return (VBool b)
evalM (EIf e e1 e2)   = do cond <- evalM' e
                           evalIf cond e1 e2
evalM (EInt i)        = return (VInt i)
evalM (EString s)     = return (VString s)
evalM (EOp f exps)    = do vs <- evalOpArgs exps
                           if acceptsExns f
                           then evalTraceOp f vs
                           else case find isException vs of
                                  Nothing  -> evalTraceOp f vs
                                  Just exn -> return exn
evalM (EPair e1 e2)   = do v1 <- evalM' e1
                           v2 <- withExn v1 (evalM' e2)
                           return (v2 >-< VPair v1 v2)
evalM (EFst e)        = do v <- evalM' e
                           let (VPair v1 _) = v
                           return (v >-< v1)
evalM (ESnd e)        = do v <- evalM' e
                           let (VPair _ v2) = v
                           return (v >-< v2)
evalM (EInL e)        = do e' <- evalM' e
                           return (e' >-< VInL e')
evalM (EInR e)        = do e' <- evalM' e
                           return (e' >-< VInR e')
evalM (ECase e m)     = do -- See Note [No exceptions in scrutinee]
                           e' <- evalM' e
                           evalMatch e' m
evalM (EFun k)        = do env <- getEnv
                           return (VClosure k env)
evalM (EApp e1 e2)    = do e1' <- evalM' e1
                           e2' <- withExn e1' (evalM' e2)
                           evalCall e1' e2'
evalM (ERoll tv e)    = do v <- evalM' e
                           return (v >-< VRoll tv v)
evalM (EUnroll _ e)   = do v <- evalM' e
                           let (VRoll _ v') = v
                           return (v >-< v')
evalM (ETrace e)      = do env    <- getEnv
                           store  <- getStore
                           (v, t) <- trace e
                           return (VTrace v t env store)
-- References
evalM (ERef e)        = do v <- evalM' e
                           if isException v
                           then return v
                           else newRef v
evalM (EDeref e)      = do v <- evalM' e
                           if isException v
                           then return v
                           else getRef v
evalM (EAssign e1 e2) = do v1 <- evalM' e1
                           v2 <- withExn v1 (evalM' e2)
                           unless (isException v2) (updateRef v1 v2)
                           return (v1 >-< VUnit)
evalM (ESeq e1 e2)    = do v1 <- evalM' e1
                           withExn v1 (evalM' e2)
-- Exceptions.  See Note [Evaluation of exceptions]
evalM (ERaise e)      = do v <- evalM' e
                           return (VException v)
evalM (ETryWith e x h)= do v <- evalM' e
                           case v of
                              VException v'->
                                  withBinder x (unnestException v') (evalM' h)
                              _            -> return v
-- This will never happen because the above matches cover all cases.  But the
-- pattern exhaustiveness checker doesn't see that because we're using pattern
-- synonym.  See GHC bug #8779.  Hopefully GHC 8.2 will ship a fix.
evalM (Exp e) = error ("Impossible happened in evalM: " ++ show e)

-- | Evaluates an expression and forces the result before returning it.  Ensures
-- strict semantics.
evalM' :: Exp -> EvalM Value
evalM' e = do v <- evalM e
              v `seq` return v

evalCall :: Value -> Value -> EvalM Value
evalCall v VHole          | isException v = return v
evalCall (VClosure _ _) v | isException v = return v
evalCall v1@(VClosure k env0) v2 =
    do let envf  = bindEnv env0 (funName k) v1
           envfx = bindEnv envf (funArg k) v2
       withEnv envfx (evalM (funBody k))
evalCall _ _ = evalError "evalCall: cannot call non-VClosure values"

evalMatch :: Value -> Match -> EvalM Value
evalMatch (VInL v) m
    = let (x, e) = inL m
      in maybeWithBinder x v (evalM' e)
evalMatch (VInR v) m
    = let (x, e) = inR m
      in maybeWithBinder x v (evalM' e)
evalMatch _ _
    = evalError "evalMatch: scrutinee does not reduce to a constructor"

evalIf :: Value -> Exp -> Exp -> EvalM Value
evalIf (VBool True ) e1 _  = evalM' e1
evalIf (VBool False) _  e2 = evalM' e2
evalIf (VException v) _ _  = return (VException v)
evalIf _ _ _ = evalError "evalIf: condition is not a VBool value"

evalOpArgs :: [Exp] -> EvalM [Value]
evalOpArgs []  = return []
evalOpArgs (x:xs) = do t <- evalM' x
                       if isException t
                       then return (t : map (const VHole) xs)
                       else do xs' <- evalOpArgs xs
                               return (t : xs')

evalTraceOp :: Primitive -> [Value] -> EvalM Value
evalTraceOp PrimVal [VTrace v _ _ _] = return v
evalTraceOp PrimTraceSlice [VTrace v t env st, p]
    | p `leq` v
    = do let (t',penv) = traceSlice st p t
             v'        = extract p v
             env'      = extract penv env
             -- JSTOLAREK: update store argument
         v' `seq` t' `seq` env' `seq` return (VTrace v' t' env' st)
    | otherwise = evalError ("slice: criterion " ++ show p ++
                             " is not a prefix of output " ++ show v)
evalTraceOp PrimBwdSlice [VTrace v t _ st, p]
    | p `leq` v
    = do let (env', _, e', _) = bwdSlice st p t
         -- JSTOLAREK: store store in a VExp
         return (VExp e' env')
    | otherwise = evalError ("bwdSlice: criterion "++ show p ++
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
evalTraceOp PrimTreeSize [VTrace _ t _ _] =
    return (VInt (forestsize (toTree t)))
evalTraceOp PrimProfile [VTrace _ t _ _]
    = do liftIO $ putStrLn (show (profile t))
         return VUnit
evalTraceOp PrimProfileDiff [VTrace _ t _ _]
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

-- Note [No exceptions in scrutinee]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- We know scrutinee does not raise exceptions because limitations in our type
-- checking algorithm don't allow that

-- Tracing as described in Section 4.2 of ICFP'12 paper
trace :: Exp -> EvalM (Value, Trace)
trace EHole          = return (VHole, THole)
trace (EVar x)       = do env <- getEnv
                          return (lookupEnv' env x, TVar x)
trace (ELet x e1 e2) = do (v1, t1) <- trace' e1
                          (v2, t2) <- withExnTrace v1
                                      (withBinder x v1 (trace' e2))
                          return (v2, TLet x t1 t2)
trace  EUnit         = return (VUnit, TUnit)
trace (EBool b)      = return (VBool b, TBool b)
trace (EIf e e1 e2)  = do e' <- trace' e
                          traceIf e' e1 e2
trace (EInt i)       = return (VInt i, TInt i)
trace (EString s)    = return (VString s, TString s)
trace (EOp f exps)   = do vts <- traceOpArgs exps
                          let (vs,ts) = unzip vts
                          v <- case find isException vs of
                                 Nothing  -> evalTraceOp f vs
                                 Just exn -> return exn
                          return (v, TOp f ts)
trace (EPair e1 e2)  = do (v1, t1) <- trace' e1
                          (v2, t2) <- withExnTrace v1 (trace' e2)
                          return (v2 >-< VPair v1 v2, TPair t1 t2)
trace (EFst e)       = do (v, t) <- trace' e
                          let (VPair v1 _) = v
                          return (v >-< v1, TFst t)
trace (ESnd e)       = do (v, t) <- trace' e
                          let (VPair _ v2) = v
                          return (v >-< v2, TSnd t)
trace (EInL e)       = do (v, t) <- trace' e
                          return (v >-< VInL v, TInL t)
trace (EInR e)       = do (v, t) <- trace' e
                          return (v >-< VInR v, TInR t)
trace (ECase e m)    = do -- See Note [No exceptions in scrutinee]
                          e' <- trace' e
                          traceMatch e' m
trace (EFun k)       = do env <- getEnv
                          return (VClosure k env, TFun k)
trace (EApp e1 e2)   = do e1' <- trace' e1
                          e2' <- withExnTrace (fst e1') (trace' e2)
                          traceCall e1' e2'
trace (ERoll tv e)   = do (v, t) <- trace' e
                          return (v >-< VRoll tv v, TRoll tv t)
trace (EUnroll _ e)  = do (v, t) <- trace' e
                          let (VRoll tv' v') = v
                          return (v >-< v', TUnroll tv' t)
trace (ETrace _)     = evalError "Cannot trace a trace"
-- references
trace (ERef e)       = do (v, t) <- trace' e
                          if isException v
                          then return (v, TRef Nothing t)
                          else do r@(VStoreLoc l) <- newRef v
                                  return (r, TRef (Just l) t)
trace (EDeref e)     = do (v, t) <- trace' e
                          if isException v
                          then return (v, TDeref Nothing t)
                          else do let r@(VStoreLoc l) = v
                                  v' <- getRef r
                                  return (v', TDeref (Just l) t)
trace (EAssign e1 e2)= do (v1, t1) <- trace' e1
                          (v2, t2) <- withExnTrace v1 (trace' e2)
                          -- withExnTrace ensures that:
                          --   v1 = VException => v2 = Exception
                          unless (isException v2) (updateRef v1 v2)
                          if isException v1
                          then return (v2, TAssign Nothing t1 t2)
                          else do let (VStoreLoc l) = v1
                                  return (VUnit, TAssign (Just l) t1 t2)
trace (ESeq e1 e2)   = do (v1, t1) <- trace' e1
                          (v2, t2) <- withExnTrace v1 (trace' e2)
                          return (v1 >-< v2, TSeq t1 t2)
-- exceptions
trace (ERaise e)     = do (v, t) <- trace' e
                          return (VException v, TRaise t)
trace (ETryWith e x h) = do (v, t) <- trace' e
                            case v of
                              VException v'->
                                  do let uv = unnestException v'
                                     (v'', ht) <- withBinder x uv (trace' h)
                                     return (v'', TTryWith t x ht)
                              _ -> return (v, TTry t)
trace (Exp e) = error ("Impossible happened in trace: " ++ show e)

trace' :: Exp -> EvalM (Value, Trace)
trace' e = do (v, t) <- trace e
              v `seq` return (v, t)

traceOpArgs :: [Exp] -> EvalM [(Value, Trace)]
traceOpArgs []  = return []
traceOpArgs (x:xs) = do t <- trace' x
                        if isException (fst t)
                        then return (t : map (const (VHole, THole)) xs)
                        else do xs' <- traceOpArgs xs
                                return (t : xs')

traceCall :: (Value, Trace) -> (Value, Trace) -> EvalM (Value, Trace)
traceCall (v, t) (VHole, THole) | isException v
    = return (v, TCallExn t THole)
traceCall (VClosure _ _, t1) (v, t2) | isException v
    = return (v, TCallExn t1 t2)
traceCall (v1@(VClosure k env0), t1) (v2, t2)
    = do let envf  = bindEnv env0 (funName k) v1
             envfx = bindEnv envf (funArg  k) v2
         (v,t) <- withEnv envfx (trace' (funBody k))
         return (v, TCall t1 t2 (funLabel k)
                         (Rec (funName k) (funArg k) t Nothing))
traceCall _ _ = evalError "traceCall: cannot call non-VClosure values"

traceMatch :: (Value, Trace) -> Match -> EvalM (Value, Trace)
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

traceIf :: (Value, Trace) -> Exp -> Exp -> EvalM (Value, Trace)
traceIf (VBool True , t) e1 _ = do (v1, t1) <- trace' e1
                                   return (v1, TIfThen t t1)
traceIf (VBool False, t) _ e2 = do (v2, t2) <- trace' e2
                                   return (v2, TIfElse t t2)
traceIf (VException v, t) _ _ = return (VException v, TIfExn t)
traceIf _ _ _ = evalError "traceIf: condition is not a VBool value"

withExn :: Value -> EvalM Value -> EvalM Value
withExn v _     | isException v = return v
withExn _ thing                 = thing

withExnTrace :: Value -> EvalM (Value, Trace) -> EvalM (Value, Trace)
withExnTrace v _     | isException v = return (v, THole)
withExnTrace _ thing                 = thing

(>-<) :: Value -> Value -> Value
(>-<) v1 _  | isException v1 = v1
(>-<) _  v2                  = v2
