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
import           System.FilePath.Posix

run :: EvalState -> Exp -> SlMIO (Outcome, EvalState)
run st e = runEvalM st (evalM e)

eval :: Env Value -> Exp -> SlMIO Outcome
eval env e = evalEvalM env (evalM e)

evalM :: Exp -> EvalM Outcome
evalM (EHole)         = return (ORet VHole)
evalM (EVar x)        = do env <- getEnv
                           return (ORet (lookupEnv' env x))
evalM (ELet x e1 e2)  = do v <- evalM' e1
                           withExn v (withBinder x (getVal v) (evalM' e2))
evalM  EUnit          = return (ORet VUnit)
evalM (EBool b)       = return (ORet $ VBool b)
evalM (EIf e e1 e2)   = do cond <- evalM' e
                           evalIf cond e1 e2
evalM (EInt i)        = return (ORet $ VInt i)
evalM (EString s)     = return (ORet $ VString s)
evalM (EOp f exps)    = do rs <- evalOpArgs exps
                           evalTraceOp f rs
evalM (EPair e1 e2)   = do v1 <- evalM' e1
                           v2 <- withExn (v1) (evalM' e2)
                           return (v2 >-< ORet (VPair (getVal v1) (getVal v2)))
evalM (EFst e)        = do v <- evalM' e
                           let (VPair v1 _) = getVal v
                           return (v >-< ORet v1)
evalM (ESnd e)        = do v <- evalM' e
                           let (VPair _ v2) = getVal v
                           return (v >-< ORet v2)
evalM (EInL e)        = do e' <- evalM' e
                           return (e' >-< (ORet (VInL (getVal e'))))
evalM (EInR e)        = do e' <- evalM' e
                           return (e' >-< (ORet (VInR (getVal e'))))
evalM (ECase e m)     = do -- See Note [No exceptions in scrutinee]
                           e' <- evalM' e
                           evalMatch e' m
evalM (EFun k)        = do env <- getEnv
                           return (ORet (VClosure k env))
evalM (EApp e1 e2)    = do e1' <- evalM' e1
                           e2' <- withExn e1' (evalM' e2)
                           evalCall e1' e2'
evalM (ERoll tv e)    = do v <- evalM' e
                           return (v >-< (ORet (VRoll tv (getVal v) )))
evalM (EUnroll _ e)   = do v <- evalM' e
                           let (VRoll _ v') = getVal v
                           return (v >-< ORet v')
evalM (ETrace e)      = do env    <- getEnv
                           store  <- getStore
                           (r, t) <- trace e
                           return (ORet (VTrace r t env store))
-- References
evalM (ERef e)        = do r <- evalM' e
                           case r of
                             OExn v -> return (OExn v)
                             ORet v -> do v' <- newRef v
                                          return (ORet v')
                             _ -> return OHole
evalM (EDeref e)      = do r <- evalM' e
                           case r of
                             OExn v -> return (OExn v)
                             ORet v -> do v' <- getRef v
                                          return (ORet v')
                             _ -> return OHole
evalM (EAssign e1 e2) = do r1 <- evalM' e1
                           r2 <- withExn r1 (evalM' e2)
                           case (r1,r2) of
                             (OExn v1, _) -> return (OExn v1)
                             (_, OExn v2) -> return (OExn v2)
                             (ORet v1, ORet v2) ->
                                 do updateRef v1 v2
                                    return (ORet VUnit)
                             _ -> return OHole
evalM (ESeq e1 e2)    = do r1 <- evalM' e1
                           withExn r1 (evalM' e2)
-- Exceptions.  See Note [Evaluation of exceptions]
evalM (ERaise e)      = do r <- evalM' e
                           case r of
                             ORet v -> return (OExn v)
                             OExn v -> return (OExn v)
                             _ -> return OHole
evalM (ETryWith e x h)= do r <- evalM' e
                           case r of
                              OExn v -> withBinder x v (evalM' h)
                              _      -> return r
-- This will never happen because the above matches cover all cases.  But the
-- pattern exhaustiveness checker doesn't see that because we're using pattern
-- synonym.  See GHC bug #8779.  Hopefully GHC 8.2 will ship a fix.
evalM (Exp e) = error ("Impossible happened in evalM: " ++ show e)


-- | Evaluates an expression and forces the result before returning it.  Ensures
-- strict semantics.
evalM' :: Exp -> EvalM Outcome
evalM' e = do v <- evalM e
              v `seq` return v

evalCall :: Outcome -> Outcome -> EvalM Outcome
evalCall (OExn v) _                      = return (OExn v)
evalCall _ (OExn v)                      = return (OExn v)
evalCall (ORet (v1@(VClosure k env0))) (ORet v2) =
    do let envf  = bindEnv env0 (funName k) v1
           envfx = bindEnv envf (funArg k) v2
       withEnv envfx (evalM (funBody k))
evalCall _ _ = evalError "evalCall: cannot call non-VClosure values"

evalMatch :: Outcome -> Match -> EvalM Outcome
evalMatch (ORet (VInL v)) m
    = let (x, e) = inL m
      in maybeWithBinder x v (evalM' e)
evalMatch (ORet (VInR v)) m
    = let (x, e) = inR m
      in maybeWithBinder x v (evalM' e)
evalMatch _ _
    = evalError "evalMatch: scrutinee does not reduce to a constructor"

evalIf :: Outcome -> Exp -> Exp -> EvalM Outcome
evalIf (ORet (VBool True)) e1 _   = evalM' e1
evalIf (ORet (VBool False)) _  e2 = evalM' e2
evalIf (OExn v) _ _               = return (OExn v)
evalIf _ _ _ = evalError "evalIf: condition is not a VBool value"


evalOpArgs :: [Exp] -> EvalM [Outcome]
evalOpArgs []  = return []
evalOpArgs (x:xs) = do r <- evalM' x
                       case r of
                         OExn _ -> return (r : map (const OHole) xs)
                         ORet _ -> do xs' <- evalOpArgs xs
                                      return (r : xs')
                         _ -> return (OHole : map (const OHole) xs)

evalTraceOp :: Primitive -> [Outcome] -> EvalM Outcome
evalTraceOp PrimVal [ORet (VTrace r _ _ _)] = return r
evalTraceOp PrimTraceSlice [ORet (VTrace r t env st), p]
    | p `leq` r
    = do let (t',penv) = traceSlice st p t
             r'        = extract p r
             env'      = extract penv env
             -- JSTOLAREK: update store argument
         r' `seq` t' `seq` env' `seq` return (ORet (VTrace r' t' env' st))
    | otherwise = evalError ("slice: criterion " ++ show p ++
                             " is not a prefix of output " ++ show r)
evalTraceOp PrimBwdSlice [ORet (VTrace r t _ st), p]
    | p `leq` r
    = do let (env', _, e', _) = bwdSlice st p t
         -- JSTOLAREK: store store in a VExp
         return (ORet (VExp e' env'))
    | otherwise = evalError ("bwdSlice: criterion "++ show p ++
                             " is not a prefix of output " ++ show r)
evalTraceOp PrimVisualize [ORet (VString s), ORet v]
    = case takeExtension s of
        ".pdf" -> lift (visualizePDF s v) >> return (ORet VUnit)
        ".svg" -> lift (visualizeSVG s v) >> return (ORet VUnit)
        ext    -> evalError $ "visualizeDiff: unknown file extension : " ++ ext
evalTraceOp PrimVisualizeDiff [ORet (VString s), ORet (v1), ORet (v2)]
    = case takeExtension s of
        ".pdf" -> lift (visualizeDiffPDF s v1 v2) >> return (ORet VUnit)
        ".svg" -> lift (visualizeDiffSVG s v1 v2) >> return (ORet VUnit)
        ext    -> evalError $ "visualizeDiff: unknown file extension : " ++ ext
evalTraceOp PrimTreeSize [ORet (VTrace _ t _ _)] =
    return (ORet (VInt (forestsize (toTree t))))
evalTraceOp PrimProfile [ORet (VTrace _ t _ _)]
    = do liftIO $ putStrLn (show (profile t))
         return (ORet VUnit)
evalTraceOp PrimProfileDiff [ORet (VTrace _ t _ _)]
    = do liftIO $ putStrLn (show (profileDiff t))
         return (ORet VUnit)
evalTraceOp op vs = evalOpExn op vs

evalOpExn :: Primitive -> [Outcome] -> EvalM Outcome
evalOpExn f rs =
  case extractExn rs of
    Left vs   -> evalOp f vs
    Right exn -> return exn
  where extractExn :: [Outcome] -> Either [Value] Outcome
        extractExn [] = Left []
        extractExn (ORet v : rs') = case extractExn rs' of
                                        Left vs -> Left (v:vs)
                                        Right exn -> Right exn
        extractExn (OExn v : _) = Right (OExn v)
        extractExn _ = Right (OHole)

evalOp :: Primitive -> [Value] -> EvalM Outcome
evalOp OpDiv [_    , VInt    0]
    = return (OExn (VString "Division by zero"))
evalOp f [VInt    i, VInt    j] | isCommonOp  f
    = return (ORet ((commonOps ! f) (i,j)))
evalOp f [VBool   i, VBool   j] | isCommonOp  f
    = return (ORet ((commonOps ! f) (i,j)))
evalOp f [VString i, VString j] | isCommonOp  f
    = return (ORet ((commonOps ! f) (i,j)))
evalOp f [VInt    i, VInt    j] | isIntBinOp  f
    = return (ORet ((intBinOps ! f) (i,j)))
evalOp f [VInt    i, VInt    j] | isIntRelOp  f
    = return (ORet ((intRelOps ! f) (i,j)))
evalOp f [VBool   i, VBool   j] | isBoolRelOp f
    = return (ORet ((boolRelOps! f) (i,j)))
evalOp f [VBool   b]            | isBoolUnOp  f
    = return (ORet ((boolUnOps ! f) b))
evalOp _ vs | VHole `elem` vs = return (ORet VHole)
evalOp _ vs | VStar `elem` vs = return (ORet VStar)
evalOp f vs = evalError ("Op " ++ show f ++ " not defined for " ++ show vs)

-- Note [No exceptions in scrutinee]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- We know scrutinee does not raise exceptions because limitations in our type
-- checking algorithm don't allow that

-- Tracing as described in Section 4.2 of ICFP'12 paper
trace :: Exp -> EvalM (Outcome, Trace)
trace EHole          = return (ORet VHole, THole)
trace (EVar x)       = do env <- getEnv
                          return (ORet $ lookupEnv' env x, TVar x)
trace (ELet x e1 e2) = do (v1, t1) <- trace' e1
                          (v2, t2) <- withExnTrace v1
                                      (withBinder x (getVal v1) (trace' e2))
                          return (v2, TLet x t1 t2)
trace  EUnit         = return (ORet $ VUnit, TUnit)
trace (EBool b)      = return (ORet $ VBool b, TBool b)
trace (EIf e e1 e2)  = do e' <- trace' e
                          traceIf e' e1 e2
trace (EInt i)       = return (ORet $ VInt i, TInt i)
trace (EString s)    = return (ORet $ VString s, TString s)
trace (EOp op exps)  = do vts <- traceOpArgs exps
                          let (vs,ts) = unzip vts
                          v <- evalTraceOp op vs
                          let f = case v of OExn _ -> True; _ -> False
                          return (v, TOp f op ts)
trace (EPair e1 e2)  = do (v1, t1) <- trace' e1
                          (v2, t2) <- withExnTrace v1 (trace' e2)
                          return (v2 >-< ORet ( VPair (getVal v1) (getVal v2)),
                                  TPair t1 t2)
trace (EFst e)       = do (v, t) <- trace' e
                          let (VPair v1 _) = getVal v
                          return (v >-< ORet v1, TFst t)
trace (ESnd e)       = do (v, t) <- trace' e
                          let (VPair _ v2) = getVal v
                          return (v >-< ORet v2, TSnd t)
trace (EInL e)       = do (v, t) <- trace' e
                          return (v >-< (ORet (VInL (getVal v))),
                                 TInL t)
trace (EInR e)       = do (v, t) <- trace' e
                          return (v >-< (ORet (VInR (getVal v))),
                                 TInR t)
trace (ECase e m)    = do -- See Note [No exceptions in scrutinee]
                          e' <- trace' e
                          traceMatch e' m
trace (EFun k)       = do env <- getEnv
                          return (ORet $ VClosure k env, TFun k)
trace (EApp e1 e2)   = do e1' <- trace' e1
                          e2' <- withExnTrace (fst e1') (trace' e2)
                          traceCall e1' e2'
trace (ERoll tv e)   = do (v, t) <- trace' e
                          return (v >-< (ORet (VRoll tv (getVal v))),
                                 TRoll tv t)
trace (EUnroll _ e)  = do (v, t) <- trace' e
                          let (VRoll tv' v') = getVal v
                          return (v >-< ORet v', TUnroll tv' t)
trace (ETrace _)     = evalError "Cannot trace a trace"
-- references
trace (ERef e)       = do (r, t) <- trace' e
                          case r of
                             OExn v -> return (OExn v, TRef Nothing t)
                             ORet v -> do v'@(VStoreLoc l) <- newRef v
                                          return (ORet v', TRef (Just l) t)
                             _ -> return (OHole,THole)
trace (EDeref e)     = do (r, t) <- trace' e
                          case r of
                             OExn v -> return (OExn v, TDeref Nothing t)
                             ORet v@(VStoreLoc l) ->
                                          do v' <- getRef v
                                             return (ORet v', TDeref (Just l) t  )
                             _ -> return (OHole,THole)
trace (EAssign e1 e2)= do (r1, t1) <- trace' e1
                          (r2, t2) <- withExnTrace r1 (trace' e2)
                          case (r1,r2) of
                             (OExn v,_) -> return (OExn v, TAssign Nothing THole THole)
                             (_, OExn v) -> return (OExn v, TAssign Nothing t1 THole)
                             (ORet v1@(VStoreLoc l), ORet v2) ->
                                  do updateRef v1 v2
                                     return (ORet VUnit, TAssign (Just l) t1 t2)
                             _ -> return (OHole, THole)
trace (ESeq e1 e2)   = do (r1, t1) <- trace' e1
                          (r2, t2) <- withExnTrace r1 (trace' e2)
                          return (r1 >-< r2, TSeq t1 t2)
-- exceptions
trace (ERaise e)     = do (r, t) <- trace' e
                          case r of
                            OExn v -> return (OExn v, TRaise t)
                            ORet v -> return (OExn v, TRaise t)
                            _ -> return (OHole, THole)
trace (ETryWith e x h) = do (r, t) <- trace' e
                            case r of
                              OExn v -> do
                                     (v'', ht) <- withBinder x v (trace' h)
                                     return (v'', TTryWith t x ht)
                              _ -> return (r, TTry t)

trace (Exp e) = error ("Impossible happened in trace: " ++ show e)

trace' :: Exp -> EvalM (Outcome, Trace)
trace' e = do (v, t) <- trace e
              v `seq` return (v, t)


traceOpArgs :: [Exp] -> EvalM [(Outcome, Trace)]
traceOpArgs []  = return []
traceOpArgs (x:xs) =
    do (r, t) <- trace' x
       case r of
         OExn _ -> return ((r, t) : map (const (OHole, THole)) xs)
         ORet _ -> do xs' <- traceOpArgs xs
                      return ((r, t) : xs')
         _ -> return ((OHole, THole) : map (const (OHole, THole)) xs)

traceCall :: (Outcome, Trace) -> (Outcome, Trace) -> EvalM (Outcome, Trace)
traceCall (OExn v, t) _
    = return (OExn v, TCallExn t THole)
traceCall (_, t1) (OExn v, t2)
    = return (OExn v, TCallExn t1 t2)
traceCall (ORet (v1@(VClosure k env0)), t1) (ORet v2, t2)
    = do let envf  = bindEnv env0 (funName k) v1
             envfx = bindEnv envf (funArg  k) v2
         (v,t) <- withEnv envfx (trace' (funBody k))
         return (v, TCall t1 t2 (funLabel k)
                         (Rec (funName k) (funArg k) t Nothing))
traceCall _ _ = evalError "traceCall: cannot call non-VClosure values"

traceMatch :: (Outcome, Trace) -> Match -> EvalM (Outcome, Trace)
traceMatch (ORet (VInL v), t) m
    = do let (x, e) = inL m
         (v1,t1) <- maybeWithBinder x v (trace' e)
         return (v1, TCaseL t x t1)
traceMatch (ORet (VInR v), t) m
    = do let (x, e) = inR m
         (v2,t2) <- maybeWithBinder x v (trace' e)
         return (v2, TCaseR t x t2)
traceMatch _ _ =
    evalError "traceMatch: scrutinee does not reduce to a constructor"

traceIf :: (Outcome, Trace) -> Exp -> Exp -> EvalM (Outcome, Trace)
traceIf (ORet (VBool True) , t) e1 _ = do (v1, t1) <- trace' e1
                                          return (v1, TIfThen t t1)
traceIf (ORet (VBool False), t) _ e2 = do (v2, t2) <- trace' e2
                                          return (v2, TIfElse t t2)
traceIf (OExn v,t) _ _ = return (OExn v, TIfExn t)
traceIf _ _ _ = evalError "traceIf: condition is not a VBool value"

withExn :: Outcome -> EvalM Outcome -> EvalM Outcome
withExn (OExn v) _  = return (OExn v)
withExn _ thing     = thing

withExnTrace :: Outcome -> EvalM (Outcome, Trace) -> EvalM (Outcome, Trace)
withExnTrace (OExn v) _     = return (OExn v, THole)
withExnTrace _ thing        = thing

(>-<) :: Outcome -> Outcome -> Outcome
(>-<) (OExn v1) _  = (OExn v1)
(>-<) _  v2        = v2
