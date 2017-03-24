{-# LANGUAGE FunctionalDependencies  #-}
{-# LANGUAGE NamedFieldPuns          #-}
{-# LANGUAGE MultiParamTypeClasses   #-}
{-# LANGUAGE MultiWayIf              #-}
{-# LANGUAGE UndecidableInstances    #-}

-- Suppress "pattern match checker maximum iterations exceeded" warning.
{-# OPTIONS_GHC -Wno-incomplete-patterns -Wno-overlapping-patterns #-}
-- | Implementations of slicing
module Language.Slicer.Slice
    ( traceSlice, fwdSlice, bwdSlice
    ) where

import           Language.Slicer.Core hiding ( allStoreHoles, existsInStore )
import           Language.Slicer.Env
import           Language.Slicer.Monad.Slice
import           Language.Slicer.UpperSemiLattice

import           Data.Foldable


--------------------------------------------------------------------------------
--                          FORWARD SLICING                                   --
--------------------------------------------------------------------------------


fwdSlice :: Env Value -> Store -> Exp -> Trace -> Value
fwdSlice env store expr trace = error "forward slicing not yet implemented"


--------------------------------------------------------------------------------
--                          TRACE SLICING                                     --
--------------------------------------------------------------------------------


traceSlice :: Outcome -> Trace -> (Trace, Env Value)
traceSlice outcome trace =
    let (env, _, _, trace') = bwdSlice outcome trace
    in (trace', env)


--------------------------------------------------------------------------------
--                         BACKWARD SLICING                                   --
--------------------------------------------------------------------------------


-- Note [Handling slicing environment inside a monad]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- Reference store and variable environment are implicitly handled inside SliceM
-- state monad.  Reference store is a normal state that is threaded through the
-- computations and requires no special treatment.  Properly handling the
-- environments is tricky though.  Every monadic backwards slicing computation
-- has to be run inside an empty environment.  At the same time, environment
-- produced during backwards slicing needs to be accumulated using `lub` with
-- already existing environment.  Also, current environment has to be accessible
-- for modification.  This is achieved by:
--
--   1. Using `withEmptyEnv` to run monadic computation inside empty environment
--      and lub the resulting environment with already existing environment.
--
--   2. Using `bwdSlicM` as a wrapper that runs the worker `bwdSliceGo` inside
--      an empty environment.  Without it we would have to explicitly insert
--      `withEmptyEnv` at every call to slicing worker.
--
--   3. Several helper functions are available to access and modify current
--      environment (eg. lookupAndUnbind).
--
-- See #36

bwdSlice :: Outcome -> Trace -> (Env Value, Store, Exp, Trace)
bwdSlice outcome trace =
    let annotatedTrace = annotTrace trace
    in runSliceM emptyStore (bwdSliceGo outcome trace annotatedTrace)

-- | Backwards slicing wrapper that ensures every slicing is started in an empty
-- environment.  See Note [Handling slicing environment inside a monad]
bwdSliceM :: Outcome -> Trace -> AnnotTrace -> SliceM (Exp, Trace)
bwdSliceM outcome trace traceAnnot =
    withEmptyEnv (bwdSliceGo outcome trace traceAnnot)


-- | Backwards slicing worker
bwdSliceGo :: Outcome -> Trace -> AnnotTrace -> SliceM (Exp, Trace)
bwdSliceGo outcome trace traceAnnot = do
  let storeWrites = getStoreWrites traceAnnot
  allStoreHoles <- allStoreHolesM storeWrites
  case (outcome, trace, traceAnnot) of
    (OHole, THole, _) ->
        return (bot, bot)
    (OExn VHole, _, _) | allStoreHoles ->
        return (EHole, TSlicedHole storeWrites RetRaise)
    (ORet VHole, _, _) | allStoreHoles ->
        return (EHole, TSlicedHole storeWrites RetValue)
    (OExn v, TRaise t, AnnotTrace _ [at]) | isExn t->
        do (e, t') <- bwdSliceM (OExn v) t at
           return (ERaise e, TRaise t')
    (OExn v, TRaise t, AnnotTrace _ [at]) ->
        do (e, t') <- bwdSliceM (ORet v) t at
           return (ERaise e, TRaise t')
    (ORet v, TVar x, _) ->
        do setSingletonEnv x v
           return (EVar x, TVar x)
    (ORet VUnit, TUnit, _) ->
        return (EUnit, TUnit)
    (ORet VStar, TUnit, _) ->
        return (EUnit, TUnit)
    (ORet (VBool b), TBool b', _) | b == b' ->
        return (EBool b, TBool b)
    (ORet VStar, TBool b, _) ->
        return (EBool b, TBool b)
    (ORet (VInt i), TInt i', _) | i == i' ->
        return (EInt i, TInt i)
    (ORet VStar, TInt i, _) ->
        return (EInt i, TInt i)
    (ORet (VDouble i), TDouble i', _) | i == i' ->
        return (EDouble i, TDouble i)
    (ORet VStar, TDouble i, _) ->
        return (EDouble i, TDouble i)
    (ORet (VString s), TString s', _) | s == s' ->
        return (EString s, TString s)
    (ORet VStar, TString s, _) ->
        return (EString s, TString s)
    (ORet (VClosure k env), TFun k', _) | k `leq` k' ->
        do setEnv env
           return (EFun k, TFun k')
    (ORet VStar, TFun k, _) ->
        do setEnv (constEnv (fvs k) VStar)
           return (EFun k, TFun k)
    (ORet (VPair p1 p2), TPair t1 t2, AnnotTrace _ [at1, at2]) ->
        do (e2, t2') <- bwdSliceM (ORet p2) t2 at2
           (e1, t1') <- bwdSliceM (ORet p1) t1 at1
           return (EPair e1 e2, TPair t1' t2')
    (ORet VStar, TPair t1 t2, AnnotTrace _ [at1, at2]) ->
        do (e2, t2') <- bwdSliceM (ORet VStar) t2 at2
           (e1, t1') <- bwdSliceM (ORet VStar) t1 at1
           return (EPair e1 e2, TPair t1' t2')
    (OExn v, TPair t1 THole, AnnotTrace _ [at, _]) ->
        do (e1, t1') <- bwdSliceM (OExn v) t1 at
           return (EPair e1 EHole, TPair t1' THole)
    (OExn v, TPair t1 t2, AnnotTrace _ [at1, at2]) ->
        do (e2, t2') <- bwdSliceM (OExn v    ) t2 at2
           (e1, t1') <- bwdSliceM (ORet VHole) t1 at1
           return (EPair e1 e2, TPair t1' t2')
    (ORet p, TFst t, AnnotTrace _ [at]) ->
        do (e', t') <- bwdSliceM (ORet (VPair p bot)) t at
           return (EFst e', TFst t')
    (OExn v, TFst t, AnnotTrace _ [at]) ->
        do (e', t') <- bwdSliceM (OExn v) t at
           return (EFst e', TFst t')
    (ORet p, TSnd t, AnnotTrace _ [at]) ->
        do (e', t') <- bwdSliceM (ORet (VPair bot p)) t at
           return (ESnd e', TSnd t')
    (OExn v, TSnd t, AnnotTrace _ [at]) ->
        do (e', t') <- bwdSliceM (OExn v) t at
           return (ESnd e', TSnd t')
    (ORet (VInL p), TInL t, AnnotTrace _ [at]) ->
        do (e', t') <- bwdSliceM (ORet p) t at
           return (EInL e', TInL t')
    (ORet VStar, TInL t, AnnotTrace _ [at]) ->
        do (e', t') <- bwdSliceM (ORet VStar) t at
           return (EInL e', TInL t')
    (OExn v, TInL t, AnnotTrace _ [at]) ->
        do (e', t') <- bwdSliceM (OExn v) t at
           return (EInL e', TInL t')
    (ORet (VInR p), TInR t, AnnotTrace _ [at]) ->
        do (e', t') <- bwdSliceM (ORet p) t at
           return (EInR e', TInR t')
    (ORet VStar, TInR t, AnnotTrace _ [at]) ->
        do (e', t') <- bwdSliceM (ORet VStar) t at
           return (EInR e', TInR t')
    (OExn v, TInR t, AnnotTrace _ [at])  ->
        do (e', t') <- bwdSliceM (OExn v) t at
           return (EInR e', TInR t')
    (OExn r, TLet x t THole, AnnotTrace _ [at, _]) ->
        do (e1, t1') <- bwdSliceM (OExn r) t at
           return (ELet x e1 EHole, TLet x t1' THole)
    (r, TLet x t1 t2, AnnotTrace _ [at1, at2]) ->
        do (e2, t2') <- bwdSliceM r t2 at2
           p1 <- lookupAndUnbind x
           (e1, t1') <- bwdSliceM (ORet p1) t1 at1
           return (ELet x e1 e2, TLet x t1' t2')
    (r, TOp f op ts, AnnotTrace _ ats) -> -- See issue #47
        do let scs = if (not (any isExn ts))
                     then map (const (ORet VStar)) ts
                     else snd (foldr expectedOutcome (False, []) ts)
               expectedOutcome :: Trace -> (Bool,[Outcome]) -> (Bool, [Outcome])
               expectedOutcome t (False, ts') | isExn t = (True , r : ts')
               expectedOutcome _ (False, ts') = (False, OHole       : ts')
               expectedOutcome _ (True , ts') = (True , ORet VHole  : ts')
               bwdSliceArgM (t', sc, at) (es', ts')
                     = do (e, t) <- bwdSliceM sc t' at
                          return (e:es', t:ts')
           (esA, tsA) <- foldrM bwdSliceArgM ([], []) (zip3 ts scs ats)
           return (EOp op esA, TOp f op tsA)
    (p1, TIfThen t t1, AnnotTrace _ [at, at1]) ->
        do (e1, t1') <- bwdSliceM p1 t1 at1
           (e , t' ) <- bwdSliceM (ORet VStar) t at
           return (EIf e e1 EHole, TIfThen t' t1')
    (p2, TIfElse t t2, AnnotTrace _ [at, at2]) ->
        do (e2, t2') <- bwdSliceM p2 t2 at2
           (e , t' ) <- bwdSliceM (ORet VStar) t at
           return (EIf e EHole e2, TIfElse t' t2')
    (OExn p, TIfExn t, AnnotTrace _ [at]) ->
        do (e, t') <- bwdSliceM (OExn p) t at
           return (EIf e EHole EHole, TIfExn t')
    (p1, TCaseL t x t1, AnnotTrace _ [at, at1]) ->
        do (e1, t1') <- bwdSliceM p1 t1 at1
           p <- maybeLookupAndUnbind x
           (e , t' ) <- bwdSliceM (ORet (VInL p)) t at
           return ( ECase e (Match (x,e1) (bot,bot)), TCaseL t' x t1' )
    (p2, TCaseR t x t2, AnnotTrace _ [at, at2]) ->
        do (e2, t2') <- bwdSliceM p2 t2 at2
           p <- maybeLookupAndUnbind x
           (e , t' ) <- bwdSliceM (ORet (VInR p)) t at
           return ( ECase e (Match (bot,bot) (x,e2)), TCaseR t' x t2')
    (p, TCall t1 t2 l t, AnnotTrace _ [at1, at2, at]) ->
        do (e, t') <- bwdSliceM p (funBody t) at
           let f    = funName t
               x    = funArg  t
               k0   = Rec f x e Nothing
           p1 <- lookupAndUnbind f
           p2 <- lookupAndUnbind x
           rho0 <- resetEnv
           (e2, t2') <- bwdSliceM (ORet p2) t2 at2
           (e1, t1') <- bwdSliceM (ORet (p1 `lub` VClosure k0 rho0)) t1 at1
           return ( EApp e1 e2, TCall t1' t2' l (Rec f x t' Nothing))
    (OExn v, TCallExn t1 THole, AnnotTrace _ [at1, _]) ->
        do (e1, t1') <- bwdSliceM (OExn v) t1 at1
           return (EApp e1 EHole, TCallExn t1' THole)
    (OExn v, TCallExn t1 t2, AnnotTrace _ [at1, at2]) ->
        do (e2, t2') <- bwdSliceM (OExn v    ) t2 at2
           (e1, t1') <- bwdSliceM (ORet VHole) t1 at1
           return (EApp e1 e2, TCallExn t1' t2')
    (ORet (VRoll tv p), TRoll tv' t, AnnotTrace _ [at]) | tv == tv' ->
        do (e, t') <- bwdSliceM (ORet p) t at
           return (ERoll tv e, TRoll tv' t')
    (ORet VStar, TRoll tv' t, AnnotTrace _ [at]) ->
        do (e, t') <- bwdSliceM (ORet VStar) t at
           return (ERoll tv' e, TRoll tv' t')
    (OExn v, TRoll tv' t, AnnotTrace _ [at]) ->
        do (e, t') <- bwdSliceM (OExn v) t at
           return (ERoll tv' e, TRoll tv' t')
    (ORet p, TUnroll tv t, AnnotTrace _ [at]) ->
        do (e, t') <- bwdSliceM (ORet (VRoll tv p)) t at
           return (EUnroll tv e, TUnroll tv t')
    (OExn v, TUnroll tv t, AnnotTrace _ [at]) ->
        do (e, t') <- bwdSliceM (OExn v) t at
           return (EUnroll tv e, TUnroll tv t')
-- References.
    (ORet _, TRef (Just l) t, AnnotTrace _ [at]) ->
        do p <- storeDerefM l
           (e, t') <- bwdSliceM (ORet p) t at
           storeUpdateHoleM l
           return (ERef e, TRef (Just l) t')
    (OExn v, TRef Nothing t, AnnotTrace _ [at]) ->
        do (e, t') <- bwdSliceM (OExn v) t at
           return (ERef e, TRef Nothing t')
    (ORet v, TDeref (Just l) t, AnnotTrace _ [at])  ->
        do (e, t') <- bwdSliceM (ORet (toValue l)) t at
           v' <- storeDerefM l
           storeUpdateM l (v `lub` v')
           return (EDeref e, TDeref (Just l) t')
    (OExn v, TDeref Nothing t, AnnotTrace _ [at]) ->
        do (e, t') <- bwdSliceM (OExn v) t at
           return (EDeref e, TDeref Nothing t')
    (ORet _, TAssign (Just l) t1 t2, AnnotTrace _ [at1, at2]) ->
        do existsInStore <- existsInStoreM l
           if not existsInStore
           then return ( EHole, TSlicedHole (singletonStoreLabel l) RetValue)
           else do p <- storeDerefM l
                   storeUpdateHoleM l
                   (e2, t2') <- bwdSliceM (ORet p) t2 at2
                   (e1, t1') <- bwdSliceM (ORet (toValue l)) t1 at1
                   return ( EAssign e1 e2, TAssign (Just l) t1' t2')
    (OExn v, TAssign Nothing t1 THole, AnnotTrace _ [at1, _]) ->
        do (e1, t1') <- bwdSliceM (OExn v) t1 at1
           return (EAssign e1 EHole, TAssign Nothing t1' THole)
    (OExn v, TAssign Nothing t1 t2, AnnotTrace _ [at1, at2]) ->
        do (e2, t2') <- bwdSliceM (OExn v    ) t2 at2
           (e1, t1') <- bwdSliceM (ORet VStar) t1 at1
           return ( EAssign e1 e2, TAssign Nothing t1' t2')
-- Arrays
    (ORet _, TArr (Just (l,dim)) t1 t2, AnnotTrace _ [at1, at2]) ->
        do p <- storeDerefArrM l dim
           (e2, t2') <- bwdSliceM (ORet p    ) t2 at2
           (e1, t1') <- bwdSliceM (ORet VStar) t1 at1
           storeUpdateArrHoleM l
           return (EArr e1 e2, TArr (Just (l,dim)) t1' t2')
    (OExn v, TArr Nothing t1 THole, AnnotTrace _ [at1, _]) ->
        do (e1, t1') <- bwdSliceM (OExn v) t1 at1
           return (EArr e1 EHole, TArr Nothing t1' THole)
    (OExn v, TArr Nothing t1 t2, AnnotTrace _ [at1, at2]) ->
        do (e2, t2') <- bwdSliceM (OExn v) t2 at2
           (e1, t1') <- bwdSliceM (ORet VStar) t1 at1
           return (EArr e1 e2, TArr Nothing t1' t2')
    (ORet v, TArrGet (Just (l,idx)) t1 t2, AnnotTrace _ [at1, at2])  ->
        do (e2, t2') <- bwdSliceM (ORet VStar) t2 at2
           (e1, t1') <- bwdSliceM (ORet VStar) t1 at1
           v' <- storeDerefArrIdxM l idx
           storeUpdateArrIdxM l idx (v `lub` v')
           return (EArrGet e1 e2, TArrGet (Just (l,idx)) t1' t2')
    (OExn v, TArrGet Nothing t1 THole, AnnotTrace _ [at1, _]) ->
        do (e1, t1') <- bwdSliceM (OExn v) t1 at1
           return (EArrGet e1 EHole, TArrGet Nothing t1' THole)
    (OExn v, TArrGet Nothing t1 t2, AnnotTrace _ [at1, at2]) ->
        do (e2, t2') <- bwdSliceM (OExn v    ) t2 at2
           (e1, t1') <- bwdSliceM (ORet VStar) t1 at1
           return (EArrGet e1 e2, TArrGet Nothing t1' t2')
    (ORet _, TArrSet (Just (l,idx)) t1 t2 t3, AnnotTrace _ [at1, at2, at3]) ->
        do existsInStore <- existsInStoreM l
           if  not existsInStore
           then return ( EHole, TSlicedHole (singletonArrLabel (l,idx)) RetValue)
           else do
             p <- storeDerefArrIdxM l idx
             storeUpdateArrIdxHoleM l idx
             (e3, t3') <- bwdSliceM (ORet p) t3 at3
             (e2, t2') <- bwdSliceM (ORet (VInt (toInteger idx))) t2 at2
             (e1, t1') <- bwdSliceM (ORet (toValue l)) t1 at1
             return ( EArrSet e1 e2 e3, TArrSet (Just (l,idx)) t1' t2' t3')
    (OExn v, TArrSet Nothing t1 THole THole, AnnotTrace _ [at1, _, _]) ->
        do (e1, t1') <- bwdSliceM (OExn v) t1 at1
           return (EArrSet e1 EHole EHole, TArrSet Nothing t1' THole THole)
    (OExn v, TArrSet Nothing t1 t2 THole, AnnotTrace _ [at1, at2, _]) ->
        do (e2, t2') <- bwdSliceM (OExn v    ) t2 at2
           (e1, t1') <- bwdSliceM (ORet VStar) t1 at1
           return ( EArrSet e1 e2 EHole, TArrSet Nothing t1' t2' THole)
    (OExn v, TArrSet Nothing t1 t2 t3, AnnotTrace _ [at1, at2, at3]) ->
        do (e3, t3') <- bwdSliceM (OExn v    ) t3 at3
           (e2, t2') <- bwdSliceM (ORet VStar) t2 at2
           (e1, t1') <- bwdSliceM (ORet VStar) t1 at1
           return ( EArrSet e1 e2 e3, TArrSet Nothing t1' t2' t3')
-- Sequential composition and WHILE
    (OExn v, TSeq t1 THole, AnnotTrace _ [at1, _]) ->
        do (e1, t1') <- bwdSliceM (OExn v) t1 at1
           return (ESeq e1 EHole, TSeq t1' THole)
    (r, TSeq t1 t2, AnnotTrace _ [at1, at2]) ->
        do (e2, t2') <- bwdSliceM r t2 at2
           (e1, t1') <- bwdSliceM (ORet VHole) t1 at1
           return (ESeq e1 e2, TSeq t1' t2')
    (ORet _, TWhileDone t1, AnnotTrace _ [at1]) ->
        do (e1, t1') <- bwdSliceM (ORet VStar) t1 at1
           return (EWhile e1 EHole, TWhileDone t1')
    (OExn v, TWhileDone t1, AnnotTrace _ [at1]) ->
        do (e1, t1') <- bwdSliceM (OExn v) t1 at1
           return (EWhile e1 EHole, TWhileDone t1')
    (ORet _, TWhileStep t1 t2 t3, AnnotTrace _ [at1, at2, at3]) ->
        do (e3, t3') <- bwdSliceM (ORet VHole) t3 at3
           (e2, t2') <- bwdSliceM (ORet VHole) t2 at2
           (e1, t1') <- bwdSliceM (ORet VStar) t1 at1
           return ( (EWhile e1 e2) `lub` e3, TWhileStep t1' t2' t3')
    (OExn v, TWhileStep t1 THole THole, AnnotTrace _ [at1, _, _]) ->
        do (e1, t1') <- bwdSliceM (OExn v) t1 at1
           return ( EWhile e1 EHole, TWhileStep t1' THole THole)
    (OExn v, TWhileStep t1 t2 THole, AnnotTrace _ [at1, at2, _]) ->
        do (e2, t2') <- bwdSliceM (OExn v    ) t2 at2
           (e1, t1') <- bwdSliceM (ORet VStar) t1 at1
           return ( EWhile e1 e2, TWhileStep t1' t2' THole)
    (OExn v, TWhileStep t1 t2 t3, AnnotTrace _ [at1, at2, at3]) ->
        do (e3, t3') <- bwdSliceM (OExn v    ) t3 at3
           (e2, t2') <- bwdSliceM (ORet VHole) t2 at2
           (e1, t1') <- bwdSliceM (ORet VStar) t1 at1
           return ( (EWhile e1 e2) `lub` e3, TWhileStep t1' t2' t3')
    (ORet v, TTry t, AnnotTrace _ [at]) ->
        do (e, t') <- bwdSliceM (ORet v) t at
           return (ETryWith e bot bot, TTry t')
    (r, TTryWith t1 x t2, AnnotTrace _ [at1, at2]) ->
        do (e2, t2') <- bwdSliceM r t2 at2
           p1 <- lookupAndUnbind x
           (e1, t1') <- bwdSliceM (OExn p1) t1 at1
           return (ETryWith e1 x e2, TTryWith t1' x t2')

    _ -> error $ "Cannot slice outcome " ++ show outcome ++
                 " from trace " ++ show trace ++ " and trace annotations " ++
                 show traceAnnot


--------------------------------------------------------------------------------
--                        SLICING HELPER FUNCTIONS                            --
--------------------------------------------------------------------------------


-- | A tree storing information about labels written to by a trace
data AnnotTrace = AnnotTrace StoreLabels [AnnotTrace]
                deriving Show

getStoreWrites :: AnnotTrace -> StoreLabels
getStoreWrites (AnnotTrace labels _) = labels

mkAnnotTrace :: StoreLabels -> [Trace] -> AnnotTrace
mkAnnotTrace labels traces =
    let annotTraces = map annotTrace traces
        storeWrites = unionsStoreLabels (labels : map getStoreWrites annotTraces)
    in AnnotTrace storeWrites annotTraces

mkPureAnnotTrace :: [Trace] -> AnnotTrace
mkPureAnnotTrace traces =
    mkAnnotTrace emptyStoreLabels traces

mkEmptyAnnotTrace :: AnnotTrace
mkEmptyAnnotTrace =
    mkAnnotTrace emptyStoreLabels []

-- | Get list of labels that a trace writes to
annotTrace :: Trace -> AnnotTrace
-- relevant store assignments
annotTrace (TRef l t) =
    mkAnnotTrace (maybeSingletonStoreLabel l) [t]
annotTrace (TAssign l t1 t2) =
    mkAnnotTrace (maybeSingletonStoreLabel l) [t1,t2]
-- relevant array assignments
annotTrace (TArr l t1 t2) = -- All labels (l,0)...(l,dim-1)
    mkAnnotTrace (arrWrites l) [t1, t2]
annotTrace (TArrSet l t1 t2 t3) =
    mkAnnotTrace (maybeSingletonArrLabel l) [t1, t2, t3]
-- sliced hole annotated with store labels
annotTrace (TCall t1 t2 _ (Rec _ _ t3 _)) =
    mkPureAnnotTrace [t1, t2, t3]
annotTrace (TSlicedHole ls _)    = mkAnnotTrace ls []
annotTrace (TIfThen t1 t2)       = mkPureAnnotTrace [t1, t2]
annotTrace (TIfElse t1 t2)       = mkPureAnnotTrace [t1, t2]
annotTrace (TIfExn t)            = mkPureAnnotTrace [t]
annotTrace (TCaseL t1 _ t2)      = mkPureAnnotTrace [t1, t2]
annotTrace (TCaseR t1 _ t2)      = mkPureAnnotTrace [t1, t2]
annotTrace (TCallExn t1 t2)      = mkPureAnnotTrace [t1, t2]
annotTrace (TDeref _ t)          = mkPureAnnotTrace [t]
annotTrace (TArrGet _ t1 t2)     = mkPureAnnotTrace [t1, t2]
annotTrace (TWhileDone t)        = mkPureAnnotTrace [t]
annotTrace (TWhileStep t1 t2 t3) = mkPureAnnotTrace [t1, t2, t3]
annotTrace (TRaise t)            = mkPureAnnotTrace [t]
annotTrace (TTry t)              = mkPureAnnotTrace [t]
annotTrace (TTryWith t1 _ t2)    = mkPureAnnotTrace [t1, t2]
annotTrace (TLet _ t1 t2)        = mkPureAnnotTrace [t1, t2]
annotTrace (TPair t1 t2)         = mkPureAnnotTrace [t1, t2]
annotTrace (TSeq t1 t2)          = mkPureAnnotTrace [t1, t2]
annotTrace (TOp _ _ ts)          = mkPureAnnotTrace ts
annotTrace (TFst t)              = mkPureAnnotTrace [t]
annotTrace (TSnd t)              = mkPureAnnotTrace [t]
annotTrace (TInL t)              = mkPureAnnotTrace [t]
annotTrace (TInR t)              = mkPureAnnotTrace [t]
annotTrace (TRoll _ t)           = mkPureAnnotTrace [t]
annotTrace (TUnroll _ t)         = mkPureAnnotTrace [t]
annotTrace TUnit                 = mkEmptyAnnotTrace
annotTrace (TVar _)              = mkEmptyAnnotTrace
annotTrace (TBool _)             = mkEmptyAnnotTrace
annotTrace (TInt _)              = mkEmptyAnnotTrace
annotTrace (TString _)           = mkEmptyAnnotTrace
annotTrace (TDouble _)           = mkEmptyAnnotTrace
annotTrace (TFun _)              = mkEmptyAnnotTrace
annotTrace THole                 = mkEmptyAnnotTrace
annotTrace (TExp e)
    = error ("Impossible happened at annotTrace: " ++ show e)
