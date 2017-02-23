{-# LANGUAGE FunctionalDependencies  #-}
{-# LANGUAGE NamedFieldPuns          #-}
{-# LANGUAGE MultiParamTypeClasses   #-}
{-# LANGUAGE MultiWayIf              #-}
{-# LANGUAGE UndecidableInstances    #-}

module Language.Slicer.Slice
    ( traceSlice, bwdSlice
    ) where

import           Language.Slicer.Core hiding ( allStoreHoles, existsInStore )
import           Language.Slicer.Env
import           Language.Slicer.Monad.Slice
import           Language.Slicer.UpperSemiLattice

import           Data.Foldable

-- Trace slicing (backward slicing) as described in section 5 of the ICFP 12
-- paper
traceSlice :: Store -> Outcome -> Trace -> (Trace, Env Value)
traceSlice store outcome trace =
    let (env, _, _, trace') = bwdSlice store outcome trace
    in (trace', env)

bwdSlice :: Store -> Outcome -> Trace -> (Env Value, Store, Exp, Trace)
bwdSlice store outcome trace = runSliceM store (bwdSliceM outcome trace)

-- Unevaluation (program slicing) as described in Section 4.3 of the ICFP'12
-- paper
bwdSliceM :: Outcome -> Trace -> SliceM (Env Value, Exp, Trace)
bwdSliceM outcome trace = do
  allStoreHoles <- allStoreHolesM (storeWrites trace)
  case (outcome, trace) of
    (OExn VHole, TRaise t) ->
        do (rho, e, t') <- bwdSliceM (ORet VStar) t
           return (rho, ERaise e, TRaise t')
    (OExn VHole, _) | allStoreHoles ->
        return (bot, EHole, TSlicedHole (storeWrites trace) RetRaise)
    (ORet VHole, _) | allStoreHoles ->
        return (bot, EHole, TSlicedHole (storeWrites trace) RetValue)
    (ORet VStar, THole) -> -- JSTOLAREK: another speculative equation
        return (bot, EHole, THole)
    (OExn v, TRaise t) | isRaise t->
        do (rho, e, t') <- bwdSliceM (OExn v) t
           return (rho, ERaise e, TRaise t')
    (OExn v, TRaise t) ->
        do (rho, e, t') <- bwdSliceM (ORet v) t
           return (rho, ERaise e, TRaise t')
    (ORet v, TVar x) ->
        return (singletonEnv x v, EVar x, TVar x)
    (ORet VUnit, TUnit) ->
        return (bot, EUnit, TUnit)
    (ORet VStar, TUnit) ->
        return (bot, EUnit, TUnit)
    (ORet (VBool b), TBool b') | b == b' ->
        return (bot, EBool b, TBool b)
    (ORet VStar, TBool b) ->
        return (bot, EBool b, TBool b)
    (ORet (VInt i), TInt i') | i == i' ->
        return (bot, EInt i, TInt i)
    (ORet VStar, TInt i) ->
        return (bot, EInt i, TInt i)
    (ORet (VString s), TString s') | s == s' ->
        return (bot, EString s, TString s)
    (ORet VStar, TString s) ->
        return (bot, EString s, TString s)
    (ORet (VClosure k env), TFun k') | k `leq` k' ->
        return (env, EFun k, TFun k')
    (ORet VStar, TFun k) ->
        return (constEnv (fvs k) VStar, EFun k, TFun k)
    (ORet (VPair p1 p2), TPair t1 t2) ->
        do (rho2, e2, t2') <- bwdSliceM (ORet p2) t2
           (rho1, e1, t1') <- bwdSliceM (ORet p1) t1
           return (rho1 `lub` rho2, EPair e1 e2, TPair t1' t2')
    (ORet VStar, TPair t1 t2) ->
        do (rho2, e2, t2') <- bwdSliceM (ORet VStar) t2
           (rho1, e1, t1') <- bwdSliceM (ORet VStar) t1
           return (rho1 `lub` rho2, EPair e1 e2, TPair t1' t2')
    (OExn v, TPair t1 THole)  -> 
        do (rho1, e1, t1') <- bwdSliceM (OExn v) t1
           return (rho1, EPair e1 EHole, TPair t1' THole)
    (OExn v, TPair t1 t2) -> 
        do (rho2, e2, t2') <- bwdSliceM (OExn v) t2
           (rho1, e1, t1') <- bwdSliceM (ORet VHole) t1
           return (rho1 `lub` rho2, EPair e1 e2, TPair t1' t2')
    (ORet p, TFst t) ->
        do (rho, e', t') <- bwdSliceM (ORet (VPair p bot)) t
           return (rho, EFst e', TFst t')
    (OExn v, TFst t) ->
        do (rho, e', t') <- bwdSliceM (OExn v) t
           return (rho, EFst e', TFst t')
    (ORet p, TSnd t) ->
        do (rho, e', t') <- bwdSliceM (ORet (VPair bot p)) t
           return (rho, ESnd e', TSnd t')
    (OExn v, TSnd t) ->
        do (rho, e', t') <- bwdSliceM (OExn v) t
           return (rho, ESnd e', TSnd t')
    (ORet (VInL p), TInL t) ->
        do (rho, e', t') <- bwdSliceM (ORet p) t
           return (rho, EInL e', TInL t')
    (ORet VStar, TInL t) ->
        do (rho, e', t') <- bwdSliceM (ORet VStar) t
           return (rho, EInL e', TInL t')
    (OExn v, TInL t) ->
        do (rho, e', t') <- bwdSliceM (OExn v) t
           return (rho, EInL e', TInL t')
    (ORet (VInR p), TInR t) ->
        do (rho, e', t') <- bwdSliceM (ORet p) t
           return (rho, EInR e', TInR t')
    (ORet VStar, TInR t) ->
        do (rho, e', t') <- bwdSliceM (ORet VStar) t
           return (rho, EInR e', TInR t')
    (OExn v, TInR t)  ->
        do (rho, e', t') <- bwdSliceM (OExn v) t
           return (rho, EInR e', TInR t')
    (r, TLet x t THole) -> -- JSTOLAREK: This case should be redundant
        do (rho, e1, t1') <- bwdSliceM r t
           return (rho, ELet x e1 EHole, TLet x t1' THole)
    (r, TLet x t1 t2) ->
        do (rho2, e2, t2') <- bwdSliceM r t2
           let p1    = lookupEnv' rho2 x
               rho2' = unbindEnv  rho2 x
           (rho1, e1, t1') <- bwdSliceM (ORet p1) t1
           return (rho1 `lub` rho2', ELet x e1 e2, TLet x t1' t2')
    (_, TOp f ts) -> -- JRC: need to be more careful here
        do let bwdSliceArgM t' (rho', es', ts')
                 = do (rho'', e, t) <- bwdSliceM (ORet VStar) t'
                      return (rho' `lub` rho'', e:es', t:ts')
           (rho, esA, tsA) <- foldrM bwdSliceArgM (bot, [], []) ts
           return (rho, EOp f esA, TOp f tsA)
    (p1, TIfThen t t1) ->
        do (rho1, e1, t1') <- bwdSliceM p1 t1
           (rho , e , t' ) <- bwdSliceM (ORet VStar) t
           return (rho1 `lub` rho, EIf e e1 EHole, TIfThen t' t1')
    (p2, TIfElse t t2) ->
        do (rho2, e2, t2') <- bwdSliceM p2 t2
           (rho , e , t' ) <- bwdSliceM (ORet VStar) t
           return (rho2 `lub` rho, EIf e EHole e2, TIfElse t' t2')
    (OExn p, TIfExn t) ->
        do (rho, e, t') <- bwdSliceM (OExn p) t
           return (rho, EIf e EHole EHole, TIfExn t')
    (p1, TCaseL t x t1) ->
        do (rho1, e1, t1') <- bwdSliceM p1 t1
           let p     = maybeLookupEnv' rho1 x
               rho1' = maybeUnbindEnv  rho1 x
           (rho, e , t' ) <- bwdSliceM (ORet (VInL p)) t
           return ( rho `lub` rho1', ECase e (Match (x,e1) (bot,bot))
                  , TCaseL t' x t1' )
    (p2, TCaseR t x t2) ->
        do (rho2, e2, t2') <- bwdSliceM p2 t2
           let p     = maybeLookupEnv' rho2 x
               rho2' = maybeUnbindEnv  rho2 x
           (rho, e , t' ) <- bwdSliceM (ORet (VInR p)) t
           return ( rho `lub` rho2', ECase e (Match (bot,bot) (x,e2))
                  , TCaseR t' x t2')
    (p, TCall t1 t2 l t) ->  
        do (rho, e, t') <- bwdSliceM p (funBody t)
           let f    = funName t
               x    = funArg  t
               k0   = Rec f x e Nothing
               p1   = lookupEnv' rho f
               p2   = lookupEnv' rho x
               rho0 = unbindEnv (unbindEnv rho f) x
           (rho2, e2, t2') <- bwdSliceM (ORet p2) t2
           (rho1, e1, t1') <- bwdSliceM (ORet (p1 `lub` VClosure k0 rho0)) t1
           return ( rho1 `lub` rho2, EApp e1 e2
                  , TCall t1' t2' l (Rec f x t' Nothing))
    (OExn v, TCallExn t1 THole) ->
        do (rho1, e1, t1') <- bwdSliceM (OExn v) t1
           return (rho1, EApp e1 EHole, TCallExn t1' THole)
    (OExn v, TCallExn t1 t2) ->
        do (rho2, e2, t2') <- bwdSliceM (OExn v) t2
           (rho1, e1, t1') <- bwdSliceM (ORet VHole) t1
           return (rho1 `lub` rho2, EApp e1 e2, TCallExn t1' t2')
    (ORet (VRoll tv p), TRoll tv' t) | tv == tv' ->
        do (rho, e, t') <- bwdSliceM (ORet p) t
           return (rho, ERoll tv e, TRoll tv' t')
    (ORet VStar, TRoll tv' t) ->
        do (rho, e, t') <- bwdSliceM (ORet VStar) t
           return (rho, ERoll tv' e, TRoll tv' t')
    (OExn v, TRoll tv' t) ->
        do (rho, e, t') <- bwdSliceM (OExn v) t
           return (rho, ERoll tv' e, TRoll tv' t')
    (ORet p, TUnroll tv t) ->
        do (rho, e, t') <- bwdSliceM (ORet (VRoll tv p)) t
           return (rho, EUnroll tv e, TUnroll tv t')
    (OExn v, TUnroll tv t) ->
        do (rho, e, t') <- bwdSliceM (OExn v) t
           return (rho, EUnroll tv e, TUnroll tv t')
    (ORet _, TRef (Just l) t) ->
        do p <- storeDerefM l
           (rho, e, t') <- bwdSliceM (ORet p) t
           storeUpdateHoleM l
           return (rho, ERef e, TRef (Just l) t')
    (OExn v, TRef Nothing t) ->
        do (rho, e, t') <- bwdSliceM (OExn v) t
           return (rho, ERef e, TRef Nothing t')
    (ORet v, TDeref (Just l) t)  ->
        do (rho, e, t') <- bwdSliceM (ORet (toValue l)) t
           storeUpdateM l v
           return (rho, EDeref e, TDeref (Just l) t')
    (OExn v, TDeref Nothing t) ->
        do (rho, e, t') <- bwdSliceM (OExn v) t
           return (rho, EDeref e, TDeref Nothing t')
    (ORet _, TAssign (Just l) t1 t2) ->
        do existsInStore <- existsInStoreM l
           if  not existsInStore
           then return (bot, EHole,
                        TSlicedHole (singletonStoreLabel l) RetValue)
           else   do p <- storeDerefM l
                     storeUpdateHoleM l
                     (rho2, e2, t2') <- bwdSliceM (ORet p) t2
                     (rho1, e1, t1') <- bwdSliceM (ORet (toValue l)) t1
                     return ( rho1 `lub` rho2, EAssign e1 e2
                            , TAssign (Just l) t1' t2')
    (OExn v, TAssign (Just l) t1 t2) ->
        do existsInStore <- existsInStoreM l
           if not existsInStore
           then return (bot, EHole,
                        TSlicedHole (singletonStoreLabel l) RetValue)
           else   do (rho2, e2, t2') <- bwdSliceM (OExn v) t2
                     (rho1, e1, t1') <- bwdSliceM (ORet (toValue l)) t1
                     return ( rho1 `lub` rho2, EAssign e1 e2
                            , TAssign (Just l) t1' t2')
    (OExn v, TAssign Nothing t1 THole) ->
        do (rho, e1, t1') <- bwdSliceM (OExn v) t1
           return (rho, EAssign e1 EHole, TAssign Nothing t1' THole)
    (OExn v, TSeq t1 THole) ->
        do (rho1, e1, t1') <- bwdSliceM (OExn v) t1
           return (rho1, ESeq e1 EHole, TSeq t1' THole)
    (r, TSeq t1 t2) ->
        do (rho2, e2, t2') <- bwdSliceM r t2
           (rho1, e1, t1') <- bwdSliceM (ORet VHole) t1
           return (rho1 `lub` rho2, ESeq e1 e2, TSeq t1' t2')
    (OExn v, TTry t) ->
        do (rho, e, t') <- bwdSliceM (OExn v) t
           return (rho, ETryWith e bot bot, TTry t')
    (r, TTryWith t1 x t2) ->
        do (rho2, e2, t2') <- bwdSliceM r t2
           let p1    = lookupEnv' rho2 x
               rho2' = unbindEnv  rho2 x
           (rho1, e1, t1') <- bwdSliceM (OExn p1) t1
           return (rho1 `lub` rho2', ETryWith e1 x e2, TTryWith t1' x t2')
    _ -> error $ "Cannot slice outcome " ++ show outcome ++
                 " from trace " ++ show trace
