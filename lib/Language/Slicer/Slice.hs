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
traceSlice :: Store -> Value -> Trace -> (Trace, Env Value)
traceSlice store value trace =
    let (env, _, _, trace') = bwdSlice store value trace
    in (trace', env)

bwdSlice :: Store -> Value -> Trace -> (Env Value, Store, Exp, Trace)
bwdSlice store value trace = runSliceM store (bwdSliceM value trace)

-- Unevaluation (program slicing) as described in Section 4.3 of the ICFP'12
-- paper
bwdSliceM :: Value -> Trace -> SliceM (Env Value, Exp, Trace)
bwdSliceM value trace = do
  allStoreHoles <- allStoreHolesM (storeWrites trace)
  case (value, trace) of
    (VHole, TRaise t) ->
        do (rho, e, t') <- bwdSliceM VStar t
           return (rho, ERaise e, TRaise t')
    (VException VHole, _) | allStoreHoles ->
        return (bot, EHole, TSlicedHole (storeWrites trace) RetRaise)
    (VHole, _) | allStoreHoles ->
        return (bot, EHole, TSlicedHole (storeWrites trace) RetValue)
    (VException _, THole) -> -- JSTOLAREK: speculative equation
        return (bot, EHole, THole)
    (VStar, THole) -> -- JSTOLAREK: another speculative equation
        return (bot, EHole, THole)
    (VException v, TRaise t) ->
        do (rho, e, t') <- bwdSliceM v t
           return (rho, ERaise e, TRaise t')
    (VStar, TRaise t) ->
        do (rho, e, t') <- bwdSliceM VStar t
           return (rho, ERaise e, TRaise t')
    (v, TVar x) ->
        return (singletonEnv x v, EVar x, TVar x)
    (VUnit, TUnit) ->
        return (bot, EUnit, TUnit)
    (VStar, TUnit) ->
        return (bot, EUnit, TUnit)
    (VBool b, TBool b') | b == b' ->
        return (bot, EBool b, TBool b)
    (VStar, TBool b) ->
        return (bot, EBool b, TBool b)
    (VInt i, TInt i') | i == i' ->
        return (bot, EInt i, TInt i)
    (VStar, TInt i) ->
        return (bot, EInt i, TInt i)
    (VString s, TString s') | s == s' ->
        return (bot, EString s, TString s)
    (VStar, TString s) ->
        return (bot, EString s, TString s)
    (VClosure k env, TFun k') | k `leq` k' ->
        return (env, EFun k, TFun k')
    (VStar, TFun k) ->
        return (constEnv (fvs k) VStar, EFun k, TFun k)
    (VPair p1 p2, TPair t1 t2) ->
        do (rho2, e2, t2') <- bwdSliceM p2 t2
           (rho1, e1, t1') <- bwdSliceM p1 t1
           return (rho1 `lub` rho2, EPair e1 e2, TPair t1' t2')
    (VStar, TPair t1 t2) ->
        do (rho2, e2, t2') <- bwdSliceM VStar t2
           (rho1, e1, t1') <- bwdSliceM VStar t1
           return (rho1 `lub` rho2, EPair e1 e2, TPair t1' t2')
    (v, TPair t1 THole) | isException v ->
        do (rho1, e1, t1') <- bwdSliceM v t1
           return (rho1, EPair e1 EHole, TPair t1' THole)
    (v, TPair t1 t2) | isException v ->
        do (rho2, e2, t2') <- bwdSliceM v t2
           (rho1, e1, t1') <- bwdSliceM VHole t1
           return (rho1 `lub` rho2, EPair e1 e2, TPair t1' t2')
    (p, TFst t) ->
        do (rho, e', t') <- bwdSliceM (VPair p bot) t
           return (rho, EFst e', TFst t')
    (p, TSnd t) ->
        do (rho, e', t') <- bwdSliceM (VPair bot p) t
           return (rho, ESnd e', TSnd t')
    (VInL p, TInL t) ->
        do (rho, e', t') <- bwdSliceM p t
           return (rho, EInL e', TInL t')
    (VStar, TInL t) ->
        do (rho, e', t') <- bwdSliceM VStar t
           return (rho, EInL e', TInL t')
    (v, TInL t) | isException v ->
        do (rho, e', t') <- bwdSliceM v t
           return (rho, EInL e', TInL t')
    (VInR p, TInR t) ->
        do (rho, e', t') <- bwdSliceM p t
           return (rho, EInR e', TInR t')
    (VStar, TInR t) ->
        do (rho, e', t') <- bwdSliceM VStar t
           return (rho, EInR e', TInR t')
    (v, TInR t) | isException v ->
        do (rho, e', t') <- bwdSliceM v t
           return (rho, EInR e', TInR t')
    (p, TLet x t THole) -> -- JSTOLAREK: This case should be redundant
        do (rho, e1, t1') <- bwdSliceM p t
           return (rho, ELet x e1 EHole, TLet x t1' THole)
    (p2, TLet x t1 t2) ->
        do (rho2, e2, t2') <- bwdSliceM p2 t2
           let p1    = lookupEnv' rho2 x
               rho2' = unbindEnv  rho2 x
           (rho1, e1, t1') <- bwdSliceM p1 t1
           return (rho1 `lub` rho2', ELet x e1 e2, TLet x t1' t2')
    (_, TOp f ts) ->
        do let bwdSliceArgM t' (rho', es', ts')
                 = do (rho'', e, t) <- bwdSliceM VStar t'
                      return (rho' `lub` rho'', e:es', t:ts')
           (rho, esA, tsA) <- foldrM bwdSliceArgM (bot, [], []) ts
           return (rho, EOp f esA, TOp f tsA)
    (p1, TIfThen t t1) ->
        do (rho1, e1, t1') <- bwdSliceM p1 t1
           (rho , e , t' ) <- bwdSliceM VStar t
           return (rho1 `lub` rho, EIf e e1 EHole, TIfThen t' t1')
    (p2, TIfElse t t2) ->
        do (rho2, e2, t2') <- bwdSliceM p2 t2
           (rho , e , t' ) <- bwdSliceM VStar t
           return (rho2 `lub` rho, EIf e EHole e2, TIfElse t' t2')
    (p, TIfExn t) ->
        do (rho, e, t') <- bwdSliceM p t
           return (rho, EIf e EHole EHole, TIfExn t')
    (p1, TCaseL t x t1) ->
        do (rho1, e1, t1') <- bwdSliceM p1 t1
           let p     = maybeLookupEnv' rho1 x
               rho1' = maybeUnbindEnv  rho1 x
           (rho, e , t' ) <- bwdSliceM (VInL p) t
           return ( rho `lub` rho1', ECase e (Match (x,e1) (bot,bot))
                  , TCaseL t' x t1' )
    (p2, TCaseR t x t2) ->
        do (rho2, e2, t2') <- bwdSliceM p2 t2
           let p     = maybeLookupEnv' rho2 x
               rho2' = maybeUnbindEnv  rho2 x
           (rho, e , t' ) <- bwdSliceM (VInR p) t
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
           (rho2, e2, t2') <- bwdSliceM p2 t2
           (rho1, e1, t1') <- bwdSliceM (p1 `lub` VClosure k0 rho0) t1
           return ( rho1 `lub` rho2, EApp e1 e2
                  , TCall t1' t2' l (Rec f x t' Nothing))
    (p, TCallExn t1 t2) ->
        do (rho2, e2, t2') <- bwdSliceM p t2
           (rho1, e1, t1') <- bwdSliceM p t1
           return (rho1 `lub` rho2, EApp e1 e2, TCallExn t1' t2')
    (VRoll tv p, TRoll tv' t) | tv == tv' ->
        do (rho, e, t') <- bwdSliceM p t
           return (rho, ERoll tv e, TRoll tv' t')
    (VStar, TRoll tv' t) ->
        do (rho, e, t') <- bwdSliceM VStar t
           return (rho, ERoll tv' e, TRoll tv' t')
    (v, TRoll tv' t) | isException v ->
        do (rho, e, t') <- bwdSliceM v t
           return (rho, ERoll tv' e, TRoll tv' t')
    (p, TUnroll tv t) ->
        do (rho, e, t') <- bwdSliceM (VRoll tv p) t
           return (rho, EUnroll tv e, TUnroll tv t')
    (v, TRef (Just l) t) | not (isException v) ->
        do p <- storeDerefM l
           (rho, e, t') <- bwdSliceM p t
           storeUpdateHoleM l
           return (rho, ERef e, TRef (Just l) t')
    (v, TRef Nothing t) | isException v ->
        do (rho, e, t') <- bwdSliceM v t
           return (rho, ERef e, TRef Nothing t')
    (v, TDeref (Just l) t) | not (isException v) ->
        do (rho, e, t') <- bwdSliceM (toValue l) t
           storeUpdateM l v
           return (rho, EDeref e, TDeref (Just l) t')
    (v, TDeref Nothing t) | isException v ->
        do (rho, e, t') <- bwdSliceM v t
           return (rho, EDeref e, TDeref Nothing t')
    (v, TAssign (Just l) t1 t2) ->
        do existsInStore <- existsInStoreM l
           if | not existsInStore ->
                  return (bot, EHole, TSlicedHole (singletonStoreLabel l)
                                      RetValue)
              | not (isException v) ->
                  do p <- storeDerefM l
                     storeUpdateHoleM l
                     (rho2, e2, t2') <- bwdSliceM p t2
                     (rho1, e1, t1') <- bwdSliceM (toValue l) t1
                     return ( rho1 `lub` rho2, EAssign e1 e2
                            , TAssign (Just l) t1' t2')
              | otherwise -> -- isException v == True
                  do (rho2, e2, t2') <- bwdSliceM v t2
                     (rho1, e1, t1') <- bwdSliceM (toValue l) t1
                     return ( rho1 `lub` rho2, EAssign e1 e2
                            , TAssign (Just l) t1' t2')
    (v, TAssign Nothing t1 THole) | isException v ->
        do (rho, e1, t1') <- bwdSliceM v t1
           return (rho, EAssign e1 EHole, TAssign Nothing t1' THole)
    (v, TSeq t1 t2) ->
        do (rho2, e2, t2') <- bwdSliceM v t2
           (rho1, e1, t1') <- bwdSliceM VHole t1
           return (rho1 `lub` rho2, ESeq e1 e2, TSeq t1' t2')
    (v, TTry t) ->
        do (rho, e, t') <- bwdSliceM v t
           return (rho, ETryWith e bot bot, TTry t')
    (v, TTryWith t1 x t2) ->
        do (rho2, e2, t2') <- bwdSliceM v t2
           let p1    = lookupEnv' rho2 x
               rho2' = unbindEnv  rho2 x
           (rho1, e1, t1') <- bwdSliceM (VException p1) t1
           return (rho1 `lub` rho2', ETryWith e1 x e2, TTryWith t1' x t2')
    _ -> error $ "Cannot slice value " ++ show value ++
                 " from trace " ++ show trace
