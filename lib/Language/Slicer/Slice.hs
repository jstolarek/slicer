{-# LANGUAGE FunctionalDependencies  #-}
{-# LANGUAGE NamedFieldPuns          #-}
{-# LANGUAGE MultiParamTypeClasses   #-}
{-# LANGUAGE UndecidableInstances    #-}

module Language.Slicer.Slice
    ( traceSlice, bwdSlice
    ) where

import           Language.Slicer.Core
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
bwdSlice store value trace = runSliceM (bwdSliceM store value trace)

-- Unevaluation (program slicing) as described in Section 4.3 of the ICFP'12
-- paper
bwdSliceM :: Store -> Value -> Trace -> SliceM (Env Value, Store, Exp, Trace)
bwdSliceM store VHole (TRaise t)
    = do (rho, store', e, t') <- bwdSliceM store VStar t
         return (rho, store', ERaise e, TRaise t')
bwdSliceM store (VException VHole) trace
    | allStoreHoles store (storeWrites trace)
    = return (bot,  store, bot, TSlicedHole (storeWrites trace) RetRaise)
bwdSliceM store VHole trace
    | allStoreHoles store (storeWrites trace)
    = return (bot,  store, bot, TSlicedHole (storeWrites trace) RetValue)
bwdSliceM store (VException _) THole -- JSTOLAREK: speculative equation
    = return (bot, store, EHole, THole)
bwdSliceM store VStar THole -- JSTOLAREK: another speculative equation
    = return (bot, store, EHole, THole)
bwdSliceM store (VException v) (TRaise t)
    = do (rho, store', e, t') <- bwdSliceM store v t
         return (rho, store', ERaise e, TRaise t')
bwdSliceM store VStar (TRaise t)
    = do (rho, store', e, t') <- bwdSliceM store VStar t
         return (rho, store', ERaise e, TRaise t')
bwdSliceM store v (TVar x)
    = return (singletonEnv x v, store, EVar x, TVar x)
bwdSliceM store VUnit TUnit
    = return (bot, store, EUnit, TUnit)
bwdSliceM store VStar TUnit
    = return (bot, store, EUnit, TUnit)
bwdSliceM store (VBool b) (TBool b') | b == b'
    = return (bot, store, EBool b, TBool b)
bwdSliceM store VStar (TBool b)
    = return (bot, store, EBool b, TBool b)
bwdSliceM store (VInt i) (TInt i') | i == i'
    = return (bot, store, EInt i, TInt i)
bwdSliceM store VStar (TInt i)
    = return (bot, store, EInt i, TInt i)
bwdSliceM store (VString s) (TString s') | s == s'
    = return (bot, store, EString s, TString s)
bwdSliceM store VStar (TString s)
    = return (bot, store, EString s, TString s)
bwdSliceM store (VClosure k env) (TFun k') | k `leq` k'
    = return (env, store, EFun k, TFun k')
bwdSliceM store VStar (TFun k)
    = return (constEnv (fvs k) VStar, store, EFun k, TFun k)
bwdSliceM store (VPair p1 p2) (TPair t1 t2)
    = do (rho2, store2, e2, t2') <- bwdSliceM store  p2 t2
         (rho1, store1, e1, t1') <- bwdSliceM store2 p1 t1
         return (rho1 `lub` rho2, store1, EPair e1 e2, TPair t1' t2')
bwdSliceM store VStar (TPair t1 t2)
    = do (rho2, store2, e2, t2') <- bwdSliceM store  VStar t2
         (rho1, store1, e1, t1') <- bwdSliceM store2 VStar t1
         return (rho1 `lub` rho2, store1, EPair e1 e2, TPair t1' t2')
bwdSliceM store p (TFst t)
    = do (rho, store', e', t') <- bwdSliceM store (VPair p bot) t
         return (rho, store', EFst e', TFst t')
bwdSliceM store p (TSnd t)
    = do (rho, store', e', t') <- bwdSliceM store (VPair bot p) t
         return (rho, store', ESnd e', TSnd t')
bwdSliceM store (VInL p) (TInL t)
    = do (rho, store', e', t') <- bwdSliceM store p t
         return (rho, store', EInL e', TInL t')
bwdSliceM store VStar (TInL t)
    = do (rho, store', e', t') <- bwdSliceM store VStar t
         return (rho, store', EInL e', TInL t')
bwdSliceM store (VInR p) (TInR t)
    = do (rho, store', e', t') <- bwdSliceM store p t
         return (rho, store', EInR e', TInR t')
bwdSliceM store VStar (TInR t)
    = do (rho, store', e', t') <- bwdSliceM store VStar t
         return (rho, store', EInR e', TInR t')
-- JSTOLAREK: This case should be redundant
bwdSliceM store p (TLet x t THole)
    = do (rho1, store', e1, t1') <- bwdSliceM store p t
         return (rho1, store', ELet x e1 EHole, TLet x t1' THole)
bwdSliceM store p2 (TLet x t1 t2)
    = do (rho2, store2, e2, t2') <- bwdSliceM store p2 t2
         let p1    = lookupEnv' rho2 x
             rho2' = unbindEnv  rho2 x
         (rho1, store1, e1, t1') <- bwdSliceM store2 p1 t1
         return (rho1 `lub` rho2', store1, ELet x e1 e2, TLet x t1' t2')
bwdSliceM store _ (TOp f ts)
    = do let bwdSliceArgM t' (rho', store', es', ts')
                 = do (rho'', store'', e, t) <- bwdSliceM store' VStar t'
                      return (rho' `lub` rho'', store'', e:es', t:ts')
         (rhoA, storeA, esA, tsA) <- foldrM bwdSliceArgM (bot, store, [], []) ts
         return (rhoA, storeA, EOp f esA, TOp f tsA)
bwdSliceM store p1 (TIfThen t t1)
    = do (rho1, store1, e1, t1') <- bwdSliceM store p1 t1
         (rho , store2, e , t' ) <- bwdSliceM store1 VStar t
         return (rho `lub` rho1, store2, EIf e e1 EHole, TIfThen t' t1')
bwdSliceM store p2 (TIfElse t t2)
    = do (rho2, store1, e2, t2') <- bwdSliceM store p2 t2
         (rho , store2, e , t' ) <- bwdSliceM store1 VStar t
         return (rho `lub` rho2, store2, EIf e EHole e2, TIfElse t' t2')
bwdSliceM store p (TIfExn t)
    = do (rho, store', e, t') <- bwdSliceM store p t
         return (rho, store', EIf e EHole EHole, TIfExn t')
bwdSliceM store p1 (TCaseL t x t1)
    = do (rho1, store1, e1, t1') <- bwdSliceM store p1 t1
         let p     = maybeLookupEnv' rho1 x
             rho1' = maybeUnbindEnv rho1 x
         (rho , store2, e , t' ) <- bwdSliceM store1 (VInL p) t
         return ( rho `lub` rho1', store2, ECase e (Match (x,e1) (bot,bot))
                , TCaseL t' x t1' )
bwdSliceM store p2 (TCaseR t x t2)
    = do (rho2, store1, e2, t2') <- bwdSliceM store p2 t2
         let p     = maybeLookupEnv' rho2 x
             rho2' = maybeUnbindEnv rho2 x
         (rho , store2, e , t' ) <- bwdSliceM store1 (VInR p) t
         return ( rho `lub` rho2', store2, ECase e (Match (bot,bot) (x,e2))
                , TCaseR t' x t2')
bwdSliceM store p (TCall t1 t2 l t)
    = do (rho, store', e, t') <- bwdSliceM store p (funBody t)
         let f    = funName t
             x    = funArg  t
             k0   = Rec f x e Nothing
             p1   = lookupEnv' rho f
             p2   = lookupEnv' rho x
             rho0 = unbindEnv (unbindEnv rho f) x
         (rho2, store2, e2, t2') <- bwdSliceM store' p2 t2
         (rho1, store1, e1, t1') <-
             bwdSliceM store2 (p1 `lub` VClosure k0 rho0) t1
         return ( rho1 `lub` rho2, store1, EApp e1 e2
                , TCall t1' t2' l (Rec f x t' Nothing))
bwdSliceM store p (TCallExn t1 t2)
    = do (rho2, store2, e2, t2') <- bwdSliceM store  p t2
         (rho1, store1, e1, t1') <- bwdSliceM store2 p t1
         return (rho1 `lub` rho2, store1, EApp e1 e2, TCallExn t1' t2')
bwdSliceM store (VRoll tv p) (TRoll tv' t)
    | tv == tv'
    = do (rho, store', e, t') <- bwdSliceM store p t
         return (rho, store', ERoll tv e, TRoll tv' t')
bwdSliceM store VStar (TRoll tv' t)
    = do (rho, store', e, t') <- bwdSliceM store VStar t
         return (rho, store', ERoll tv' e, TRoll tv' t')
bwdSliceM store p (TUnroll tv t)
    = do (rho, store', e, t') <- bwdSliceM store (VRoll tv p) t
         return (rho, store', EUnroll tv e, TUnroll tv t')
bwdSliceM store v (TRef (Just l) t) | not (isException v)
    = do (rho, store', e, t') <- bwdSliceM store (storeDeref store l) t
         return (rho, storeUpdateHole store' l, ERef e, TRef (Just l) t')
bwdSliceM store v (TRef Nothing t) | isException v
    = do (rho, store', e, t') <- bwdSliceM store v t
         return (rho, store', ERef e, TRef Nothing t')
bwdSliceM store v (TDeref (Just l) t) | not (isException v)
    = do (rho, store', e, t') <- bwdSliceM store (toValue l) t
         return (rho, storeUpdate store' l v, EDeref e, TDeref (Just l) t')
bwdSliceM store v (TDeref Nothing t) | isException v
    = do (rho, store', e, t') <- bwdSliceM store v t
         return (rho, store', EDeref e, TDeref Nothing t')
bwdSliceM store _ (TAssign (Just l) _ _) | not (existsInStore store l)
    = return ( bot, store, EHole, TSlicedHole (singletonStoreLabel l) RetValue)
bwdSliceM store v (TAssign (Just l) t1 t2) | not (isException v)
    = do (rho2, store2, e2, t2') <- bwdSliceM store  (storeDeref store l) t2
         (rho1, store1, e1, t1') <- bwdSliceM store2 (toValue l) t1
         return ( rho1 `lub` rho2, storeUpdateHole store1 l, EAssign e1 e2
                , TAssign (Just l) t1' t2')
bwdSliceM store v (TAssign Nothing t1 THole) | isException v
    = do (rho1, store1, e1, t1') <- bwdSliceM store v t1
         return ( rho1, store1, EAssign e1 EHole, TAssign Nothing t1' THole)
bwdSliceM store v (TAssign (Just l) t1 t2) | isException v
    = do (rho2, store2, e2, t2') <- bwdSliceM store  v t2
         (rho1, store1, e1, t1') <- bwdSliceM store2 (toValue l) t1
         return ( rho1 `lub` rho2, store1, EAssign e1 e2
                , TAssign (Just l) t1' t2')
bwdSliceM store v (TSeq t1 t2)
    = do (rho2, store2, e2, t2') <- bwdSliceM store v t2
         (rho1, store1, e1, t1') <- bwdSliceM store2 VHole t1
         return ( rho1 `lub` rho2, store1, ESeq e1 e2, TSeq t1' t2')
bwdSliceM store v (TTry t)
    = do (rho, store', e, t') <- bwdSliceM store v t
         return (rho, store', ETryWith e bot bot, TTry t')
bwdSliceM store v (TTryWith t1 x t2)
    = do (rho2, store2, e2, t2') <- bwdSliceM store v t2
         let p1    = lookupEnv' rho2 x
             rho2' = unbindEnv  rho2 x
         (rho1, store1, e1, t1') <- bwdSliceM store2 (VException p1) t1
         return ( rho1 `lub` rho2', store1, ETryWith e1 x e2
                , TTryWith t1' x t2')
bwdSliceM _ v t = error $ "Cannot slice value " ++ show v ++
                         " from trace " ++ show t
