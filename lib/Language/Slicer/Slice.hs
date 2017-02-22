{-# LANGUAGE FunctionalDependencies  #-}
{-# LANGUAGE NamedFieldPuns          #-}
{-# LANGUAGE MultiParamTypeClasses   #-}
{-# LANGUAGE UndecidableInstances    #-}

module Language.Slicer.Slice
    ( bslice, bwdSlice
    ) where

import           Language.Slicer.Core
import           Language.Slicer.Env
import           Language.Slicer.UpperSemiLattice

-- Trace slicing (backward slicing) as described in section 5 of the ICFP 12
-- paper
bslice :: Store -> Value -> Trace -> (Trace, Env Value)
bslice store value trace =
    let (env, _, _, trace') = bwdSlice store value trace
    in (trace', env)

-- Unevaluation (program slicing) as described in Section 4.3 of the ICFP'12
-- paper
bwdSlice :: Store -> Value -> Trace -> (Env Value, Store, Exp, Trace)
bwdSlice store VHole (TRaise t)
    = let (rho, store', e, t') = bwdSlice store VStar t
      in (rho, store', ERaise e, TRaise t')
bwdSlice store (VException VHole) trace | allStoreHoles store (storeWrites trace)
    = (bot,  store, bot, TSlicedHole (storeWrites trace) RetRaise)
bwdSlice store VHole trace | allStoreHoles store (storeWrites trace)
    = (bot,  store, bot, TSlicedHole (storeWrites trace) RetValue)
bwdSlice store (VException _) THole -- JSTOLAREK: speculative equation
    = (bot, store, EHole, THole)
bwdSlice store VStar THole -- JSTOLAREK: another speculative equation
    = (bot, store, EHole, THole)
bwdSlice store (VException v) (TRaise t)
    = let (rho, store', e, t') = bwdSlice store v t
      in (rho, store', ERaise e, TRaise t')
bwdSlice store VStar (TRaise t)
    = let (rho, store', e, t') = bwdSlice store VStar t
      in (rho, store', ERaise e, TRaise t')
bwdSlice store v (TVar x)
    = (singletonEnv x v, store, EVar x, TVar x)
bwdSlice store VUnit TUnit
    = (bot, store, EUnit, TUnit)
bwdSlice store VStar TUnit
    = (bot, store, EUnit, TUnit)
bwdSlice store (VBool b) (TBool b') | b == b'
    = (bot, store, EBool b, TBool b)
bwdSlice store VStar (TBool b)
    = (bot, store, EBool b, TBool b)
bwdSlice store (VInt i) (TInt i') | i == i'
    = (bot, store, EInt i, TInt i)
bwdSlice store VStar (TInt i)
    = (bot, store, EInt i, TInt i)
bwdSlice store (VString s) (TString s') | s == s'
    = (bot, store, EString s, TString s)
bwdSlice store VStar (TString s)
    = (bot, store, EString s, TString s)
bwdSlice store (VClosure k env) (TFun k') | k `leq` k'
    = (env, store, EFun k, TFun k')
bwdSlice store VStar (TFun k)
    = (constEnv (fvs k) VStar, store, EFun k, TFun k)
bwdSlice store (VPair p1 p2) (TPair t1 t2)
    = let (rho2, store2, e2, t2') = bwdSlice store  p2 t2
          (rho1, store1, e1, t1') = bwdSlice store2 p1 t1
      in (rho1 `lub` rho2, store1, EPair e1 e2, TPair t1' t2')
bwdSlice store VStar (TPair t1 t2)
    = let (rho2, store2, e2, t2') = bwdSlice store  VStar t2
          (rho1, store1, e1, t1') = bwdSlice store2 VStar t1
      in (rho1 `lub` rho2, store1, EPair e1 e2, TPair t1' t2')
bwdSlice store p (TFst t)
    = let (rho, store', e', t') = bwdSlice store (VPair p bot) t
      in (rho, store', EFst e', TFst t')
bwdSlice store p (TSnd t)
    = let (rho, store', e', t') = bwdSlice store (VPair bot p) t
      in (rho, store', ESnd e', TSnd t')
bwdSlice store (VInL p) (TInL t)
    = let (rho, store', e', t') = bwdSlice store p t
      in (rho, store', EInL e', TInL t')
bwdSlice store VStar (TInL t)
    = let (rho, store', e', t') = bwdSlice store VStar t
      in (rho, store', EInL e', TInL t')
bwdSlice store (VInR p) (TInR t)
    = let (rho, store', e', t') = bwdSlice store p t
      in (rho, store', EInR e', TInR t')
bwdSlice store VStar (TInR t)
    = let (rho, store', e', t') = bwdSlice store VStar t
      in (rho, store', EInR e', TInR t')
-- JSTOLAREK: This case should be redundant
bwdSlice store p (TLet x t THole)
    = let (rho1, store', e1, t1') = bwdSlice store p t
      in  (rho1, store', ELet x e1 EHole, TLet x t1' THole)
bwdSlice store p2 (TLet x t1 t2)
    = let (rho2, store2, e2, t2') = bwdSlice store p2 t2
          p1                      = lookupEnv' rho2 x
          rho2'                   = unbindEnv  rho2 x
          (rho1, store1, e1, t1') = bwdSlice store2 p1 t1
      in (rho1 `lub` rho2', store1, ELet x e1 e2, TLet x t1' t2')
bwdSlice store _ (TOp f ts)
    = let (rhoA, storeA, esA, tsA) = foldr (\t' (rho', store', es', ts') ->
                    let (rho'', store'', e, t) = bwdSlice store' VStar t'
                    in (rho' `lub` rho'', store'', e:es', t:ts'))
                  (bot, store, [], []) ts
      in (rhoA, storeA, EOp f esA, TOp f tsA)
bwdSlice store p1 (TIfThen t t1)
    = let (rho1, store1, e1, t1') = bwdSlice store p1 t1
          (rho , store2, e , t' ) = bwdSlice store1 VStar t
      in (rho `lub` rho1, store2, EIf e e1 EHole, TIfThen t' t1')
bwdSlice store p2 (TIfElse t t2)
    = let (rho2, store1, e2, t2') = bwdSlice store p2 t2
          (rho , store2, e , t' ) = bwdSlice store1 VStar t
      in (rho `lub` rho2, store2, EIf e EHole e2, TIfElse t' t2')
bwdSlice store p (TIfExn t)
    = let (rho, store', e, t') = bwdSlice store p t
      in (rho, store', EIf e EHole EHole, TIfExn t')
bwdSlice store p1 (TCaseL t x t1)
    = let (rho1, store1, e1, t1') = bwdSlice store p1 t1
          p                       = maybeLookupEnv' rho1 x
          rho1'                   = maybeUnbindEnv rho1 x
          (rho , store2, e , t' ) = bwdSlice store1 (VInL p) t
      in ( rho `lub` rho1', store2, ECase e (Match (x,e1) (bot,bot))
         , TCaseL t' x t1' )
bwdSlice store p2 (TCaseR t x t2)
    = let (rho2, store1, e2, t2') = bwdSlice store p2 t2
          p                       = maybeLookupEnv' rho2 x
          rho2'                   = maybeUnbindEnv rho2 x
          (rho , store2, e , t' ) = bwdSlice store1 (VInR p) t
      in ( rho `lub` rho2', store2, ECase e (Match (bot,bot) (x,e2))
         , TCaseR t' x t2')
bwdSlice store p (TCall t1 t2 l t)
    = let (rho, store', e, t')    = bwdSlice store p (funBody t)
          f                       = funName t
          x                       = funArg  t
          k0                      = Rec f x e Nothing
          p1                      = lookupEnv' rho f
          p2                      = lookupEnv' rho x
          rho0                    = unbindEnv (unbindEnv rho f) x
          (rho2, store2, e2, t2') = bwdSlice store' p2 t2
          (rho1, store1, e1, t1') = bwdSlice store2 (p1 `lub` VClosure k0 rho0) t1
      in ( rho1 `lub` rho2, store1, EApp e1 e2
         , TCall t1' t2' l (Rec f x t' Nothing))
bwdSlice store p (TCallExn t1 t2)
    = let (rho2, store2, e2, t2') = bwdSlice store  p t2
          (rho1, store1, e1, t1') = bwdSlice store2 p t1
      in (rho1 `lub` rho2, store1, EApp e1 e2, TCallExn t1' t2')
bwdSlice store (VRoll tv p) (TRoll tv' t)
    | tv == tv'
    = let (rho, store', e, t') = bwdSlice store p t
      in (rho, store', ERoll tv e, TRoll tv' t')
bwdSlice store VStar (TRoll tv' t)
    = let (rho, store', e, t') = bwdSlice store VStar t
      in (rho, store', ERoll tv' e, TRoll tv' t')
bwdSlice store p (TUnroll tv t)
    = let (rho, store', e, t') = bwdSlice store (VRoll tv p) t
      in (rho, store', EUnroll tv e, TUnroll tv t')
bwdSlice store v (TRef (Just l) t) | not (isException v)
    = let (rho, store', e, t') = bwdSlice store (storeDeref store l) t
      in (rho, storeUpdateHole store' l, ERef e, TRef (Just l) t')
bwdSlice store v (TRef Nothing t) | isException v
    = let (rho, store', e, t') = bwdSlice store v t
      in (rho, store', ERef e, TRef Nothing t')
bwdSlice store v (TDeref (Just l) t) | not (isException v)
    = let (rho, store', e, t') = bwdSlice store (toValue l) t
      in (rho, storeUpdate store' l v, EDeref e, TDeref (Just l) t')
bwdSlice store v (TDeref Nothing t) | isException v
    = let (rho, store', e, t') = bwdSlice store v t
      in (rho, store', EDeref e, TDeref Nothing t')
bwdSlice store _ (TAssign (Just l) _ _) | not (existsInStore store l)
    = ( bot, store, EHole, TSlicedHole (singletonStoreLabel l) RetValue)
bwdSlice store v (TAssign (Just l) t1 t2) | not (isException v)
    = let (rho2, store2, e2, t2') = bwdSlice store  (storeDeref store l) t2
          (rho1, store1, e1, t1') = bwdSlice store2 (toValue l) t1
      in ( rho1 `lub` rho2, storeUpdateHole store1 l, EAssign e1 e2
         , TAssign (Just l) t1' t2')
bwdSlice store v (TAssign Nothing t1 THole) | isException v
    = let (rho1, store1, e1, t1') = bwdSlice store v t1
      in ( rho1, store1, EAssign e1 EHole, TAssign Nothing t1' THole)
bwdSlice store v (TAssign (Just l) t1 t2) | isException v
    = let (rho2, store2, e2, t2') = bwdSlice store  v t2
          (rho1, store1, e1, t1') = bwdSlice store2 (toValue l) t1
      in ( rho1 `lub` rho2, store1, EAssign e1 e2, TAssign (Just l) t1' t2')
bwdSlice store v (TSeq t1 t2)
    = let (rho2, store2, e2, t2') = bwdSlice store v t2
          (rho1, store1, e1, t1') = bwdSlice store2 VHole t1
      in ( rho1 `lub` rho2, store1, ESeq e1 e2, TSeq t1' t2')
bwdSlice store v (TTry t)
    = let (rho, store', e, t') = bwdSlice store v t
      in (rho, store', ETryWith e bot bot, TTry t')
bwdSlice store v (TTryWith t1 x t2)
    = let (rho2, store2, e2, t2') = bwdSlice store v t2
          p1                      = lookupEnv' rho2 x
          rho2'                   = unbindEnv  rho2 x
          (rho1, store1, e1, t1') = bwdSlice store2 (VException p1) t1
      in ( rho1 `lub` rho2', store1, ETryWith e1 x e2, TTryWith t1' x t2')
bwdSlice _ v t = error $ "Cannot slice value " ++ show v ++
                         " from trace " ++ show t
