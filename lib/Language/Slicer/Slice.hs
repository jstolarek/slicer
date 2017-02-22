{-# LANGUAGE FunctionalDependencies  #-}
{-# LANGUAGE NamedFieldPuns          #-}
{-# LANGUAGE MultiParamTypeClasses   #-}
{-# LANGUAGE UndecidableInstances    #-}

module Language.Slicer.Slice
    ( bslice, pslice
    ) where

import           Language.Slicer.Core
import           Language.Slicer.Env
import           Language.Slicer.UpperSemiLattice

import           Control.Exception ( assert      )
import qualified Data.IntMap as M
import           Data.Maybe        ( maybeToList )

-- slicing.  Find parts of trace/input "needed" for part of output.
-- version with unevaluation in app.

-- | Get list of labels that a trace writes to
storeWrites :: Trace -> StoreLabels
-- relevant store assignments
storeWrites (TRef l t)         = maybeToList l ++ storeWrites t
storeWrites (TAssign l t1 t2)
    = maybeToList l ++ storeWrites t1 ++ storeWrites t2
-- sliced hole annotated with store labels
storeWrites (TSlicedHole ls _) = ls
storeWrites (TIfThen t1 t2)    = storeWrites t1 ++ storeWrites t2
storeWrites (TIfElse t1 t2)    = storeWrites t1 ++ storeWrites t2
storeWrites (TIfExn t)         = storeWrites t
storeWrites (TCaseL t1 _ t2)   = storeWrites t1 ++ storeWrites t2
storeWrites (TCaseR t1 _ t2)   = storeWrites t1 ++ storeWrites t2
storeWrites (TCall t1 t2 _ (Rec _ _ t3 _))
    = storeWrites t1 ++ storeWrites t2 ++ storeWrites t3
storeWrites (TCallExn t1 t2)   = storeWrites t1 ++ storeWrites t2
storeWrites (TDeref _ t)       = storeWrites t
storeWrites (TRaise t)         = storeWrites t
storeWrites (TTry t)           = storeWrites t
storeWrites (TTryWith t1 _ t2) = storeWrites t1 ++ storeWrites t2
storeWrites (TLet _ t1 t2)     = storeWrites t1 ++ storeWrites t2
storeWrites (TPair t1 t2)      = storeWrites t1 ++ storeWrites t2
storeWrites (TSeq t1 t2)       = storeWrites t1 ++ storeWrites t2
storeWrites (TOp _ ts)         = concatMap storeWrites ts
storeWrites (TFst t)           = storeWrites t
storeWrites (TSnd t)           = storeWrites t
storeWrites (TInL t)           = storeWrites t
storeWrites (TInR t)           = storeWrites t
storeWrites (TRoll _ t)        = storeWrites t
storeWrites (TUnroll _ t)      = storeWrites t
storeWrites TUnit              = []
storeWrites (TVar _)           = []
storeWrites (TBool _)          = []
storeWrites (TInt _)           = []
storeWrites (TString _)        = []
storeWrites (TFun _)           = []
storeWrites THole              = []
storeWrites (TExp e)
    = error ("Impossible happened at storeWrites: " ++ show e)

insertStoreHole :: Store -> StoreLabel -> Store
insertStoreHole = updateLabel VHole

updateLabel :: Value -> Store -> StoreLabel -> Store
updateLabel val st l =
  assert (l `M.member` st) $
  M.insert l val st

-- Trace slicing (backward slicing) as described in section 5 of the ICFP 12
-- paper
bslice :: Value -> Trace -> (Trace, Env Value)
bslice VHole _       = (bot     , bot)
bslice p (TVar x)   = (TVar x , singletonEnv x p)
bslice _ TUnit      = (TUnit  , bot)
bslice _ (TBool b)  = (TBool b, bot)
bslice _ (TInt i)   = (TInt  i, bot)
bslice (VClosure k env) (TFun _k')
    = (TFun k, env) -- assumes k <= k'
bslice  VStar (TFun k)
    = (TFun k, constEnv (fvs k) VStar)
bslice p2 (TLet x t1 t2)
    = let (t2',rho2) = bslice p2 t2
          p1         = lookupEnv' rho2 x
          rho2'      = unbindEnv rho2 x
          (t1',rho1) = bslice p1 t1
      in (TLet x t1' t2', rho1 `lub` rho2')
bslice _ (TOp f ts)
    = let (ts', rhos) = unzip (map (\t -> bslice VStar t) ts)
      in (TOp f ts', foldl lub bot rhos)
bslice (VPair p1 p2) (TPair t1 t2)
    = let (t1',rho1) = bslice p1 t1
          (t2',rho2) = bslice p2 t2
      in (TPair t1' t2', rho1 `lub` rho2)
bslice VStar (TPair t1 t2)
    = let (t1',rho1) = bslice VStar t1
          (t2',rho2) = bslice VStar t2
      in (TPair t1' t2', rho1 `lub` rho2)
bslice p (TFst t)
    = let (t',rho) = bslice (VPair p bot) t
      in (TFst t', rho)
bslice p (TSnd t)
    = let (t',rho) = bslice (VPair bot p) t
      in (TSnd t', rho)
bslice (VInL p) (TInL t)
    = let (t',rho) = bslice p t
      in (TInL t',rho)
bslice VStar (TInL t)
    = let (t',rho) = bslice VStar t
      in (TInL t',rho)
bslice (VInR p) (TInR t)
    = let (t', rho) = bslice p t
      in (TInR t', rho)
bslice VStar (TInR t)
    = let (t', rho) = bslice VStar t
      in (TInR t', rho)
bslice p1 (TIfThen t t1)
    = let (t1',rho1) = bslice p1 t1
          (t',rho)   = bslice VStar t
      in (TIfThen t' t1', rho `lub` rho1)
bslice p2 (TIfElse t t2)
    = let (t2',rho2) = bslice p2 t2
          (t',rho)   = bslice VStar t
      in (TIfElse t' t2', rho `lub` rho2)
bslice p1 (TCaseL t x t1)
    = let (t1',rho1) = bslice p1 t1
          p          = maybeLookupEnv' rho1 x
          rho1'      = maybeUnbindEnv rho1 x
          (t',rho)   = bslice (VInL p) t
      in (TCaseL t' x t1', rho `lub` rho1')
bslice p2 (TCaseR t x t2)
    = let (t2',rho2) = bslice p2 t2
          p          = maybeLookupEnv' rho2 x
          rho2'      = maybeUnbindEnv rho2 x
          (t',rho)   = bslice (VInR p) t
      in (TCaseR t' x t2', rho `lub` rho2')
bslice p (TCall t1 t2 k t)
    = let (t',rho)    = bslice p (funBody t)
          f           = funName t
          x           = funArg  t
          e'          = uneval t'
          k0          = Rec f x e' Nothing
          p1          = lookupEnv' rho f
          p2          = lookupEnv' rho x
          rho0        = unbindEnv (unbindEnv rho f) x
          (t1', rho1) = bslice (p1 `lub` VClosure k0 rho0) t1
          (t2', rho2) = bslice p2 t2
      in (TCall t1' t2' k (Rec f x t' Nothing), rho1 `lub` rho2)
bslice (VRoll tv p) (TRoll tv' t)
    | tv == tv'
    = let (t',rho) = bslice p t
      in (TRoll tv' t', rho)
bslice VStar (TRoll tv t)
    = let (t',rho) = bslice VStar t
      in (TRoll tv t', rho)
bslice p (TUnroll tv t)
    = let (t',rho) = bslice (VRoll tv p) t
      in (TUnroll tv t', rho)
bslice _ x = error $ show x


-- Unevaluation (program slicing) as described in Section 4.3 of the ICFP'12
-- paper
pslice :: Store -> Value -> Trace -> (Env Value, Store, Exp, Trace)
pslice store VHole (TRaise t)
    = let (rho, store', e, t') = pslice store VStar t
      in (rho, store', ERaise e, TRaise t')
pslice store (VException VHole) trace
    = (bot,  store, bot, TSlicedHole (storeWrites trace) RetRaise)
pslice store VHole trace
    = (bot,  store, bot, TSlicedHole (storeWrites trace) RetValue)
pslice store (VException _) THole -- JSTOLAREK: speculative equation
    = (bot, store, EHole, THole)
pslice store VStar THole -- JSTOLAREK: another speculative equation
    = (bot, store, EHole, THole)
pslice store (VException v) (TRaise t)
    = let (rho, store', e, t') = pslice store v t
      in (rho, store', ERaise e, TRaise t')
pslice store VStar (TRaise t)
    = let (rho, store', e, t') = pslice store VStar t
      in (rho, store', ERaise e, TRaise t')
pslice store v (TVar x)
    = (singletonEnv x v, store, EVar x, TVar x)
pslice store VUnit TUnit
    = (bot, store, EUnit, TUnit)
pslice store VStar TUnit
    = (bot, store, EUnit, TUnit)
pslice store (VBool b) (TBool b') | b == b'
    = (bot, store, EBool b, TBool b)
pslice store VStar (TBool b)
    = (bot, store, EBool b, TBool b)
pslice store (VInt i) (TInt i') | i == i'
    = (bot, store, EInt i, TInt i)
pslice store VStar (TInt i)
    = (bot, store, EInt i, TInt i)
pslice store (VString s) (TString s') | s == s'
    = (bot, store, EString s, TString s)
pslice store VStar (TString s)
    = (bot, store, EString s, TString s)
pslice store (VClosure k env) (TFun k') | k `leq` k'
    = (env, store, EFun k, TFun k')
pslice store VStar (TFun k)
    = (constEnv (fvs k) VStar, store, EFun k, TFun k)
pslice store (VPair p1 p2) (TPair t1 t2)
    = let (rho2, store2, e2, t2') = pslice store  p2 t2
          (rho1, store1, e1, t1') = pslice store2 p1 t1
      in (rho1 `lub` rho2, store1, EPair e1 e2, TPair t1' t2')
pslice store VStar (TPair t1 t2)
    = let (rho2, store2, e2, t2') = pslice store  VStar t2
          (rho1, store1, e1, t1') = pslice store2 VStar t1
      in (rho1 `lub` rho2, store1, EPair e1 e2, TPair t1' t2')
pslice store p (TFst t)
    = let (rho, store', e', t') = pslice store (VPair p bot) t
      in (rho, store', EFst e', TFst t')
pslice store p (TSnd t)
    = let (rho, store', e', t') = pslice store (VPair bot p) t
      in (rho, store', ESnd e', TSnd t')
pslice store (VInL p) (TInL t)
    = let (rho, store', e', t') = pslice store p t
      in (rho, store', EInL e', TInL t')
pslice store VStar (TInL t)
    = let (rho, store', e', t') = pslice store VStar t
      in (rho, store', EInL e', TInL t')
pslice store (VInR p) (TInR t)
    = let (rho, store', e', t') = pslice store p t
      in (rho, store', EInR e', TInR t')
pslice store VStar (TInR t)
    = let (rho, store', e', t') = pslice store VStar t
      in (rho, store', EInR e', TInR t')
-- JSTOLAREK: This case should be redundant
pslice store p (TLet x t THole)
    = let (rho1, store', e1, t1') = pslice store p t
      in  (rho1, store', ELet x e1 EHole, TLet x t1' THole)
pslice store p2 (TLet x t1 t2)
    = let (rho2, store2, e2, t2') = pslice store p2 t2
          p1                      = lookupEnv' rho2 x
          rho2'                   = unbindEnv  rho2 x
          (rho1, store1, e1, t1') = pslice store2 p1 t1
      in (rho1 `lub` rho2', store1, ELet x e1 e2, TLet x t1' t2')
pslice store _ (TOp f ts)
    = let (rhoA, storeA, esA, tsA) = foldr (\t' (rho', store', es', ts') ->
                    let (rho'', store'', e, t) = pslice store' VStar t'
                    in (rho' `lub` rho'', store'', e:es', t:ts'))
                  (bot, store, [], []) ts
      in (rhoA, storeA, EOp f esA, TOp f tsA)
pslice store p1 (TIfThen t t1)
    = let (rho1, store1, e1, t1') = pslice store p1 t1
          (rho , store2, e , t' ) = pslice store1 VStar t
      in (rho `lub` rho1, store2, EIf e e1 EHole, TIfThen t' t1')
pslice store p2 (TIfElse t t2)
    = let (rho2, store1, e2, t2') = pslice store p2 t2
          (rho , store2, e , t' ) = pslice store1 VStar t
      in (rho `lub` rho2, store2, EIf e EHole e2, TIfElse t' t2')
pslice store p (TIfExn t)
    = let (rho, store', e, t') = pslice store p t
      in (rho, store', EIf e EHole EHole, TIfExn t')
pslice store p1 (TCaseL t x t1)
    = let (rho1, store1, e1, t1') = pslice store p1 t1
          p                       = maybeLookupEnv' rho1 x
          rho1'                   = maybeUnbindEnv rho1 x
          (rho , store2, e , t' ) = pslice store1 (VInL p) t
      in ( rho `lub` rho1', store2, ECase e (Match (x,e1) (bot,bot))
         , TCaseL t' x t1' )
pslice store p2 (TCaseR t x t2)
    = let (rho2, store1, e2, t2') = pslice store p2 t2
          p                       = maybeLookupEnv' rho2 x
          rho2'                   = maybeUnbindEnv rho2 x
          (rho , store2, e , t' ) = pslice store1 (VInR p) t
      in ( rho `lub` rho2', store2, ECase e (Match (bot,bot) (x,e2))
         , TCaseR t' x t2')
pslice store p (TCall t1 t2 l t)
    = let (rho, store', e, t')    = pslice store p (funBody t)
          f                       = funName t
          x                       = funArg  t
          k0                      = Rec f x e Nothing
          p1                      = lookupEnv' rho f
          p2                      = lookupEnv' rho x
          rho0                    = unbindEnv (unbindEnv rho f) x
          (rho2, store2, e2, t2') = pslice store' p2 t2
          (rho1, store1, e1, t1') = pslice store2 (p1 `lub` VClosure k0 rho0) t1
      in ( rho1 `lub` rho2, store1, EApp e1 e2
         , TCall t1' t2' l (Rec f x t' Nothing))
pslice store p (TCallExn t1 t2)
    = let (rho2, store2, e2, t2') = pslice store  p t2
          (rho1, store1, e1, t1') = pslice store2 p t1
      in (rho1 `lub` rho2, store1, EApp e1 e2, TCallExn t1' t2')
pslice store (VRoll tv p) (TRoll tv' t)
    | tv == tv'
    = let (rho, store', e, t') = pslice store p t
      in (rho, store', ERoll tv e, TRoll tv' t')
pslice store VStar (TRoll tv' t)
    = let (rho, store', e, t') = pslice store VStar t
      in (rho, store', ERoll tv' e, TRoll tv' t')
pslice store p (TUnroll tv t)
    = let (rho, store', e, t') = pslice store (VRoll tv p) t
      in (rho, store', EUnroll tv e, TUnroll tv t')
pslice store v (TRef (Just l) t) | not (isException v)
    = let (rho, store', e, t') = pslice store (deref store l) t
      in (rho, insertStoreHole store' l, ERef e, TRef (Just l) t')
pslice store v (TRef Nothing t) | isException v
    = let (rho, store', e, t') = pslice store v t
      in (rho, store', ERef e, TRef Nothing t')
pslice store v (TDeref (Just l) t) | not (isException v)
    = let (rho, store', e, t') = pslice store (VStoreLoc l) t
      in (rho, storeInsert store' l v, EDeref e, TDeref (Just l) t')
pslice store v (TDeref Nothing t) | isException v
    = let (rho, store', e, t') = pslice store v t
      in (rho, store', EDeref e, TDeref Nothing t')
pslice store _ (TAssign (Just l) _ _) | not (existsInStore store l)
    = ( bot, store, EHole, TSlicedHole [l] RetValue)
pslice store v (TAssign (Just l) t1 t2) | not (isException v)
    = let (rho2, store2, e2, t2') = pslice store  (deref store l) t2
          (rho1, store1, e1, t1') = pslice store2 (VStoreLoc l) t1
      in ( rho1 `lub` rho2, insertStoreHole store1 l, EAssign e1 e2
         , TAssign (Just l) t1' t2')
pslice store v (TAssign Nothing t1 THole) | isException v
    = let (rho1, store1, e1, t1') = pslice store v t1
      in ( rho1, store1, EAssign e1 EHole, TAssign Nothing t1' THole)
pslice store v (TAssign (Just l) t1 t2) | isException v
    = let (rho2, store2, e2, t2') = pslice store  v t2
          (rho1, store1, e1, t1') = pslice store2 (VStoreLoc l) t1
      in ( rho1 `lub` rho2, store1, EAssign e1 e2, TAssign (Just l) t1' t2')
pslice store v (TSeq t1 t2)
    = let (rho2, store2, e2, t2') = pslice store v t2
          (rho1, store1, e1, t1') = pslice store2 VHole t1
      in ( rho1 `lub` rho2, store1, ESeq e1 e2, TSeq t1' t2')
pslice store v (TTry t)
    = let (rho, store', e, t') = pslice store v t
      in (rho, store', ETryWith e bot bot, TTry t')
pslice store v (TTryWith t1 x t2)
    = let (rho2, store2, e2, t2') = pslice store v t2
          p1                      = lookupEnv' rho2 x
          rho2'                   = unbindEnv  rho2 x
          (rho1, store1, e1, t1') = pslice store2 (VException p1) t1
      in ( rho1 `lub` rho2', store1, ETryWith e1 x e2, TTryWith t1' x t2')
pslice _ v t = error $ "Cannot slice value " ++ show v ++
                       " from trace " ++ show t
