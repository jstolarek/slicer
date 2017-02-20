{-# LANGUAGE FunctionalDependencies  #-}
{-# LANGUAGE NamedFieldPuns          #-}
{-# LANGUAGE MultiParamTypeClasses   #-}
{-# LANGUAGE UndecidableInstances    #-}

module Language.Slicer.Slice
    ( bslice, pslice
    ) where

import           Language.Slicer.Core
import           Language.Slicer.Env
import           Language.Slicer.Monad.Eval
import           Language.Slicer.UpperSemiLattice

import           Control.Exception ( assert      )
import qualified Data.IntMap as M
import           Data.Maybe        ( maybeToList )

-- slicing.  Find parts of trace/input "needed" for part of output.
-- version with unevaluation in app.

-- | Get list of labels that a trace writes to
storeWrites :: Trace -> [ StoreLabel ]
-- relevant store assignments
storeWrites (TRef l t)         = maybeToList l ++ storeWrites t
storeWrites (TAssign l t1 t2)
    = maybeToList l ++ storeWrites t1 ++ storeWrites t2
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

insertStoreHole :: EvalState -> StoreLabel -> EvalState
insertStoreHole = updateLabel VHole

updateLabel :: Value -> EvalState -> StoreLabel -> EvalState
updateLabel val st@(EvalState { refs }) l =
  assert (l `M.member` refs) $
  st { refs = M.insert l val refs }

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

-- JSTOLAREK TODO:
--  * add Store argument
--  * swap return order of arguments
--  * add return store argument
--  * returns trace as well - this makes bslice obsolete
pslice :: Store -> Value -> Trace -> (Exp, Env Value)
pslice _ VHole _      = (bot    , bot)
pslice _ p (TVar x )  = (EVar x , singletonEnv x p)
pslice _ _ TUnit      = (EUnit  , bot)
pslice _ _ (TBool b)  = (EBool b, bot)
pslice _ _ (TInt i)   = (EInt i , bot)
pslice _ (VClosure k env) (TFun _k')
    = (EFun k, env) -- assumes k <= k'
pslice _ VStar (TFun k)
    = (EFun k, constEnv (fvs k) VStar)
pslice _ p2 (TLet x t1 t2)
    = let (t2',rho2) = pslice undefined p2 t2
          p1         = lookupEnv' rho2 x
          rho2'      = unbindEnv rho2 x
          (t1',rho1) = pslice undefined p1 t1
      in (ELet x t1' t2', rho1 `lub` rho2')
pslice _ _ (TOp f ts)
    = let (ts', rhos) = unzip (map (\t -> pslice undefined VStar t) ts)
      in (EOp f ts', foldl lub bot rhos)
pslice _ (VPair p1 p2) (TPair t1 t2)
    = let (t1',rho1) = pslice undefined p1 t1
          (t2',rho2) = pslice undefined p2 t2
      in (EPair t1' t2', rho1 `lub` rho2)
pslice _ VStar (TPair t1 t2)
    = let (t1',rho1) = pslice undefined VStar t1
          (t2',rho2) = pslice undefined VStar t2
      in (EPair t1' t2', rho1 `lub` rho2)
pslice _ p (TFst t)
    = let (t',rho) = pslice undefined (VPair p bot) t
      in (EFst t', rho)
pslice _ p (TSnd t)
    = let (t',rho) = pslice undefined (VPair bot p) t
      in (ESnd t', rho)
pslice _ (VInL p) (TInL t)
    = let (t',rho) = pslice undefined p t
      in (EInL t',rho)
pslice _ VStar (TInL t)
    = let (t',rho) = pslice undefined VStar t
      in (EInL t',rho)
pslice _ (VInR p) (TInR t)
    = let (t', rho) = pslice undefined p t
      in (EInR t', rho)
pslice _ VStar (TInR t)
    = let (t', rho) = pslice undefined VStar t
      in (EInR t', rho)
pslice _ p1 (TIfThen t t1)
    = let (e1, rho1) = pslice undefined p1 t1
          (e, rho)   = pslice undefined VStar t
      in (EIf e e1 EHole, rho `lub` rho1)
pslice _ p2 (TIfElse t t2)
    = let (e2, rho2) = pslice undefined p2 t2
          (e, rho)   = pslice undefined VStar t
      in (EIf e EHole e2, rho `lub` rho2)
pslice _ p1 (TCaseL t x t1)
    = let (e1, rho1) = pslice undefined p1 t1
          p          = maybeLookupEnv' rho1 x
          rho1'      = maybeUnbindEnv rho1 x
          (e, rho)   = pslice undefined (VInL p) t
      in (ECase e (Match (x,e1) (bot,bot)), rho `lub` rho1')
pslice _ p2 (TCaseR t x t2)
    = let (e2, rho2) = pslice undefined p2 t2
          p          = maybeLookupEnv' rho2 x
          rho2'      = maybeUnbindEnv rho2 x
          (e, rho)   = pslice undefined (VInR p) t
      in (ECase e (Match (bot,bot) (x,e2)), rho `lub` rho2')
pslice _ p (TCall t1 t2 _ t)
    = let (e, rho)   = pslice undefined p (funBody t)
          f          = funName t
          x          = funArg  t
          k0         = Rec f x e Nothing
          p1         = lookupEnv' rho f
          p2         = lookupEnv' rho x
          rho0       = unbindEnv (unbindEnv rho f) x
          (e1, rho1) = pslice undefined (p1 `lub` VClosure k0 rho0) t1
          (e2, rho2) = pslice undefined p2 t2
      in (EApp e1 e2, rho1 `lub` rho2)
pslice _ (VRoll tv p) (TRoll tv' t)
    | tv == tv'
    = let (t',rho) = pslice undefined p t
      in (ERoll tv' t', rho)
pslice _ VStar (TRoll tv' t)
    = let (t',rho) = pslice undefined VStar t
      in (ERoll tv' t', rho)
pslice _ p (TUnroll tv t)
    = let (t',rho) = pslice undefined (VRoll tv p) t
      in (EUnroll tv t', rho)
pslice _ v t = error $ "Cannot unevaluate value " ++ show v ++
                       " from trace " ++ show t
