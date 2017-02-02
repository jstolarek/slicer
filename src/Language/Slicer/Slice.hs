{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies,
  UndecidableInstances #-}

module Language.Slicer.Slice
    ( bslice, pslice, uneval
    ) where

import           Language.Slicer.Core
import           Language.Slicer.Env
import           Language.Slicer.UpperSemiLattice

-- slicing.  Find parts of trace/input "needed" for part of output.
-- version with unevaluation in app.

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
bslice p1 (IfThen t e1 e2 t1)
    = let (t1',rho1) = bslice p1 t1
          (t',rho)   = bslice VStar t
      in (IfThen t' e1 e2 t1', rho `lub` rho1)
bslice p2 (IfElse t e1 e2 t2)
    = let (t2',rho2) = bslice p2 t2
          (t',rho)   = bslice VStar t
      in (IfElse t' e1 e2 t2', rho `lub` rho2)
bslice p1 (CaseL t x t1)
    = let (t1',rho1) = bslice p1 t1
          p          = lookupEnv' rho1 x
          rho1'      = unbindEnv rho1 x
          (t',rho)   = bslice (VInL p) t
      in (CaseL t' x t1', rho `lub` rho1')
bslice p2 (CaseR t x t2)
    = let (t2',rho2) = bslice p2 t2
          p          = lookupEnv' rho2 x
          rho2'      = unbindEnv rho2 x
          (t',rho)   = bslice (VInR p) t
      in (CaseR t' x t2', rho `lub` rho2')
bslice p (Call t1 t2 k t)
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
      in (Call t1' t2' k (Rec f x t' Nothing), rho1 `lub` rho2)
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
pslice :: Value -> Trace -> (Exp, Env Value)
pslice VHole _      = (bot    , bot)
pslice p (TVar x )  = (EVar x  , singletonEnv x p)
pslice _ TUnit      = (EUnit   , bot)
pslice _ (TBool b)  = (EBool b, bot)
pslice _ (TInt i)   = (EInt i , bot)
pslice (VClosure k env) (TFun _k')
    = (EFun k, env) -- assumes k <= k'
pslice VStar (TFun k)
    = (EFun k, constEnv (fvs k) VStar)
pslice p2 (TLet x t1 t2)
    = let (t2',rho2) = pslice p2 t2
          p1         = lookupEnv' rho2 x
          rho2'      = unbindEnv rho2 x
          (t1',rho1) = pslice p1 t1
      in (ELet x t1' t2', rho1 `lub` rho2')
pslice _ (TOp f ts)
    = let (ts', rhos) = unzip (map (\t -> pslice VStar t) ts)
      in (EOp f ts', foldl lub bot rhos)
pslice (VPair p1 p2) (TPair t1 t2)
    = let (t1',rho1) = pslice p1 t1
          (t2',rho2) = pslice p2 t2
      in (EPair t1' t2', rho1 `lub` rho2)
pslice VStar (TPair t1 t2)
    = let (t1',rho1) = pslice VStar t1
          (t2',rho2) = pslice VStar t2
      in (EPair t1' t2', rho1 `lub` rho2)
pslice p (TFst t)
    = let (t',rho) = pslice (VPair p bot) t
      in (EFst t', rho)
pslice p (TSnd t)
    = let (t',rho) = pslice (VPair bot p) t
      in (ESnd t', rho)
pslice (VInL p) (TInL t)
    = let (t',rho) = pslice p t
      in (EInL t',rho)
pslice VStar (TInL t)
    = let (t',rho) = pslice VStar t
      in (EInL t',rho)
pslice (VInR p) (TInR t)
    = let (t', rho) = pslice p t
      in (EInR t', rho)
pslice VStar (TInR t)
    = let (t', rho) = pslice VStar t
      in (EInR t', rho)
pslice p1 (IfThen t _ _ t1)
    = let (e1, rho1) = pslice p1 t1
          (e, rho)   = pslice VStar t
      in (If e e1 EHole, rho `lub` rho1)
pslice p2 (IfElse t _ _ t2)
    = let (e2, rho2) = pslice p2 t2
          (e, rho)   = pslice VStar t
      in (If e EHole e2, rho `lub` rho2)
pslice p1 (CaseL t x t1)
    = let (e1, rho1) = pslice p1 t1
          p          = lookupEnv' rho1 x
          rho1'      = unbindEnv rho1 x
          (e, rho)   = pslice (VInL p) t
      in (Case e (Match (x,e1) (bot,bot)), rho `lub` rho1')
pslice p2 (CaseR t x t2)
    = let (e2, rho2) = pslice p2 t2
          p          = lookupEnv' rho2 x
          rho2'      = unbindEnv rho2 x
          (e, rho)   = pslice (VInR p) t
      in (Case e (Match (bot,bot) (x,e2)), rho `lub` rho2')
pslice p (Call t1 t2 _ t)
    = let (e, rho)   = pslice p (funBody t)
          f          = funName t
          x          = funArg  t
          k0         = Rec f x e Nothing
          p1         = lookupEnv' rho f
          p2         = lookupEnv' rho x
          rho0       = unbindEnv (unbindEnv rho f) x
          (e1, rho1) = pslice (p1 `lub` VClosure k0 rho0) t1
          (e2, rho2) = pslice p2 t2
      in (App e1 e2, rho1 `lub` rho2)
pslice (VRoll tv p) (TRoll tv' t)
    | tv == tv'
    = let (t',rho) = pslice p t
      in (ERoll tv' t', rho)
pslice VStar (TRoll tv' t)
    = let (t',rho) = pslice VStar t
      in (ERoll tv' t', rho)
pslice p (TUnroll tv t)
    = let (t',rho) = pslice (VRoll tv p) t
      in (EUnroll tv t', rho)
pslice v t = error $ "Cannot unevaluate value " ++ show v ++
                     " from trace " ++ show t

-- unevaluation.  Squash trace back down into expression.
class Uneval a b | a -> b where
    uneval :: a -> b

instance Uneval Trace Exp where
    uneval (CaseL t x t1)    = Case (uneval t) (Match (x, uneval t1) (bot, EHole))
    uneval (CaseR t x t2)    = Case (uneval t) (Match (bot, EHole) (x, uneval t2))
    uneval (IfThen t _ _ t1) = If (uneval t) (uneval t1) EHole
    uneval (IfElse t _ _ t2) = If (uneval t) EHole (uneval t2)
    uneval (Call t1 t2 _ _)  = App (uneval t1) (uneval t2)
    uneval (TExp expr)       = Exp (uneval expr)

instance Uneval a b => Uneval (Syntax a) (Syntax b) where
    uneval (Var x)       = Var x
    uneval Unit          = Unit
    uneval Hole          = Hole
    uneval (CBool b)     = CBool b
    uneval (CInt i)      = CInt i
    uneval (CString s)   = CString s
    uneval (Fun k)       = Fun k
    uneval (Let x e1 e2) = Let x (uneval e1) (uneval e2)
    uneval (Op f es)     = Op f (map uneval es)
    uneval (Pair e1 e2)  = Pair (uneval e1) (uneval e2)
    uneval (Fst e)       = Fst (uneval e)
    uneval (Snd e)       = Snd (uneval e)
    uneval (InL e)       = InL (uneval e)
    uneval (InR e)       = InR (uneval e)
    uneval (Roll tv e)   = Roll tv (uneval e)
    uneval (Unroll tv e) = Unroll tv (uneval e)

instance Uneval a b => Uneval (Code a) (Code b) where
    uneval (Rec name arg body label) = Rec name arg (uneval body) label

