module Slice
    ( bslice, pslice
    ) where

import           Trace
import           Env
import           UpperSemiLattice

-- slicing.  Find parts of trace/input "needed" for part of output.
-- version with unevaluation in app.

-- Unevaluation as described in Section 4.3 of the ICFP'12 paper
bslice :: Value -> Trace -> (Trace, Env Value)
bslice VHole _     = (bot    , bot)
bslice p (Var x)   = (Var x  , singletonEnv x p)
bslice _ Unit      = (Unit   , bot)
bslice _ (CBool b) = (CBool b, bot)
bslice _ (CInt i)  = (CInt i , bot)
bslice (VClosure k env) (Fun _k')
    = (Fun k, env) -- assumes k <= k'
bslice  VStar (Fun k)
    = (Fun k, constEnv (fvs k) VStar)
bslice p2 (Let x t1 t2)
    = let (t2',rho2) = bslice p2 t2
          p1         = lookupEnv' rho2 x
          rho2'      = unbindEnv rho2 x
          (t1',rho1) = bslice p1 t1
      in (Let x t1' t2', rho1 `lub` rho2')
bslice _ (Op f ts)
    = let (ts', rhos) = unzip (map (\t -> bslice VStar t) ts)
      in (Op f ts', foldl lub bot rhos)
bslice (VPair p1 p2) (Pair t1 t2)
    = let (t1',rho1) = bslice p1 t1
          (t2',rho2) = bslice p2 t2
      in (Pair t1' t2', rho1 `lub` rho2)
bslice VStar (Pair t1 t2)
    = let (t1',rho1) = bslice VStar t1
          (t2',rho2) = bslice VStar t2
      in (Pair t1' t2', rho1 `lub` rho2)
bslice p (Fst t)
    = let (t',rho) = bslice (VPair p bot) t
      in (Fst t', rho)
bslice p (Snd t)
    = let (t',rho) = bslice (VPair bot p) t
      in (Snd t', rho)
bslice (VInL p) (InL t)
    = let (t',rho) = bslice p t
      in (InL t',rho)
bslice VStar (InL t)
    = let (t',rho) = bslice VStar t
      in (InL t',rho)
bslice (VInR p) (InR t)
    = let (t', rho) = bslice p t
      in (InR t', rho)
bslice VStar (InR t)
    = let (t', rho) = bslice VStar t
      in (InR t', rho)
bslice p1 (IfThen t e1 e2 t1)
    = let (t1',rho1) = bslice p1 t1
          (t',rho)   = bslice VStar t
      in (IfThen t' e1 e2 t1', rho `lub` rho1)
bslice p2 (IfElse t e1 e2 t2)
    = let (t2',rho2) = bslice p2 t2
          (t',rho)   = bslice VStar t
      in (IfElse t' e1 e2 t2', rho `lub` rho2)
bslice p1 (CaseL t m x t1)
    = let (t1',rho1) = bslice p1 t1
          p          = lookupEnv' rho1 x
          rho1'      = unbindEnv rho1 x
          (t',rho)   = bslice (VInL p) t
      in (CaseL t' m x t1', rho `lub` rho1')
bslice p2 (CaseR t m x t2)
    = let (t2',rho2) = bslice p2 t2
          p          = lookupEnv' rho2 x
          rho2'      = unbindEnv rho2 x
          (t',rho)   = bslice (VInR p) t
      in (CaseR t' m x t2', rho `lub` rho2')
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
bslice (VRoll tv p) (Roll tv' t)
    | tv == tv'
    = let (t',rho) = bslice p t
      in (Roll tv' t', rho)
bslice VStar (Roll tv t)
    = let (t',rho) = bslice VStar t
      in (Roll tv t', rho)
bslice p (Unroll tv t)
    = let (t',rho) = bslice (VRoll tv p) t
      in (Unroll tv t', rho)
bslice _ x = error $ show x


pslice :: Value -> Trace -> (Exp, Env Value)
pslice VHole _     = (bot    , bot)
pslice p (Var x)   = (Var x  , singletonEnv x p)
pslice _ Unit      = (Unit   , bot)
pslice _ (CBool b) = (CBool b, bot)
pslice _ (CInt i)  = (CInt i , bot)
pslice (VClosure k env) (Fun _k')
    = (Fun k, env) -- assumes k <= k'
pslice VStar (Fun k)
    = (Fun k, constEnv (fvs k) VStar)
pslice p2 (Let x t1 t2)
    = let (t2',rho2) = pslice p2 t2
          p1         = lookupEnv' rho2 x
          rho2'      = unbindEnv rho2 x
          (t1',rho1) = pslice p1 t1
      in (Let x t1' t2', rho1 `lub` rho2')
pslice _ (Op f ts)
    = let (ts', rhos) = unzip (map (\t -> pslice VStar t) ts)
      in (Op f ts', foldl lub bot rhos)
pslice (VPair p1 p2) (Pair t1 t2)
    = let (t1',rho1) = pslice p1 t1
          (t2',rho2) = pslice p2 t2
      in (Pair t1' t2', rho1 `lub` rho2)
pslice VStar (Pair t1 t2)
    = let (t1',rho1) = pslice VStar t1
          (t2',rho2) = pslice VStar t2
      in (Pair t1' t2', rho1 `lub` rho2)
pslice p (Fst t)
    = let (t',rho) = pslice (VPair p bot) t
      in (Fst t', rho)
pslice p (Snd t)
    = let (t',rho) = pslice (VPair bot p) t
      in (Snd t', rho)
pslice (VInL p) (InL t)
    = let (t',rho) = pslice p t
      in (InL t',rho)
pslice VStar (InL t)
    = let (t',rho) = pslice VStar t
      in (InL t',rho)
pslice (VInR p) (InR t)
    = let (t', rho) = pslice p t
      in (InR t', rho)
pslice VStar (InR t)
    = let (t', rho) = pslice VStar t
      in (InR t', rho)
pslice p1 (IfThen t _ _ t1)
    = let (e1, rho1) = pslice p1 t1
          (e, rho)   = pslice VStar t
      in (If e e1 Hole, rho `lub` rho1)
pslice p2 (IfElse t _ _ t2)
    = let (e2, rho2) = pslice p2 t2
          (e, rho)   = pslice VStar t
      in (If e Hole e2, rho `lub` rho2)
pslice p1 (CaseL t _ x t1)
    = let (e1, rho1) = pslice p1 t1
          p          = lookupEnv' rho1 x
          rho1'      = unbindEnv rho1 x
          (e, rho)   = pslice (VInL p) t
      in (Case e (Match (x,e1) (bot,bot)), rho `lub` rho1')
pslice p2 (CaseR t _ x t2)
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
pslice (VRoll tv p) (Roll tv' t)
    | tv == tv'
    = let (t',rho) = pslice p t
      in (Roll tv' t', rho)
pslice VStar (Roll tv' t)
    = let (t',rho) = pslice VStar t
      in (Roll tv' t', rho)
pslice p (Unroll tv t)
    = let (t',rho) = pslice (VRoll tv p) t
      in (Unroll tv t', rho)
pslice v t = error $ "Cannot unevaluate value " ++ show v ++
                     " from trace " ++ show t

-- unevaluation.  Squash trace back down into expression.

uneval :: Trace -> Exp
uneval (Var x)           = Var x
uneval Unit              = Unit
uneval Hole              = Hole
uneval (CBool b)         = CBool b
uneval (CInt i)          = CInt i
uneval (CString s)       = CString s
uneval (Fun k)           = Fun k
uneval (Let x e1 e2)     = Let x (uneval e1) (uneval e2)
uneval (Op f es)         = Op f (map uneval es)
uneval (Pair e1 e2)      = Pair (uneval e1) (uneval e2)
uneval (Fst e)           = Fst (uneval e)
uneval (Snd e)           = Snd (uneval e)
uneval (InL e)           = InL (uneval e)
uneval (InR e)           = InR (uneval e)
uneval (Case e m)        = Case (uneval e) m
uneval (App e1 e2)       = App (uneval e1) (uneval e2)
uneval (Roll tv e)       = Roll tv (uneval e)
uneval (Unroll tv e)     = Unroll tv (uneval e)
--traces
uneval (CaseL t _ x t1)  = Case (uneval t) (Match (x, uneval t1) (bot, Hole))
uneval (CaseR t _ x t2)  = Case (uneval t) (Match (bot, Hole) (x, uneval t2))
uneval (IfThen t _ _ t1) = If (uneval t) (uneval t1) Hole
uneval (IfElse t _ _ t2) = If (uneval t) Hole (uneval t2)
uneval (Call t1 t2 _ _)  = App (uneval t1) (uneval t2)
