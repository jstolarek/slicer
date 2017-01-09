module Type where
import Env
import Trace
import LowerSemiLattice


tc :: Ctx -> Exp -> Type -> Bool
tc ctx (Roll e) (RecTy a ty) = tc ctx e (substTy ty a (RecTy a ty))
tc ctx e ty = (ti ctx e) == ty

ti :: Ctx -> Exp -> Type
ti ctx (Var x) = lookupEnv' ctx x
ti ctx (Let x e1 e2) = let ty1 = ti ctx e1
                       in ti (bindEnv ctx x ty1) e2
ti ctx Unit = UnitTy
ti ctx (CBool _) = BoolTy
ti ctx (If e e1 e2) = let BoolTy = ti ctx e
                          ty1 = ti ctx e1
                          ty2 = ti ctx e2
                      in ty1 `lub` ty2
ti ctx (CInt i) = IntTy
ti ctx (Op (O "val" _ _) [e]) = let TraceTy _ ty = ti ctx e
                                in ty
ti ctx (Op (O "replay" _ _) [e]) = let TraceTy ctx ty = ti ctx e
                                   in TraceTy ctx ty
ti ctx (Op (O "slice" _ _) [e1,e2]) = let TraceTy ctx ty1 = ti ctx e1
                                          ty2 = ti ctx e2
                                      in ty2 `lub` ty1
-- TODO: other ops
ti ctx (Op (O _ tys ty) es) = if (map (ti ctx) es) == tys
                              then ty
                              else undefined
ti ctx (Pair e1 e2) = PairTy (ti ctx e1) (ti ctx e2)
ti ctx (Fst e) = let PairTy ty1 _ = ti ctx e
                 in ty1
ti ctx (Snd e) = let PairTy _ ty2 = ti ctx e
                 in ty2
ti ctx (InL e) = SumTy (ti ctx e) HoleTy
ti ctx (InR e) = SumTy HoleTy (ti ctx e)
ti ctx (Case e m) = let SumTy ty1 ty2 = ti e
                    in tiMatch ctx ty1 ty2 m
ti ctx (Unroll e) = let RecTy a ty = ti ctx e
                    in subst ty a (RecTy a ty)
ti ctx (Hole) = HoleTy

tiMatch ctx ty1 ty2 (Match (x,e1) (y,e2))
    = let ty1' = ti (bindCtx x ty1) e1
          ty2' = ti (bindCtx x ty2) e2
      in ty1' `lub` ty2

