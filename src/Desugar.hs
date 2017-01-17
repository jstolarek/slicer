module Desugar
    ( -- * Desugaring TML expressions
      desugar
    ) where

import qualified Absyn as A
import           Env
import           PrettyPrinting
import           Trace
import           UpperSemiLattice

import qualified Data.Map as M

-- Assuming that op name + argument types determines the op result type.
lookupOp :: Primitive -> [Type] -> Type
-- built-in operators, closely corresponds to evalOp
lookupOp op [IntTy   , IntTy   ] | isCommonOp  op = BoolTy
lookupOp op [BoolTy  , BoolTy  ] | isCommonOp  op = BoolTy
lookupOp op [StringTy, StringTy] | isCommonOp  op = BoolTy
lookupOp op [IntTy   , IntTy   ] | isIntBinOp  op = IntTy
lookupOp op [IntTy   , IntTy   ] | isIntRelOp  op = BoolTy
lookupOp op [BoolTy  , BoolTy  ] | isBoolRelOp op = BoolTy
lookupOp op [BoolTy  ]           | isBoolUnOp  op = BoolTy
-- built-in primitives
lookupOp PrimVal        [TraceTy _ ty] = ty
lookupOp PrimWhere      [TraceTy _ ty] = ty
lookupOp PrimDep        [TraceTy _ ty] = ty
lookupOp PrimExpr       [TraceTy _ ty] = ty
lookupOp PrimTreeSize   [TraceTy _ _ ] = IntTy
lookupOp PrimProfile    [TraceTy _ _ ] = UnitTy
lookupOp PrimProfile2   [TraceTy _ _ ] = UnitTy
lookupOp PrimVisualize  [StringTy, TraceTy _ _]              = UnitTy
lookupOp PrimVisualize2 [StringTy, TraceTy _ _, TraceTy _ _] = UnitTy
lookupOp PrimSlice [ty@(TraceTy _ ty1), ty2] =
    if ty1 == ty2
    then ty
    else error "slice type mismatch" -- TODO: Partialize
lookupOp PrimPSlice [ty@(TraceTy _ ty1), ty2] =
    if ty1 == ty2
    then ty
    else error "slice type mismatch" -- TODO: Partialize
lookupOp op tys =
    error ("Unknown op " ++ (show op) ++ " at types " ++ show (map pp tys))

--todo: handle general sums/datatypes
inject :: [(A.Con, A.Type)] -> A.Con -> Exp -> Exp
inject [(inl, _), (_  , _)] k e | k == inl = InL e
inject [(_  , _), (inr, _)] k e | k == inr = InR e
inject _ _ _ = error "non binary sums not yet implemented"


-- simple version that just fails if term is not well-typed
desugar :: A.TyCtx -> Ctx -> A.Exp -> (Exp,Type)
desugar _     gamma (A.Var x) = case lookupEnv' gamma x
                                of HoleTy -> error ("unbound variable "++show x)
                                   ty -> (Var x, ty)
desugar _     _     (A.CBool b) = (CBool b, BoolTy)
desugar _     _     (A.CInt i) = (CInt i, IntTy)
desugar _     _     (A.CString s) = (CString s, StringTy)
desugar decls gamma (A.Let x e1 e2)
    = let (e1',ty1) = desugar decls gamma e1
          (e2',ty2) = desugar decls (bindEnv gamma x ty1) e2
      in (Let x e1' e2',ty2)
desugar decls gamma (A.LetR _ e1) = desugar decls gamma e1
desugar _     _     (A.Unit) = (Unit, UnitTy)
desugar decls gamma (A.If e e1 e2)
    = let (e',BoolTy) = desugar decls gamma e
          (e1',ty1) = desugar decls gamma e1
          (e2',ty2) = desugar decls gamma e2
      in if ty1 == ty2
         then (If e' e1' e2', ty1)
         else error "Types of branches do not match"
desugar decls gamma (A.Op f es)
    = let (es',tys) = unzip (map (desugar decls gamma) es)
          ty        = lookupOp f tys
      in (Op f es', ty)
desugar decls gamma (A.Pair e1 e2)
    = let (e1',ty1) = desugar decls gamma e1
          (e2',ty2) = desugar decls gamma e2
      in (Pair e1' e2', PairTy ty1 ty2)
desugar decls gamma (A.Fst e)
    = let (e1',ty) = desugar decls gamma e
      in case ty
         of PairTy ty1 _ -> (Fst e1', ty1)
            _ -> error ("expected pair type, got " ++ show ty)
desugar decls gamma (A.Snd e)
    = let (e1', ty) = desugar decls gamma e
      in case ty
         of PairTy _ ty2 ->  (Snd e1', ty2)
            _ -> error ("expected pair type, got " ++ show ty)
desugar decls gamma (A.Con k [e])  -- TODO: Handle general case
    = let (e',ty) = desugar decls gamma e
      in case  A.getTyDeclByCon decls k
         of Just (A.TyDecl dataty cons, ty') ->
              if ty ==  desugarTy ty'
              then (Roll (Just dataty) (inject cons k e'), TyVar dataty)
              else error ("ill-typed argument "++ show ty ++" to constructor " ++ show k ++ " which expects type " ++ show ty')
            Nothing -> error "undeclared constructor"
desugar _     _     (A.Con k _) = error ("Invalid data constructor " ++ show k)
desugar decls gamma (A.Case e m)
    = let (e',TyVar dataty) = desugar decls gamma e
      in case (A.getTyDeclByName decls dataty)
         of Just decl -> desugarMatch decls gamma (A.constrs decl) (Unroll (Just dataty) e') m
            Nothing -> error "undeclared datatype in case"
desugar decls gamma (A.Fun k) = desugarFun decls gamma k
desugar decls gamma (A.App e1 e2) =
    let (e1', FunTy ty1 ty2) = desugar decls gamma e1
        (e2', ty1') = desugar decls gamma e2
    in if ty1 == ty1'
       then (App e1' e2', ty2)
       else error "mismatched types in app"
desugar decls gamma (A.Trace e) =
    let (e',ty) = desugar decls gamma e
    in (Trace e', TraceTy gamma ty)
desugar _ _  (A.Hole ty) = (Hole,desugarTy ty)


desugarTy :: A.Type -> Type
desugarTy A.IntTy = IntTy
desugarTy A.BoolTy = BoolTy
desugarTy A.UnitTy = UnitTy
desugarTy A.StringTy = StringTy
desugarTy (A.PairTy ty1 ty2) = PairTy (desugarTy ty1) (desugarTy ty2)
desugarTy (A.SumTy ty1 ty2) = SumTy (desugarTy ty1) (desugarTy ty2)
desugarTy (A.FunTy ty1 ty2) = FunTy (desugarTy ty1) (desugarTy ty2)
desugarTy (A.TyVar ty) = TyVar ty
desugarTy (A.TraceTy ctx ty) = TraceTy (fmap desugarTy ctx) (desugarTy ty)


desugarFun :: A.TyCtx -> Ctx -> A.Code -> (Exp,Type)
desugarFun decls gamma (A.Rec f args rty e lbl) =
    let fun_ty    = desugarTy (foldr (\(_,ty) ty' -> A.FunTy ty ty') rty args)
        gamma'    = bindEnv gamma f fun_ty
        gamma''   = foldl (\g (x,ty) -> bindEnv g x (desugarTy ty)) gamma' args
        (e',rty') = desugar decls gamma'' e
        (x1:tl)   = map fst args
        lbl'      = mkL `fmap` lbl
        e'' = foldr (\x e0 -> Fun (Rec bot x e0 Nothing)) e' tl
        e''' = Fun (Rec f x1 e'' lbl')
    in if desugarTy rty == rty'
       then (e''', fun_ty)
       else error "declared function return type is wrong"

-- todo: generalize to handle arbitrary datatypes
desugarMatch :: A.TyCtx -> Ctx -> [(A.Con, A.Type)] -> Exp -> A.Match -> (Exp,Type)
desugarMatch decls gamma [(inl, ty1), (inr, ty2)] e (A.Match m) =
    let Just ([x1],e1) = M.lookup inl m
        (e1',ty1') = desugar decls (bindEnv gamma x1 (desugarTy ty1)) e1
        Just ([x2],e2) = M.lookup inr m
        (e2',ty2') = desugar decls (bindEnv gamma x2 (desugarTy ty2)) e2
    in if ty1' == ty2'
       then (Case e (Match (x1,e1') (x2,e2')), ty1')
        else error ("Type mismatch in case expression: "++ show ty1' ++ " doesn't match " ++ show ty2')
desugarMatch _ _ _ _ _ = error "desugarMatch: data type is not binary"
