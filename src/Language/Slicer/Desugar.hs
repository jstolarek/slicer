module Language.Slicer.Desugar
    ( -- * Desugaring TML expressions
      desugar
    ) where

import qualified Language.Slicer.Absyn as A
import           Language.Slicer.Core
import           Language.Slicer.Env
import           Language.Slicer.Monad
import           Language.Slicer.PrettyPrinting
import           Language.Slicer.UpperSemiLattice

import           Control.Monad ( mapAndUnzipM, when )
import qualified Data.Map as M
import           Data.Maybe ( isNothing )

-- Assuming that op name + argument types determines the op result type.
lookupOp :: Primitive -> [Type] -> SlM Type
-- built-in operators, closely corresponds to evalOp
lookupOp op [IntTy   , IntTy   ] | isCommonOp  op = return BoolTy
lookupOp op [BoolTy  , BoolTy  ] | isCommonOp  op = return BoolTy
lookupOp op [StringTy, StringTy] | isCommonOp  op = return BoolTy
lookupOp op [IntTy   , IntTy   ] | isIntBinOp  op = return IntTy
lookupOp op [IntTy   , IntTy   ] | isIntRelOp  op = return BoolTy
lookupOp op [BoolTy  , BoolTy  ] | isBoolRelOp op = return BoolTy
lookupOp op [BoolTy  ]           | isBoolUnOp  op = return BoolTy
-- built-in primitives
lookupOp PrimVal           [TraceTy ty] = return ty
lookupOp PrimWhere         [TraceTy ty] = return ty
lookupOp PrimDep           [TraceTy ty] = return ty
lookupOp PrimExpr          [TraceTy ty] = return ty
lookupOp PrimTreeSize      [TraceTy _ ] = return IntTy
lookupOp PrimProfile       [TraceTy _ ] = return UnitTy
lookupOp PrimProfileDiff   [TraceTy _ ] = return UnitTy
lookupOp PrimVisualize     [StringTy, TraceTy _]            = return UnitTy
lookupOp PrimVisualizeDiff [StringTy, TraceTy _, TraceTy _] = return UnitTy
lookupOp PrimSlice [ty@(TraceTy ty1), ty2] =
    if ty1 == ty2
    then return ty
    else typeError ("Slice type mismatch: " ++ show ty1 ++
                    " does not match " ++ show ty2)
lookupOp PrimPSlice [ty@(TraceTy ty1), ty2] =
    if ty1 == ty2
    then return ty
    else typeError ("Slice type mismatch: " ++ show ty1 ++
                    " does not match " ++ show ty2)
lookupOp op tys =
    desugarError ("Unknown op " ++ show op ++ " at types " ++
                  show (map pp tys))

--todo: handle general sums/datatypes
inject :: [(A.Con, A.Type)] -> A.Con -> Exp -> SlM Exp
inject [(inl, _), (_  , _)] k e | k == inl = return (InL e)
inject [(_  , _), (inr, _)] k e | k == inr = return (InR e)
inject _ _ _ = desugarError "Non binary sums not yet implemented"


-- simple version that just fails if term is not well-typed
desugar :: A.TyCtx -> Ctx -> A.Exp -> SlM (Exp, Type)
desugar _     gamma (A.Var x)
    = case lookupEnv' gamma x of
        HoleTy -> desugarError ("Unbound variable " ++ show x)
        ty     -> return (Var x, ty)
desugar _     _     (A.CBool b)   = return (CBool b, BoolTy)
desugar _     _     (A.CInt i)    = return (CInt i, IntTy)
desugar _     _     (A.CString s) = return (CString s, StringTy)
desugar decls gamma (A.Let x e1 e2)
    = do (e1',ty1) <- desugar decls gamma e1
         (e2',ty2) <- desugar decls (bindEnv gamma x ty1) e2
         return (Let x e1' e2',ty2)
desugar decls gamma (A.LetR _ e1) = desugar decls gamma e1
desugar _     _     (A.Unit) = return (Unit, UnitTy)
desugar decls gamma (A.If e e1 e2)
    = do (e' , BoolTy) <- desugar decls gamma e
         (e1', ty1   ) <- desugar decls gamma e1
         (e2', ty2   ) <- desugar decls gamma e2
         if ty1 == ty2
         then return (If e' e1' e2', ty1)
         else typeError ("Types of branches do not match :" ++
                        show ty1 ++ " does not match " ++ show ty2)
desugar decls gamma (A.Op f es)
    = do (es',tys) <- mapAndUnzipM (desugar decls gamma) es
         ty        <- lookupOp f tys
         return (Op f es', ty)
desugar decls gamma (A.Pair e1 e2)
    = do (e1',ty1) <- desugar decls gamma e1
         (e2',ty2) <- desugar decls gamma e2
         return (Pair e1' e2', PairTy ty1 ty2)
desugar decls gamma (A.Fst e)
    = do (e1', ty) <- desugar decls gamma e
         case ty of
           PairTy ty1 _ -> return (Fst e1', ty1)
           _ -> typeError ("Expected pair type but got " ++ show ty)
desugar decls gamma (A.Snd e)
    = do (e1', ty) <- desugar decls gamma e
         case ty of
           PairTy _ ty2 -> return  (Snd e1', ty2)
           _ -> typeError ("Expected pair type but got " ++  show ty)
desugar decls gamma (A.Con k e)
    = do (e', ty) <- desugar decls gamma e
         case A.getTyDeclByCon decls k of
           Just (A.TyDecl dataty cons, ty') ->
              if ty == desugarTy ty'
              then do aval <- inject cons k e'
                      return (Roll (Just dataty) aval, TyVar dataty)
              else typeError ("Ill-typed argument "  ++ show ty ++
                              " to constructor "     ++ show k  ++
                              " which expects type " ++ show ty')
           Nothing -> desugarError ("Undeclared constructor: " ++ show k)
desugar decls gamma (A.Case e m)
    = do (e', TyVar dataty) <- desugar decls gamma e
         case (A.getTyDeclByName decls dataty) of
           Just decl -> desugarMatch decls gamma (A.constrs decl)
                                     (Unroll (Just dataty) e') m
           Nothing -> desugarError ("Undeclared datatype in case: " ++
                                    show dataty)
desugar decls gamma (A.Fun k) = desugarFun decls gamma k
desugar decls gamma (A.App e1 e2) =
    do (e1', FunTy ty1 ty2) <- desugar decls gamma e1
       (e2', ty1'         ) <- desugar decls gamma e2
       if ty1 == ty1'
       then return (App e1' e2', ty2)
       else typeError ("Mismatched types in application.  Function expects " ++
                        show ty1 ++ " but argument has type " ++ show ty1')
desugar decls gamma (A.Trace e)
    = do (e', ty) <- desugar decls gamma e
         return (Trace e', TraceTy ty)
desugar _ _  (A.Hole ty) = return (Hole, desugarTy ty)


desugarTy :: A.Type -> Type
desugarTy A.IntTy            = IntTy
desugarTy A.BoolTy           = BoolTy
desugarTy A.UnitTy           = UnitTy
desugarTy A.StringTy         = StringTy
desugarTy (A.PairTy ty1 ty2) = PairTy (desugarTy ty1) (desugarTy ty2)
desugarTy (A.SumTy  ty1 ty2) = SumTy (desugarTy ty1) (desugarTy ty2)
desugarTy (A.FunTy  ty1 ty2) = FunTy (desugarTy ty1) (desugarTy ty2)
desugarTy (A.TyVar  ty)      = TyVar ty
desugarTy (A.TraceTy ty)     = TraceTy (desugarTy ty)


desugarFun :: A.TyCtx -> Ctx -> A.Code -> SlM (Exp,Type)
desugarFun decls gamma (A.Rec f args rty e lbl)
    = do let fun_ty    = desugarTy (foldr (\(_,ty) ty' -> A.FunTy ty ty')
                                          rty args)
             gamma'    = bindEnv gamma f fun_ty
             gamma''   = foldl (\g (x,ty) -> bindEnv g x (desugarTy ty)) gamma'
                               args
         (e', rty') <- desugar decls gamma'' e
         let (x1:tl)   = map fst args
             lbl'      = mkL `fmap` lbl
             e''       = foldr (\x e0 -> Fun (Rec bot x e0 Nothing)) e' tl
             e'''      = Fun (Rec f x1 e'' lbl')
         if desugarTy rty == rty'
         then return (e''', fun_ty)
         else typeError ("Declared function return type is " ++
                          show (desugarTy rty) ++
                         " but function body has type " ++ show rty')

-- todo: generalize to handle arbitrary datatypes
desugarMatch :: A.TyCtx -> Ctx -> [(A.Con, A.Type)] -> Exp -> A.Match
             -> SlM (Exp, Type)
desugarMatch decls gamma [(inl, ty1), (inr, ty2)] e (A.Match m) =
    do let con1 = M.lookup inl m
       let con2 = M.lookup inr m
       when (isNothing con1) (typeError $ "Expected match on constructor " ++
                                          show inl ++ " but none found.")
       when (isNothing con2) (typeError $ "Expected match on constructor " ++
                                          show inr ++ " but none found.")
       let Just (x1, e1) = con1
           Just (x2, e2) = con2
       (e1', ty1') <- desugar decls (bindEnv gamma x1 (desugarTy ty1)) e1
       (e2', ty2') <- desugar decls (bindEnv gamma x2 (desugarTy ty2)) e2
       if ty1' == ty2'
       then return (Case e (Match (x1, e1') (x2, e2')), ty1')
       else typeError ("Type mismatch in case expression: " ++ show ty1' ++
                       " does not match " ++ show ty2' )
desugarMatch _ _ _ _ _ = desugarError "desugarMatch: data type is not binary"
