module Language.Slicer.Desugar
    ( -- * Desugaring TML expressions
      desugar
    ) where

import qualified Language.Slicer.Absyn as A
import           Language.Slicer.Core
import           Language.Slicer.Env
import           Language.Slicer.Error
import           Language.Slicer.Monad ( SlM )
import           Language.Slicer.Monad.Desugar
import           Language.Slicer.Primitives
import           Language.Slicer.UpperSemiLattice

import           Control.Monad.Except
import qualified Data.Map as M
import           Data.Maybe

desugar :: A.TyCtx -> Ctx -> A.Exp -> SlM (Exp, Type)
desugar decls gamma expr = runDesugarM decls gamma (desugarM expr)

-- Assuming that op name + argument types determines the op result type.
lookupOp :: Primitive -> [Type] -> DesugarM Type
-- built-in operators, closely corresponds to evalOp.  Note that we test types
-- of argument using == rather than a direct pattern match, because == for types
-- takes exception type into account (in other words we admit exceptions as
-- arguments to primitive operators)
lookupOp op tys | tys == [IntTy   , IntTy   ] && isCommonOp  op = return BoolTy
lookupOp op tys | tys == [BoolTy  , BoolTy  ] && isCommonOp  op = return BoolTy
lookupOp op tys | tys == [StringTy, StringTy] && isCommonOp  op = return BoolTy
lookupOp op tys | tys == [IntTy   , IntTy   ] && isIntBinOp  op = return IntTy
lookupOp op tys | tys == [DoubleTy, DoubleTy] && isDoubleBinOp op =
    return DoubleTy
lookupOp op tys | tys == [IntTy   , IntTy   ] && isOrdOp     op = return BoolTy
lookupOp op tys | tys == [DoubleTy, DoubleTy] && isOrdOp     op = return BoolTy
lookupOp op tys | tys == [BoolTy  , BoolTy  ] && isBoolRelOp op = return BoolTy
lookupOp op tys | tys == [BoolTy  ]           && isBoolUnOp  op = return BoolTy
-- built-in primitives.  No exceptions allowed here, thus we use direct pattern
-- matching on arguments.
lookupOp PrimVal           [TraceTy ty] = return ty
lookupOp PrimVisualize     [StringTy, _]               = return UnitTy
lookupOp PrimVisualizeDiff [StringTy, t, t'] | t == t' = return UnitTy
lookupOp PrimTraceSlice [ty@(TraceTy ty1), ty2] =
    if ty1 == ty2
    then return ty
    else typeError ("Slice type mismatch: " ++ show ty1 ++
                    " does not match " ++ show ty2)
lookupOp PrimBwdSlice [ty@(TraceTy ty1), ty2] =
    if ty1 == ty2
    then return ty
    else typeError ("Backward slice type mismatch: " ++ show ty1 ++
                    " does not match " ++ show ty2)
lookupOp op tys =
    desugarError ("Unknown op " ++ show op ++ " at types " ++
                  show tys)

--todo: handle general sums/datatypes
inject :: (A.Con, A.Con) -> A.Con -> Exp -> DesugarM Exp
inject (inl, _) k e | k == inl = return (EInL e)
inject (_, inr) k e | k == inr = return (EInR e)
inject _ _ _ = desugarError "No matching constructor"


-- simple version that just fails if term is not well-typed
desugarM :: A.Exp -> DesugarM (Exp, Type)
desugarM (A.Var x)
    = do gamma <- getGamma
         case lookupEnv' gamma x of
           HoleTy -> desugarError ("Unbound variable " ++ show x)
           ty     -> return (EVar x, ty)
desugarM (A.CBool   b) = return (EBool   b, BoolTy  )
desugarM (A.CInt    i) = return (EInt    i, IntTy   )
desugarM (A.CDouble d) = return (EDouble d, DoubleTy)
desugarM (A.CString s) = return (EString s, StringTy)
desugarM (A.Let x e1 e2)
    = do (e1',ty1) <- desugarM e1
         (e2',ty2) <- withBinder x ty1 (desugarM e2)
         return (ELet x e1' e2',ty2)
desugarM (A.LetR _ e1) = desugarM e1
desugarM (A.Unit) = return (EUnit, UnitTy)
desugarM (A.If e e1 e2)
    = do (e' , ty ) <- desugarM e
         unless (isCondTy ty) $ typeError ("If condition is not a boolean type")
         (e1', ty1) <- desugarM e1
         (e2', ty2) <- desugarM e2
         if ty1 == ty2
         then return (EIf e' e1' e2', ty1)
         else typeError ("Types of branches do not match :" ++
                        show ty1 ++ " does not match " ++ show ty2)
desugarM (A.Op f es)
    = do (es',tys) <- mapAndUnzipM desugarM es
         ty        <- lookupOp f tys
         return (EOp f es', ty)
desugarM (A.Pair e1 e2)
    = do (e1',ty1) <- desugarM e1
         (e2',ty2) <- desugarM e2
         return (EPair e1' e2', PairTy ty1 ty2)
desugarM (A.Fst e)
    = do (e1', ty) <- desugarM e
         if isPairTy ty
         then return (EFst e1', fstTy ty)
         else typeError ("Expected pair type but got " ++ show ty)
desugarM (A.Snd e)
    = do (e1', ty) <- desugarM e
         if isPairTy ty
         then return (ESnd e1', sndTy ty)
         else typeError ("Expected pair type but got " ++  show ty)
desugarM (A.Con k e)
    = do (e', ty) <- desugarM e
         decls    <- getDecls
         case A.getTyDeclByCon decls k of
           Just (decl@(A.TyDecl dataty _ _), ty') ->
              if ty == desugarTy ty'
              then do aval <- inject (A.constrs decl) k e'
                      return (ERoll dataty aval, TyVar dataty)
              else typeError ("Ill-typed argument "  ++ show ty ++
                              " to constructor "     ++ show k  ++
                              " which expects type " ++ show ty')
           Nothing -> desugarError ("Undeclared constructor: " ++ show k)
desugarM (A.Case e m)
    = do (e', t) <- desugarM e
         when (isExnTy t) $
              desugarError "Case scrutinee cannot throw exceptions"
         let (TyVar dataty) = t
         decls   <- getDecls
         case (A.getTyDeclByName decls dataty) of
           Just decl -> desugarMatch (A.constrL decl) (A.constrR decl)
                                     (EUnroll dataty e') m
           Nothing -> desugarError ("Undeclared datatype in case: " ++
                                    show dataty)
desugarM (A.Fun k) = desugarFun k
desugarM (A.App e1 e2) =
    do (e1', ty1) <- desugarM e1
       unless (isFunTy ty1) $
              typeError ("Function application error. Expected a function type "
                         ++ "but got type " ++ show ty1)
       (e2', ty2) <- desugarM e2
       if fstTy ty1 == ty2
       then return (EApp e1' e2', sndTy ty1)
       else typeError
                ("Mismatched types in application.  Function expects "
               ++ show (fstTy ty1) ++ " but argument has type " ++ show ty2)
desugarM (A.Trace e)
    = do (e', ty) <- desugarM e
         return (ETrace e', TraceTy ty)
desugarM (A.Hole ty) = return (EHole, desugarTy ty)
-- Desugaring mutable references. Cf. TAPL, p. 165 for typechecking rules
desugarM (A.Ref e)
    = do (e', ty) <- desugarM e
         return (ERef e', RefTy ty)
desugarM (A.Deref e)
    = do (e', ty) <- desugarM e
         unless (isRefTy ty) $
                desugarError ("Dereferenced expression (" ++ show e ++
                             ") does not have a reference type")
         return (EDeref e', fstTy ty)
desugarM (A.Assign e1 e2)
    = do (e1', t1) <- desugarM e1
         unless (isRefTy t1) $
                typeError ("Expression does not have reference type: " ++
                           show e1)
         (e2', t2) <- desugarM e2
         let t1' = fstTy t1
         unless (t1' == t2) $ typeError ("Cannot assign expression of type: "
                                    ++ show t2  ++ " to reference of type "
                                    ++ show t1' ++ ". Offending expression is: "
                                    ++ show e2)
         return (EAssign e1' e2', UnitTy)
desugarM (A.Seq e1 e2)
    = do (e1', t1) <- desugarM e1
         unless (t1 == UnitTy) $ typeError ("Cannot sequence.  Expression "
                                    ++ show e1 ++ " has type " ++ show t1
                                    ++ " but it shold have unit type.")
         (e2', t2) <- desugarM e2
         return (ESeq e1' e2', t2)
desugarM (A.While e1 e2)
    = do (e1', t1) <- desugarM e1
         unless (t1 == BoolTy) $ typeError ("While loop test  "
                                    ++ show e1 ++ " has type " ++ show t1
                                    ++ " but it shold have bool type.")
         (e2', t2) <- desugarM e2
         unless (t2 == UnitTy) $ typeError ("While loop body "
                                    ++ show e2 ++ " has type " ++ show t2
                                    ++ " but it shold have unit type.")
         return (EWhile e1' e2', t2)
-- | Arrays
desugarM (A.Arr e1 e2)
    = do (e1', t1) <- desugarM e1
         (e2', t2) <- desugarM e2
         unless (t1 == IntTy) $ typeError ("Array length has type "
                                            ++ show t1
                                            ++ " but should have int type.")
         return (EArr e1' e2', ArrTy t2)
desugarM (A.ArrGet e1 e2)
    = do (e1', t1) <- desugarM e1
         unless (isArrTy t1) $
                desugarError ("Expression (" ++ show e1 ++ ") has type " ++
                              show t1 ++ "but should be an array")
         (e2', t2) <- desugarM e2
         unless (t2 == IntTy) $
                desugarError ("Dereferenced expression index (" ++ show e2 ++
                             ") has type " ++ show t2 ++ " but should have type int.")
         return (EArrGet e1' e2', fstTy t1)
desugarM (A.ArrSet e1 e2 e3)
    = do (e1', t1) <- desugarM e1
         unless (isArrTy t1) $
                desugarError ("Dereferenced expression (" ++ show e1 ++
                             ") does not have array type")
         (e2', t2) <- desugarM e2
         unless (t2 == IntTy) $
                desugarError ("Dereferenced expression index (" ++ show e2 ++
                             ") has type " ++ show t2 ++ " but should have type int.")
         (e3', t3) <- desugarM e3
         let t1' = fstTy t1
         unless (t1' == t3) $ typeError ("Cannot assign expression of type: "
                                    ++ show t3  ++ " to array of type "
                                    ++ show t1' ++ ". Offending expression is: "
                                    ++ show e3)
         return (EArrSet e1' e2' e3', UnitTy)
-- Exceptions
desugarM (A.Raise e)
    = do (e', t) <- desugarM e
         unless (t == StringTy) $
                typeError ("Arguments to raise must have string type, but " ++
                           "expression " ++ show t ++ " has type " ++ show t)
         return (ERaise e', ExnTy)
desugarM (A.Catch e x h)
    = do (e', ty1) <- desugarM e
         (h', ty2) <- withBinder x StringTy (desugarM h)
         unless (ty1 == ty2) $
                typeError ("Types of \"try\" and \"with\" blocks don't match. "
                        ++ "Try has type " ++ show ty1 ++ " but with has type "
                        ++ show ty2)
         return (ETryWith e' x h', ty1)

desugarTy :: A.Type -> Type
desugarTy A.IntTy            = IntTy
desugarTy A.BoolTy           = BoolTy
desugarTy A.UnitTy           = UnitTy
desugarTy A.StringTy         = StringTy
desugarTy A.DoubleTy         = DoubleTy
desugarTy A.ExnTy            = ExnTy
desugarTy (A.RefTy ty)       = RefTy (desugarTy ty)
desugarTy (A.ArrTy ty)       = ArrTy (desugarTy ty)
desugarTy (A.PairTy ty1 ty2) = PairTy (desugarTy ty1) (desugarTy ty2)
desugarTy (A.SumTy  ty1 ty2) = SumTy (desugarTy ty1) (desugarTy ty2)
desugarTy (A.FunTy  ty1 ty2) = FunTy (desugarTy ty1) (desugarTy ty2)
desugarTy (A.TyVar  ty)      = TyVar ty
desugarTy (A.TraceTy ty)     = TraceTy (desugarTy ty)


desugarFun :: A.Code -> DesugarM (Exp,Type)
desugarFun (A.Rec f args rty e lbl)
    = do gamma <- getGamma
         let fun_ty    = desugarTy (foldr (\(_,ty) ty' -> A.FunTy ty ty')
                                          rty args)
             gamma'    = bindEnv gamma f fun_ty
             gamma''   = foldl (\g (x,ty) -> bindEnv g x (desugarTy ty)) gamma'
                               args
         (e', rty') <- withGamma gamma'' (desugarM e)
         let (x1:tl)   = map fst args
             lbl'      = mkL `fmap` lbl
             e''       = foldr (\x e0 -> EFun (Rec bot x e0 Nothing)) e' tl
             e'''      = EFun (Rec f x1 e'' lbl')
         if desugarTy rty == rty'
         then return (e''', fun_ty)
         else typeError ("Declared function return type is " ++
                          show (desugarTy rty) ++
                         " but function body has type " ++ show rty')

-- todo: generalize to handle arbitrary datatypes
desugarMatch :: (A.Con, A.Type) -> (A.Con, A.Type) -> Exp -> A.Match
             -> DesugarM (Exp, Type)
desugarMatch (inl, ty1) (inr, ty2) e (A.Match m) =
    do let con1 = M.lookup inl m
       let con2 = M.lookup inr m
       when (isNothing con1) (typeError $ "Expected match on constructor " ++
                                          show inl ++ " but none found.")
       when (isNothing con2) (typeError $ "Expected match on constructor " ++
                                          show inr ++ " but none found.")
       let Just (x1, e1) = con1
           Just (x2, e2) = con2
       (e1', ty1') <- maybeWithBinder x1 (desugarTy ty1) (desugarM e1)
       (e2', ty2') <- maybeWithBinder x2 (desugarTy ty2) (desugarM e2)
       if ty1' == ty2'
       then return (ECase e (Match (x1, e1') (x2, e2')), ty1')
       else typeError ("Type mismatch in case expression: " ++ show ty1' ++
                       " does not match " ++ show ty2' )
