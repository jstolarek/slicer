{-# LANGUAGE FlexibleInstances, FlexibleContexts, TupleSections, ViewPatterns #-}

-- We temporarily silence all warnings in this module.  It is in such a sorry
-- state that it is not worth bothering keeping it warning-free.
{-# OPTIONS_GHC -fno-warn-orphans -w #-}

module Language.Slicer.Resugar where

import qualified Language.Slicer.Absyn as A
import           Language.Slicer.Core
import           Language.Slicer.Env
import           Language.Slicer.Parser -- for constants
import           Language.Slicer.PrettyPrinting
import           Language.Slicer.UpperSemiLattice

import           Control.Arrow hiding ((<+>))
import           Control.Exception
import qualified Data.Map as Map
import           Text.PrettyPrint

-- Old stuff we're not using.

forLaTeX :: Bool
forLaTeX = False

-- Not the best name, but will do for now.
class (PP a, PP (A.TyCtx, a)) => Container a where
   -- Whether I am a "container" (see below for meaning). Only defined for non-terminals.
   container :: a -> Bool
   -- Whether to parenthesise me if I'm contained by something other than a container.
   parenth :: a -> Bool

   partial_parensOpt :: A.TyCtx -> a -> a -> a -> Doc
   partial_parensOpt tyCtx e e1 e1' =
      let doc = pp_partial (tyCtx, e1) (tyCtx, e1') in
      if not (container e) && parenth e1
         then parens doc
         else doc

indent :: Int
indent = 2

-- Plan is to migrate my old prettyprinting code over and dump James' implementation in Traces.hs.
-- For now, we use James' impl, and just add these extra cases.
-- Also, ideally we would factor this into two parts: resugaring back into the sugared syntax, and
-- then prettyprinting from the sugared syntax.

-- Wrap in textcolor, if LaTeX enabled.
colorise :: String -> Doc -> Doc
colorise col d =
   if forLaTeX
   then zeroWidthText ("\\textcolor{" ++ col ++ "}{") <> d <> zeroWidthText "}"
   else d

coloriseIf :: Bool -> String -> Doc -> Doc
coloriseIf b col = if b then colorise col else id

-- Underline, if LaTeX enabled.
underline :: Doc -> Doc
underline d =
   if forLaTeX
   then zeroWidthText ("\\ul{") <> d <> zeroWidthText "}"
   else d


instance PP (A.TyCtx, Value) where
   pp x = pp_partial x x
   pp_partial (tyCtx, VStar) (eq tyCtx -> True, VStar) = colorise "Gray" $ text $ "{$\\Diamond$}"
   pp_partial (tyCtx, VClosure k env) (eq tyCtx -> True, VClosure k' env') =
      pp_partial (tyCtx, (env, EFun k)) (tyCtx, (env', EFun k'))
   pp_partial (tyCtx, VStoreLoc _) (eq tyCtx -> True, VStoreLoc _) =
      text "<ref>"
   pp_partial (tyCtx, v) (eq tyCtx -> True, v') =
      pp_partial (tyCtx, val2exp v) (tyCtx, val2exp v')
   pp_partial _ _ = error "Pretty-printing error: (TyCtx, Value)"

instance (Eq a, PP (A.TyCtx, a)) => PP (A.TyCtx, (Env Value, a)) where
   pp (tyCtx, (rho, e)) = pp_partial (tyCtx, (rho, e)) (tyCtx, (rho, e))
   pp_partial (tyCtx, ((== emptyEnv) -> True, e)) (eq tyCtx -> True, ((== emptyEnv) -> True, e')) =
      pp_partial (tyCtx, e) (tyCtx, e')
   pp_partial (tyCtx, (_rho, e)) (eq tyCtx -> True, (_rho', e')) =
      {-vcat [text strWith, nest indent $ pp_partial (tyCtx, rho) (tyCtx, rho') <+> text strIn] $$ -}
      pp_partial (tyCtx, e) (tyCtx, e')
   pp_partial _ _ = error "Pretty-printing error: (TyCtx, (Env Value, a))"

instance PP (A.TyCtx, Env Value) where
   pp (tyCtx, env) = pp_partial (tyCtx, env) (tyCtx, env)
   pp_partial (tyCtx, (== emptyEnv) -> True) (eq tyCtx -> True, (== emptyEnv) -> True) = empty
   pp_partial (tyCtx, Env rho) (eq tyCtx -> True, Env rho') =
      assert (Map.keys rho == Map.keys rho') $
      vcat $ punctuate comma $
             map (uncurry $ pp_partial_binding tyCtx) $
                 zipWith (\(x, v) (_, v') -> (x, Just (v, v'))) (Map.assocs rho) (Map.assocs rho')
   pp_partial _ _ = error "Pretty-printing error: (TyCtx, Env Value)"

instance Container Exp where
   -- Ignore trace operations for now.
   container (ELet _ _ _)      = True
   container (EIf _ _ _)       = True
   container (EOp _ _)         = False
   container (EPair _ _)       = True
   container (EFst _)          = False
   container (ESnd _)          = False
   container (ECase _ _)       = True
   container (EInL _)          = False
   container (EInR _)          = False
   container (EFun _)          = True
   container (EApp _ _)        = False
   container (ERoll _ _)       = False
   container (EUnroll _ _)     = False
   container _                 = error "Unsupported Exp container"

   parenth EHole       = False
   parenth (EBool _)   = False
   parenth (EInt _)    = False
   parenth EUnit       = False
   parenth (EPair _ _) = False
   parenth (EVar _)    = False
   parenth _           = True

instance PP (A.TyCtx, Exp) where
   pp (tyCtx, e) = pp_partial (tyCtx, e) (tyCtx, e)
   pp_partial (tyCtx, expr) (eq tyCtx -> True, expr') =
      let pp_partial' = partial_parensOpt tyCtx expr in -- doesn't matter if we use expr or expr' as the parent
      case (expr, expr') of
         (EVar x, EVar (eq x -> True)) -> text $ show x
         (ELet x e1 e2, ELet (eq x -> True) e1' e2') ->
            sep [text strLet <+> pp_partial_binding tyCtx x Nothing,
                 nest indent $ text "=" <+> pp_partial' e1 e1' <+> text strIn] $$
            pp_partial' e2 e2'
         (EUnit, EUnit) -> text strUnitVal
         (EBool b, EBool (eq b -> True)) -> text (show b)
         (EIf e e1 e2, EIf e' e1' e2') ->
            text strIf <+> pp_partial' e e'
                $$ text strThen <+> pp_partial' e1 e1'
                $$ text strElse <+> pp_partial' e2 e2'
         (EInt n, EInt (eq n -> True)) -> text (show n)
         -- Only support binary ops for now. Deal with other cases as they arise.
         (EOp f l1, EOp (eq f -> True) l2) ->
             case (l1, l2) of
               ([e1,e2], [e1',e2']) -> pp_partial' e1 e1' <+> pp f <+> pp_partial' e2 e2'
               _ -> error "Resugaring of unary operators not supported"
         (EPair e1 e2, EPair e1' e2') ->
            parens $ sep [pp_partial' e1 e1' <> text ",", pp_partial' e2 e2']
         (EFst e, EFst e') -> text strFst <+> pp_partial' e e'
         (ESnd e, ESnd e') -> text strSnd <+> pp_partial' e e'
         (EInL e, EInL e') -> text strInL <+> pp_partial' e e'
         (EInR e, EInR e') -> text strInR <+> pp_partial' e e'
         (ECase (EUnroll (Just tv) e) (Match (x1, e1) (x2, e2)),
          ECase (EUnroll (eq (Just tv) -> True) e') (Match (eq x1 -> True, e1') (eq x2 -> True, e2'))) ->
            let [c1, c2] = A.getConstrs tyCtx tv in
            text strCase <+> pp_partial' e e' <+> text strOf $$
            pp_partial_caseClause c1 x1 e1 e1' $$
            pp_partial_caseClause c2 x2 e2 e2'
         (EFun _, EFun _) -> pp_partial_multiFun expr expr'
         (EApp _ _, EApp _ _) -> pp_partial_multiApp expr expr'
         -- Explicit rolls (unassociated with desugared constructors) are not supported.
         -- Use the inL/inR as the 'parent' for influencing parenthesisation (compatible with
         -- how a constructor should behave).
         (ERoll (Just tv) (EInL e), ERoll (eq (Just tv) -> True) (EInL e')) ->
            pp_partial_constr tyCtx (EInL e) (A.getConstrs tyCtx tv !! 0) e e'
         (ERoll (Just tv) (EInR e), ERoll (eq (Just tv) -> True) (EInR e')) ->
            pp_partial_constr tyCtx (EInR e) (A.getConstrs tyCtx tv !! 1) e e'
         -- Explicit unrolls (unassociated with desugared scrutinees) also not unsupported.
         (EHole, EHole) -> colorise "Gray" hole
         t -> error $ show t

      where
         hole :: Doc
         hole = if forLaTeX
                then text "{$\\square$}"
                else text "_"
         -- This breaks if the body calls any of the functions other than the outermost
         -- recursively, but I guess that's very rare. (You'll end up with a function
         -- being mentioned whose syntax isn't visible.) Really we should only treat "anonymous"
         -- functions in this way, but this will do for now.
         pp_partial_multiFun :: Exp -> Exp -> Doc
         pp_partial_multiFun fun@(EFun (Rec f _ _ _))
                             fun'@(EFun (Rec (eq f -> True) _ _ _)) =
            let
               (xs, (e1, e1')) = multiFun fun fun' in
               sep [
                  text strFun <+> pp_partial_binding tyCtx f Nothing
                              <+> (hsep $ map (parens . flip (pp_partial_binding tyCtx) Nothing) xs)
                              <+> text strFunBodySep,
                  nest indent $ partial_parensOpt tyCtx fun e1 e1' -- doesn't matter whether we use fun or fun'
               ]
            where
               multiFun :: Exp -> Exp -> ([Var], (Exp, Exp))
               multiFun (EFun (Rec _ x body _)) (EFun (Rec _ (eq x -> True) body' _)) =
                  case (body, body') of
                     (EFun _, EFun _) -> first (x :) $ multiFun body body'
                     _ -> ([x], (body, body'))
               multiFun _ _ =
                   error "Pretty-printing error: incorrect multiFun arguments"
         pp_partial_multiFun _ _ =
                   error "Pretty-printing error: incorrect pp_partial_multiFun arguments"

         pp_partial_multiApp :: Exp -> Exp -> Doc
         pp_partial_multiApp exp_e exp_e' =
            let ((e1, e1'), es) = multiApp exp_e exp_e' in
               sep $ partial_parensOpt tyCtx exp_e e1 e1' :
                       (map (nest indent . (uncurry $ partial_parensOpt tyCtx exp_e)) es)
            where
               -- Returns the "leaf" function and a list of arguments.
               multiApp :: Exp -> Exp -> ((Exp, Exp), [(Exp, Exp)])
               multiApp (EApp e1 e2) (EApp e1' e2') =
                  case (e1, e1') of
                     (EApp _ _, EApp _ _) -> second (flip (++) [(e2, e2')]) $ multiApp e1 e1'
                     _ -> ((e1, e1'), [(e2, e2')])
               multiApp _ _ =
                   error "Pretty-printing error: incorrect multiApp arguments"

         pp_partial_caseClause :: A.Con -> Var -> Exp -> Exp -> Doc
         pp_partial_caseClause c x exp_e exp_e' =
            let varOpt = if x == bot then empty else pp_partial_binding tyCtx x Nothing in
               nest indent (sep [
                  (text $ show c) <+> varOpt <+> text strCaseClauseSep,
                  nest indent $ pp_partial (tyCtx, exp_e) (tyCtx, exp_e')
               ])

   pp_partial _ _ = error "Pretty-printing error: (TyCtx, Exp)"

pp_partial_binding :: A.TyCtx -> Var -> Maybe (Value, Value) -> Doc
pp_partial_binding tyCtx x v_opt =
   let var = underline (pp x) in
   case v_opt of
      Just (v, v') -> var <> (text "." <> pp_partial (tyCtx, v) (tyCtx, v'))
      Nothing -> var

pp_partial_constr :: Container a => A.TyCtx -> a -> A.Con -> a -> a -> Doc
pp_partial_constr tyCtx parent c e e' =
   let arg =
         if (fst $ A.constrmap tyCtx Map.! c) == A.UnitTy
         then empty
         else nest indent $ partial_parensOpt tyCtx parent e e' in
   sep [text $ show c, arg]

-- Assert that y == x. For use as a view pattern.
eq :: (Eq a, Show a) => a -> a -> Bool
eq x y = if x == y then True else error $ "Found " ++ show y ++ ", expected "++ show x

-- DEAD CODE: This code was commented out from PP Exp instance after a separate
-- data type for traces was created.  This code is here temporarily until this
-- whole module gets rewritten.

{-
instance Container Trace where
   container (Exp e)          = container e
   container (CaseL _ _ _ _)  = True
   container (CaseR _ _ _ _)  = True
   container (IfThen _ _ _ _) = True
   container (IfElse _ _ _ _) = True
   container (Call _ _ _ _)   = True

   parenth _ = True

instance PP (A.TyCtx, Trace) where
   pp (tyCtx, e) = pp_partial (tyCtx, e) (tyCtx, e)
   pp_partial (tyCtx, expr) (eq tyCtx -> True, expr') =
      let pp_partial' = partial_parensOpt tyCtx expr in -- doesn't matter if we use expr or expr' as the parent
      case (expr, expr') of
         (IfThen e _ e2 t1, IfThen e' _ e2' t1') ->
            text strIf <+> pp_partial' e e'
                $$ text strThen <+> pp_partial' t1 t1'
                $$ text strElse <+> pp_partial' e2 e2'
         (IfElse e e1 _ t2, IfElse e' e1' _ t2') ->
            text strIf <+> pp_partial' e e'
                $$ text strThen <+> pp_partial' e1 e1'
                $$ text strElse <+> pp_partial' t2 t2'
         (CaseL (Unroll (Just tv) t) (Match (x1, _) _) _ t1,
          CaseL (Unroll (eq (Just tv) -> True) t') (Match (eq x1 -> True, _) _) _ t1') ->
            let [c1, _] = A.getConstrs tyCtx tv in
            text strCase <+> pp_partial' t t' <+> text strOf <+> pp_partial_ctrPattern c1 x1 $$
            (nest indent $ pp_partial' t1 t1')
         (CaseR (Unroll (Just tv) t) (Match _ (x2, _)) _ t2,
          CaseR (Unroll (eq (Just tv) -> True) t') (Match _ (eq x2 -> True, _)) _ t2') ->
            let [_, c2] = A.getConstrs tyCtx tv in
            text strCase <+> pp_partial' t t' <+> text strOf <+> pp_partial_ctrPattern c2 x2 $$
            (nest indent $ pp_partial' t2 t2')
         (Call _ _ _ _, Call _ _ _ _) ->
            pp_partial_multiCall expr expr'

      where

         -- TODO: factor out commonality with pp_partial_caseClause.
         pp_partial_ctrPattern :: A.Con -> Var -> Doc
         pp_partial_ctrPattern c x =
            let varOpt = if x == bot then empty else pp_partial_binding tyCtx x Nothing in
               colorise "Mulberry" (text $ show c) <+> varOpt <+> text strCaseClauseSep

         pp_partial_multiCall :: Trace -> Trace -> Doc
         pp_partial_multiCall t@(Call t1 t2 _ (Rec _ x t3 _))
                              (Call t1' t2' _ (Rec _ (eq x -> True) t3' _)) =
            let ((t1_, t1_'), ts) = multiCall t1 t1' in
               sep [

                  colorise "RoyalBlue" $ partial_parensOpt tyCtx t t1_ t1_',
                  nest indent $ vcat $ map pp_partial_call $ ts ++ [((x, (t2, t2')), (t3, t3'))]
               ]
            where
               pp_partial_call :: ((Var, (Exp, Exp)), (Exp, Exp)) -> Doc
               pp_partial_call ((exp_x, (exp_t2, exp_t2')), (exp_t3, exp_t3')) =
                  sep $
                     [ sep [ pp_partial_binding tyCtx exp_x Nothing
                         , nest indent $ text "=" <+>
                           partial_parensOpt tyCtx t exp_t2 exp_t2'
                         ]
                     ] ++ body
                  where
                     body = case (exp_t3, exp_t3') of
                        (Fun _, Fun _) -> []
                        -- Gratuitous indentation hack :-/
                        _ -> [nest (-indent) $ text strFunBodySep <+>
                                               partial_parensOpt tyCtx t t3 t3']
         pp_partial_multiCall _ _ =
             error "Pretty-printing error: incorrect multiCall arguments"

         multiCall :: Trace -> Trace -> ((Exp, Exp), [((Var, (Exp, Exp)), (Exp, Exp))])
         multiCall t t' =
            case (t, t') of
               (Call t1 t2 _ (Rec _ x t3 _), Call t1' t2' _ (Rec _ (eq x -> True) t3' _)) ->
                  second (flip (++) [((x, (t2, t2')), (t3, t3'))]) $ multiCall t1 t1'
               _ -> ((t, t'), [])
-}
