{-# LANGUAGE FlexibleInstances, FlexibleContexts, TupleSections, ViewPatterns #-}

module Resugar where

import Control.Arrow hiding ((<+>))
import Control.Exception
import Data.Maybe
import qualified Data.Map as Map
import Text.PrettyPrint

import UpperSemiLattice
import Env
import qualified Absyn as A
import Trace
import UntypedParser -- for constants
--import LaTeX
import PrettyPrinting

-- Old stuff we're not using.

forLaTeX :: Bool
forLaTeX = True

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
      pp_partial (tyCtx, (env, Fun k)) (tyCtx, (env', Fun k'))
   pp_partial (tyCtx, v) (eq tyCtx -> True, v') =
      pp_partial (tyCtx, val2exp v) (tyCtx, val2exp v')

instance (Eq a, PP (A.TyCtx, a)) => PP (A.TyCtx, (Env Value, a)) where
   pp (tyCtx, (rho, e)) = pp_partial (tyCtx, (rho, e)) (tyCtx, (rho, e))
   pp_partial (tyCtx, ((== emptyEnv) -> True, e)) (eq tyCtx -> True, ((== emptyEnv) -> True, e')) =
      pp_partial (tyCtx, e) (tyCtx, e')
   pp_partial (tyCtx, (rho, e)) (eq tyCtx -> True, (rho', e')) =
      vcat [text strWith, nest indent $ pp_partial (tyCtx, rho) (tyCtx, rho') <+> text strIn] $$
      pp_partial (tyCtx, e) (tyCtx, e')

instance PP (A.TyCtx, Env Value) where
   pp (tyCtx, env) = pp_partial (tyCtx, env) (tyCtx, env)
   pp_partial (tyCtx, (== emptyEnv) -> True) (eq tyCtx -> True, (== emptyEnv) -> True) = empty
   pp_partial (tyCtx, Env rho) (eq tyCtx -> True, Env rho') =
      assert (Map.keys rho == Map.keys rho') $
      vcat $ punctuate comma $
             map (uncurry $ pp_partial_binding tyCtx) $
                 zipWith (\(x, v) (_, v') -> (x, Just (v, v'))) (Map.assocs rho) (Map.assocs rho')

instance Container Exp where
   -- Ignore trace operations for now.
   container (Let _ _ _) = True
   container (If _ _ _) = True
   container (IfThen _ _ _ _) = True
   container (IfElse _ _ _ _) = True
   container (Op _ _) = False
   container (Pair _ _) = True
   container (Fst _) = False
   container (Snd _) = False
   container (InL _) = False
   container (InR _) = False
   container (Case _ _) = True
   container (CaseL _ _ _ _) = True
   container (CaseR _ _ _ _) = True
   container (Fun _) = True
   container (App _ _) = False
   container (Call _ _ _ _) = True
   container (Roll _ _) = False
   container (Unroll _ _) = False

   parenth Hole = False
   parenth (CBool _) = False
   parenth (CInt _) = False
   parenth Unit = False
   parenth (Pair _ _) = False
   parenth (Var _) = False
   parenth _ = True


instance PP (A.TyCtx, Exp) where
   pp (tyCtx, e) = pp_partial (tyCtx, e) (tyCtx, e)
   pp_partial (tyCtx, e) (eq tyCtx -> True, e') =
      let pp_partial' = partial_parensOpt tyCtx e in -- doesn't matter if we use e or e' as the parent
      case (e, e') of
         (Var x, Var (eq x -> True)) -> text $ show x
         (Let x e1 e2, Let (eq x -> True) e1' e2') ->
            sep [text strLet <+> pp_partial_binding tyCtx x Nothing,
                 nest indent $ text "=" <+> pp_partial' e1 e1' <+> text strIn] $$
            pp_partial' e2 e2'
         (Unit, Unit) -> text strUnitVal
         (CBool b, CBool (eq b -> True)) -> text (show b)
         (If e e1 e2, If e' e1' e2') ->
            text strIf <+> pp_partial' e e'
                $$ text strThen <+> pp_partial' e1 e1'
                $$ text strElse <+> pp_partial' e2 e2'
         (IfThen e _ e2 t1, IfThen e' _ e2' t1') ->
            text strIf <+> pp_partial' e e'
                $$ text strThen <+> pp_partial' t1 t1'
                $$ text strElse <+> pp_partial' e2 e2'
         (IfElse e e1 _ t2, IfElse e' e1' _ t2') ->
            text strIf <+> pp_partial' e e'
                $$ text strThen <+> pp_partial' e1 e1'
                $$ text strElse <+> pp_partial' t2 t2'
         (CInt n, CInt (eq n -> True)) -> text (show n)
         -- Only support binary ops for now. Deal with other cases as they arise.
         (Op f l1, Op (eq f -> True) l2) ->
            (case (l1, l2)
             of ([e1,e2], [e1',e2']) -> pp_partial' e1 e1' <+> pp f <+> pp_partial' e2 e2')
         (Pair e1 e2, Pair e1' e2') ->
            parens $ sep [pp_partial' e1 e1' <> text ",", pp_partial' e2 e2']
         (Fst e, Fst e') -> text strFst <+> pp_partial' e e'
         (Snd e, Snd e') -> text strSnd <+> pp_partial' e e'
         (InL e, InL e') -> text strInL <+> pp_partial' e e'
         (InR e, InR e') -> text strInR <+> pp_partial' e e'
         (Case (Unroll (Just tv) e) (Match (x1, e1) (x2, e2)),
          Case (Unroll (eq (Just tv) -> True) e') (Match (eq x1 -> True, e1') (eq x2 -> True, e2'))) ->
            let [c1, c2] = A.getConstrs tyCtx tv in
            text strCase <+> pp_partial' e e' <+> text strOf $$
            pp_partial_caseClause c1 x1 e1 e1' $$
            pp_partial_caseClause c2 x2 e2 e2'
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
         (Fun _, Fun _) -> pp_partial_multiFun e e'
         (App _ _, App _ _) -> pp_partial_multiApp e e'
         -- Explicit rolls (unassociated with desugared constructors) are not supported.
         -- Use the inL/inR as the 'parent' for influencing parenthesisation (compatible with
         -- how a constructor should behave).
         (Call _ _ _ _, Call _ _ _ _) ->
            pp_partial_multiCall e e'
         (Roll (Just tv) (InL e), Roll (eq (Just tv) -> True) (InL e')) ->
            pp_partial_constr tyCtx (InL e) (A.getConstrs tyCtx tv !! 0) e e'
         (Roll (Just tv) (InR e), Roll (eq (Just tv) -> True) (InR e')) ->
            pp_partial_constr tyCtx (InR e) (A.getConstrs tyCtx tv !! 1) e e'
         -- Explicit unrolls (unassociated with desugared scrutinees) also not unsupported.
         (Hole, Hole) -> colorise "Gray" $ text $ "{$\\square$}"
         t -> error $ show t

      where
         -- This breaks if the body calls any of the functions other than the outermost
         -- recursively, but I guess that's very rare. (You'll end up with a function
         -- being mentioned whose syntax isn't visible.) Really we should only treat "anonymous"
         -- functions in this way, but this will do for now.
         pp_partial_multiFun :: Exp -> Exp -> Doc
         pp_partial_multiFun e@(Fun (Rec f _ _ _))
                             e'@(Fun (Rec (eq f -> True) _ _ _)) =
            let
               (xs, (e1, e1')) = multiFun e e' in
               sep [
                  text strFun <+> pp_partial_binding tyCtx f Nothing
                              <+> (hsep $ map (parens . flip (pp_partial_binding tyCtx) Nothing) xs)
                              <+> text strFunBodySep,
                  nest indent $ partial_parensOpt tyCtx e e1 e1' -- doesn't matter whether we use e or e'
               ]
            where
               multiFun :: Exp -> Exp -> ([Var], (Exp, Exp))
               multiFun (Fun (Rec _ x e _)) (Fun (Rec _ (eq x -> True) e' _)) =
                  case (e, e') of
                     (Fun _, Fun _) -> first (x :) $ multiFun e e'
                     _ -> ([x], (e, e'))

         pp_partial_multiApp :: Exp -> Exp -> Doc
         pp_partial_multiApp e e' =
            let ((e1, e1'), es) = multiApp e e' in
               sep $ partial_parensOpt tyCtx e e1 e1' : (map (nest indent . (uncurry $ partial_parensOpt tyCtx e)) es)
            where
               -- Returns the "leaf" function and a list of arguments.
               multiApp :: Exp -> Exp -> ((Exp, Exp), [(Exp, Exp)])
               multiApp (App e1 e2) (App e1' e2') =
                  case (e1, e1') of
                     (App _ _, App _ _) -> second (flip (++) [(e2, e2')]) $ multiApp e1 e1'
                     _ -> ((e1, e1'), [(e2, e2')])

         -- TODO: factor out commonality with pp_partial_caseClause.
         pp_partial_ctrPattern :: A.Con -> Var -> Doc
         pp_partial_ctrPattern c x =
            let varOpt = if x == bot then empty else pp_partial_binding tyCtx x Nothing in
               colorise "Mulberry" (text $ show c) <+> varOpt <+> text strCaseClauseSep

         pp_partial_caseClause :: A.Con -> Var -> Exp -> Exp -> Doc
         pp_partial_caseClause c x e e' =
            let varOpt = if x == bot then empty else pp_partial_binding tyCtx x Nothing in
               nest indent (sep [
                  (text $ show c) <+> varOpt <+> text strCaseClauseSep,
                  nest indent $ pp_partial (tyCtx, e) (tyCtx, e')
               ])

         pp_partial_multiCall :: Exp -> Exp -> Doc
         pp_partial_multiCall t@(Call t1 t2 _ (Rec _ x t3 _))
                              t'@(Call t1' t2' _ (Rec _ (eq x -> True) t3' _)) =
            let ((t1_, t1_'), ts) = multiCall t1 t1' in
               sep [

                  colorise "RoyalBlue" $ partial_parensOpt tyCtx t t1_ t1_',
                  nest indent $ vcat $ map pp_partial_call $ ts ++ [((x, (t2, t2')), (t3, t3'))]
               ]
            where
               pp_partial_call :: ((Var, (Exp, Exp)), (Exp, Exp)) -> Doc
               pp_partial_call ((x, (t2, t2')), (t3, t3')) =
                  sep $ [
                     sep [pp_partial_binding tyCtx x Nothing, nest indent $ text "=" <+> partial_parensOpt tyCtx t t2 t2']
                  ] ++ body
                  where
                     body = case (t3, t3') of
                        (Fun _, Fun _) -> []
                        -- Gratuitous indentation hack :-/
                        _ -> [nest (-indent) $ text strFunBodySep <+> partial_parensOpt tyCtx t t3 t3']

         multiCall :: Exp -> Exp -> ((Exp, Exp), [((Var, (Exp, Exp)), (Exp, Exp))])
         multiCall t t' =
            case (t, t') of
               (Call t1 t2 _ (Rec _ x t3 _), Call t1' t2' _ (Rec _ (eq x -> True) t3' _)) ->
                  second (flip (++) [((x, (t2, t2')), (t3, t3'))]) $ multiCall t1 t1'
               _ -> ((t, t'), [])

pp_partial_binding :: A.TyCtx -> Var -> Maybe (Value, Value) -> Doc
pp_partial_binding tyCtx x v_opt =
   let var = underline (pp x) in
   case v_opt of
      Just (v, v') -> var <> (text "." <> pp_partial (tyCtx, v) (tyCtx, v'))
      Nothing -> var

pp_partial_constr :: (PP (A.TyCtx, a), Container a) => A.TyCtx -> a -> A.Con -> a -> a -> Doc
pp_partial_constr tyCtx parent c e e' =
   let arg =
         if (fst $ A.constrmap tyCtx Map.! c) == [A.UnitTy]
         then empty
         else nest indent $ partial_parensOpt tyCtx parent e e' in
   sep [text $ show c, arg]

-- Assert that y == x. For use as a view pattern.
eq :: (Eq a, Show a) => a -> a -> Bool
eq x y = if x == y then True else error $ "Found " ++ show y ++ ", expected "++ show x
