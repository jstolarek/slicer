{-# LANGUAGE DeriveAnyClass   #-}
{-# LANGUAGE DeriveGeneric    #-}

module Language.Slicer.Resugar
    ( RExp, resugar
    )  where

import           Language.Slicer.Absyn ( Con, TyCtx, getTyDeclByName
                                       , conL, conR )
import           Language.Slicer.Core
import           Language.Slicer.Env
import           Language.Slicer.Error
import           Language.Slicer.Monad
import           Language.Slicer.Monad.Desugar
import           Language.Slicer.Primitives
import           Language.Slicer.UpperSemiLattice

import           Control.DeepSeq ( NFData  )
import           GHC.Generics    ( Generic )
import           Text.PrettyPrint.HughesPJClass

-- See GitHub ticket #10 and pull request #20 for discussion and thoughts on
-- possible improvements to the resugaring mechanism

data RExp = RVar Var | RLet Var RExp RExp
          | RUnit
          | RBool Bool | RIf RExp RExp RExp
          | RInt Int | ROp Primitive [RExp]
          | RString String
          | RPair RExp RExp | RFst RExp | RSnd RExp
          | RCon Con RExp | RCase RExp RMatch
          | RFun RCode | RApp RExp RExp
          | RTrace RExp
          | RHole
          -- References
          | RRef RExp | RDeref RExp | RAssign RExp RExp | RSeq RExp RExp
          -- Exceptions
          | RRaise RExp | RCatch RExp Var RExp | RException
            deriving (Show, Eq, Ord, Generic, NFData)

data RCode = RRec Var [Var] RExp -- name, args, body
             deriving (Show, Eq, Ord, Generic, NFData)

data RMatch = RMatch [ ( Con, Maybe Var, RExp ) ]
              deriving (Show, Eq, Ord, Generic, NFData)

resugar :: Resugarable a => TyCtx -> a -> SlM RExp
resugar decls expr = runDesugarM decls emptyEnv (resugarM expr)

-- | Class of things that can be resugared into surface syntax
class Resugarable a where
   resugarM :: a -> DesugarM RExp

instance (Resugarable a, AskConstrs a, Show a) => Resugarable (Syntax a) where
    resugarM (Var v) = return (RVar v)
    resugarM (Let v e1 e2)
        = do e1' <- resugarM e1
             e2' <- resugarM e2
             return (RLet v e1' e2')
    resugarM  Unit = return RUnit
    resugarM (CBool   b) = return (RBool   b)
    resugarM (CInt    i) = return (RInt    i)
    resugarM (CString s) = return (RString s)
    resugarM (Op f args)
        = do args' <- mapM resugarM args
             return (ROp f args')
    resugarM (Pair e1 e2)
        = do e1' <- resugarM e1
             e2' <- resugarM e2
             return (RPair e1' e2')
    resugarM (Fst e)
        = do e' <- resugarM e
             return (RFst e')
    resugarM (Snd e)
        = do e' <- resugarM e
             return (RSnd e')
    resugarM (Roll dataty e) | Just e' <- maybeInL e
        = do e'' <- resugarM e'
             decls <- getDecls
             case getTyDeclByName decls dataty of
               Just decl -> return (RCon (conL decl) e'')
               Nothing -> resugarError ("Unknown data type: " ++ show dataty)
    resugarM (Roll dataty e) | Just e' <- maybeInR e
        = do e'' <- resugarM e'
             decls <- getDecls
             case getTyDeclByName decls dataty of
               Just decl -> return (RCon (conR decl) e'')
               Nothing -> resugarError ("Unknown data type: " ++ show dataty)
    resugarM (Fun code@(Rec name' _ _ _))
        = -- Functions in Core are single-argument.  Need to traverse body to
          -- reconstruct multi-argument functions
          do let (args, body) = resugarMultiFun code
             body' <- resugarM body
             return (RFun (RRec name' (reverse args) body'))
    resugarM  Hole = return RHole
    resugarM (Seq e1 e2)
        = do e1' <- resugarM e1
             e2' <- resugarM e2
             return (RSeq e1' e2')
    -- These should never happen in a well-formed program
    resugarM (InL e)
        = resugarError ("Left data constructor not wrapped in roll, can't resugar "
                        ++ show e)
    resugarM (InR e)
        = resugarError ("Right data constructor not wrapped in roll, can't resugar "
                        ++ show e)
    resugarM (Roll _ e)
        = resugarError ("Non-constructor expression wrapped in a roll, can't resugar "
                        ++ show e)
    resugarM (Unroll _ e)
        = resugarError ("Unroll outside of case scrutinee, can't resugar "
                        ++ show e)

instance Resugarable Exp where
    resugarM (EIf c e1 e2)
        = do c'  <- resugarM c
             e1' <- resugarM e1
             e2' <- resugarM e2
             return (RIf c' e1' e2')
    resugarM (ECase (EUnroll dataty e) (Match alt1 alt2))
        = do e' <- resugarM e
             m' <- resugarMatch dataty alt1 alt2
             return (RCase e' m')
    resugarM (ECase e _)
        = resugarError ("Case scrutinee not wrapped in unroll, can't resugar "
                        ++ show e)
    resugarM (EApp e1 e2)
        = do e1' <- resugarM e1
             e2' <- resugarM e2
             return (RApp e1' e2')
    resugarM (ETrace e)
        = do e' <- resugarM e
             return (RTrace e')
    resugarM (ERef e)
        = do e' <- resugarM e
             return (RRef e')
    resugarM (EDeref e)
        = do e' <- resugarM e
             return (RDeref e')
    resugarM (EAssign e1 e2)
        = do e1' <- resugarM e1
             e2' <- resugarM e2
             return (RAssign e1' e2')
    resugarM (ERaise e)
        = do e' <- resugarM e
             return (RRaise e')
    resugarM (ECatch e x h)
        = do e' <- resugarM e
             h' <- resugarM h
             return (RCatch e' x h')
    resugarM (Exp e) = resugarM e

instance Resugarable Trace where
    resugarM (TIfThen tc t1)
        = do tc' <- resugarM tc
             t1' <- resugarM t1
             return (RIf tc' t1' RHole)
    resugarM (TIfElse tc t2)
        = do tc' <- resugarM tc
             t2' <- resugarM t2
             return (RIf tc' RHole t2')
    resugarM (TIfExn tc)
        = do tc' <- resugarM tc
             return (RIf tc' RHole RHole)
    resugarM (TCaseL (TUnroll dataty t) v tl)
        = do t' <- resugarM t
             m' <- resugarMatch dataty (v, tl) (Just bot, THole)
             return (RCase t' m')
    resugarM (TCaseL e _ _)
        = resugarError ("TCaseL scrutinee not wrapped in unroll, can't resugar "
                        ++ show e)
    resugarM (TCaseR (TUnroll dataty t) v tr)
        = do t' <- resugarM t
             m' <- resugarMatch dataty (Just bot, THole) (v, tr)
             return (RCase t' m')
    resugarM (TCaseR e _ _)
        = resugarError ("TCaseR scrutinee not wrapped in unroll, can't resugar "
                        ++ show e)
    resugarM (TCall t1 t2 _ _)
        = do t1' <- resugarM t1
             t2' <- resugarM t2
             return (RApp t1' t2')
    resugarM (TCallExn t1 t2)
        = do t1' <- resugarM t1
             t2' <- resugarM t2
             return (RApp t1' t2')
    resugarM (TRef _ t)
        = do t' <- resugarM t
             return (RRef t')
    resugarM (TDeref _ t)
        = do t' <- resugarM t
             return (RDeref t')
    resugarM (TAssign _ t1 t2)
        = do t1' <- resugarM t1
             t2' <- resugarM t2
             return (RAssign t1' t2')
    resugarM (TRaise e)
        = do e' <- resugarM e
             return (RRaise e')
    resugarM (TTry t)
        = do t' <- resugarM t
             return (RCatch t' bot RHole)
    resugarM (TTryWith t x ht)
        = do t' <- resugarM t
             ht' <- resugarM ht
             return (RCatch t' x ht')
    resugarM (TExp e) = resugarM e


-- | Class of syntax trees that can contain InL or InR constructors.  We need
--   this in Resugarable instance for Syntax, because Syntax can be
--   parameterized by Exp or Trace and in the Roll case we need a uniform way of
--   pattern matching on InL/InR.
class AskConstrs a where
    maybeInL :: a -> Maybe a
    maybeInR :: a -> Maybe a

instance AskConstrs Exp where
    maybeInL (EInL e) = Just e
    maybeInL _        = Nothing

    maybeInR (EInR e) = Just e
    maybeInR _        = Nothing

instance AskConstrs Trace where
    maybeInL (TInL e) = Just e
    maybeInL _        = Nothing

    maybeInR (TInR e) = Just e
    maybeInR _        = Nothing

resugarMatch :: Resugarable a => TyVar -> (Maybe Var, a) -> (Maybe Var, a)
             -> DesugarM RMatch
resugarMatch dataty (v1, e1) (v2, e2)
    = do decls <- getDecls
         e1' <- resugarM e1
         e2' <- resugarM e2
         case getTyDeclByName decls dataty of
           Just decl ->
               return (RMatch [ ((conL decl), v1, e1')
                              , ((conR decl), v2, e2') ] )
           Nothing -> resugarError ("Unknown data type: " ++ show dataty)

resugarMultiFun :: Code Exp -> ([Var], Exp)
resugarMultiFun = go []
    where go :: [Var] -> Code Exp -> ([Var], Exp)
          go args (Rec _ arg (EFun code) _) = go (arg:args) code
          go args (Rec _ arg body        _) = (arg:args, body)

instance Resugarable Value where
    resugarM VHole       = return RHole
    resugarM VUnit       = return RUnit
    resugarM VException  = return RException
    resugarM (VBool b)   = return (RBool b)
    resugarM (VInt i)    = return (RInt i)
    resugarM (VString s) = return (RString s)
    resugarM (VPair v1 v2)
        = do e1 <- resugarM v1
             e2 <- resugarM v2
             return (RPair e1 e2)
    resugarM (VRoll dataty (VInL v))
        = do e <- resugarM v
             decls <- getDecls
             case getTyDeclByName decls dataty of
               Just decl -> return (RCon (conL decl) e)
               Nothing -> resugarError ("Unknown data type: " ++ show dataty)
    resugarM (VRoll dataty (VInR v))
        = do e <- resugarM v
             decls <- getDecls
             case getTyDeclByName decls dataty of
               Just decl -> return (RCon (conR decl) e)
               Nothing -> resugarError ("Unknown data type: " ++ show dataty)
    resugarM (VClosure v _) = resugarM (EFun v)
    resugarM (VExp v _)     = resugarM v
    resugarM (VTrace _ t _)
        = do e <- resugarM t
             return (RTrace e)
    resugarM (VInL v)
        = resugarError ("Left data value not wrapped in roll, can't resugar "
                        ++ show v)
    resugarM (VInR v)
        = resugarError ("Right data value not wrapped in roll, can't resugar "
                        ++ show v)
    resugarM (VRoll _ v)
        = resugarError ("Non-constructor value wrapped in a roll, can't resugar "
                        ++ show v)
    resugarM VStar
        = resugarError ("Don't know how to desugar stars. " ++
                        "Where did you get this value from?" )
    resugarM (VStoreLoc _)
        = resugarError ("Cannot resugar store labels")

instance Pretty RExp where
    pPrint RHole       = text "_"
    pPrint RUnit       = text "()"
    pPrint RException  = text "<exception>"
    pPrint (RInt    i) = int i
    pPrint (RString s) = text (show s)
    pPrint (RBool b)   = if b then text "true" else text "false"
    pPrint (RVar    x) = pPrint x
    pPrint (RLet x e1 e2)
        = text "let" <+> pPrint x <+> equals <+> pPrint e1 $$
          text "in" <+> pPrint e2
    pPrint (RIf e e1 e2)
        = text "if" <+> pPrint e
                $$ text "then" <+> pPrint e1
                $$ text "else" <+> pPrint e2
    pPrint (ROp f es)
        = case (isInfixOp f, es) of
            (True, [e1, e2]) ->
                partial_parensOpt e1  <+> pPrint f <+>
                partial_parensOpt e2
            _ -> pPrint f <> parens (hcat (punctuate comma (map pPrint es)))
    pPrint (RPair e1 e2)   = parens (pPrint e1 <> comma <+> pPrint e2)
    pPrint (RFst e)        = text "fst" <+> partial_parensOpt e
    pPrint (RSnd e)        = text "snd" <+> partial_parensOpt e
    -- Special case to handle nullary constructors
    pPrint (RCon c RUnit)  = text (show c)
    pPrint (RCon c e)      = text (show c) <+> partial_parensOpt e
    pPrint (RCase e m)     = text "case" <+> pPrint e <+> text "of" $$
                             nest 2 (pPrint m)
    pPrint (RFun k)        = pPrint k
    pPrint (RApp e1 e2)    = sep [ pPrint e1, pPrint e2 ]
    pPrint (RRef e)        = text "ref" <+> partial_parensOpt e
    pPrint (RDeref e)      = text "!" <> partial_parensOpt e
    pPrint (RAssign e1 e2) = pPrint e1 <+> text ":=" <+> pPrint e2
    pPrint (RSeq e1 e2)    = pPrint e1 <+> text ";;" <+> pPrint e2
    pPrint (RTrace e)      = text "trace" <+> partial_parensOpt e
    pPrint (RRaise e)      = text "raise" <+> partial_parensOpt e
    pPrint (RCatch e x h)  = text "try" $$ nest 2 (pPrint e) $$
                             text "with" <+> pPrint x <+> text "=>" $$
                             nest 2 (pPrint h)

instance Pretty RMatch where
    pPrint (RMatch ms) = vcat (punctuate semi (map pp_match ms))
        where pp_match (con, var, expr)
                  = text (show con) <+> pPrint var <+> text "->" <+>
                       pPrint expr

instance Pretty RCode where
    pPrint (RRec name args body)
        = text "fun" <+> pPrint name <+> sep (map pPrint args) <+> text "=>" <+>
          nest 2 (pPrint body)

parenth :: RExp -> Bool
parenth RHole       = False
parenth (RBool _)   = False
parenth (RInt _)    = False
parenth (RString _) = False
parenth RUnit       = False
parenth (RPair _ _) = False
parenth (RVar _)    = False
parenth (RDeref _)  = False
parenth _           = True

partial_parensOpt :: RExp -> Doc
partial_parensOpt e
    = let doc = pPrint e in
      if parenth e then parens doc else doc
