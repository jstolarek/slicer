{-# LANGUAGE DeriveAnyClass   #-}
{-# LANGUAGE DeriveGeneric    #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE UndecidableInstances   #-}

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
-- possible improvements to the resugaring mechanism.  See #24 for thoughts on
-- resugaring of error messages.

--------------------------------------------------------------------------------
--                   RESUGARED EXPRESSION LANGUAGE                            --
--------------------------------------------------------------------------------

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
          | RRaise RExp | RCatch RExp Var RExp | RException RExp
            deriving (Show, Eq, Ord, Generic, NFData)

data RCode = RRec Var [Var] RExp -- name, args, body
             deriving (Show, Eq, Ord, Generic, NFData)

data RMatch = RMatch [ ( Con, Maybe Var, RExp ) ]
              deriving (Show, Eq, Ord, Generic, NFData)


--------------------------------------------------------------------------------
--                            UNEVALUATION                                    --
--------------------------------------------------------------------------------

-- Unevaluation squashes a trace back down into an expression.  When resugaring
-- a trace it first gets unevaluated into an expression and then that expression
-- is resugared.  The benefit is that the fairly complicated logic of resugaring
-- is written only once at the expense of having to define a relatively simple
-- unevaluation logic.

class Uneval a b | a -> b where
    uneval :: a -> b

instance Uneval Trace Exp where
    uneval (TCaseL t x t1)   = ECase (uneval t) (Match (x, uneval t1) (bot, bot))
    uneval (TCaseR t x t2)   = ECase (uneval t) (Match (bot, bot) (x, uneval t2))
    uneval (TCaseExn t)      = ECase (uneval t) (Match (bot, bot) (bot,bot))
    uneval (TIfThen t t1)    = EIf (uneval t) (uneval t1) bot
    uneval (TIfElse t t2)    = EIf (uneval t) bot (uneval t2)
    uneval (TIfExn t)        = EIf (uneval t) bot bot
    uneval (TCall t1 t2 _ _) = EApp (uneval t1) (uneval t2)
    uneval (TCallExn t1 t2)  = EApp (uneval t1) (uneval t2)
    uneval (TRef _ t)        = ERef (uneval t)
    uneval (TDeref _ t)      = EDeref (uneval t)
    uneval (TAssign _ t1 t2) = EAssign (uneval t1) (uneval t2)
    uneval (TRaise t)        = ERaise (uneval t)
    uneval (TTry t)          = ETryWith (uneval t) bot bot
    uneval (TTryWith t x h)  = ETryWith (uneval t) x (uneval h)
    uneval (TExp expr)       = Exp (uneval expr)
    uneval (TSlicedHole _ _) = EHole

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
    uneval (Seq e1 e2)   = Seq (uneval e1) (uneval e2)

instance Uneval a b => Uneval (Code a) (Code b) where
    uneval (Rec name arg body label) = Rec name arg (uneval body) label


--------------------------------------------------------------------------------
--                             RESUGARING                                     --
--------------------------------------------------------------------------------

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
    resugarM (ETryWith e x h)
        = do e' <- resugarM e
             h' <- resugarM h
             return (RCatch e' x h')
    resugarM (Exp e) = resugarM e

instance Resugarable Trace where
    resugarM t = resugarM (uneval t)

instance Resugarable Value where
    resugarM VHole       = return RHole
    resugarM VUnit       = return RUnit
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
    resugarM (VTrace _ t _ _)
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
        = resugarError ("Don't know how to resugar stars. " ++
                        "Where did you get this value from?" )
    resugarM (VStoreLoc _)
        = resugarError ("Cannot resugar store labels")


instance Resugarable Outcome where
    resugarM OHole = return RHole
    resugarM (ORet v) = resugarM v
    resugarM (OExn v) = do e <- resugarM v
                           return (RRaise e) 
    resugarM OStar
        = resugarError ("Don't know how to resugar stars. " ++
                        "Where did you get this value from?" )


--------------------------------------------------------------------------------
--                      RESUGARING - HELPER FUNCTIONS                         --
--------------------------------------------------------------------------------

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


--------------------------------------------------------------------------------
--                  PRETTY PRINTING OF RESUGARED EXPRESSIONS                  --
--------------------------------------------------------------------------------

instance Pretty RExp where
    pPrint RHole       = text "_"
    pPrint RUnit       = text "()"
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
    pPrint (RException e)  = text "<exception>" <> partial_parensOpt e

instance Pretty RMatch where
    pPrint (RMatch ms) = vcat (punctuate semi (map pp_match ms))
        where pp_match (con, var, expr)
                  = text (show con) <+> pPrint var <+> text "->" <+>
                       pPrint expr

instance Pretty RCode where
    pPrint (RRec name args body)
        = text "fun" <+> pPrint name <+> sep (map pPrint args) <+> text "=>" <+>
          nest 2 (pPrint body)

-- | Should the expression be wrapped in parentheses?
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

-- | Pretty-print an expression, wrapping it in parentheses if necessary
partial_parensOpt :: RExp -> Doc
partial_parensOpt e
    = let doc = pPrint e in
      if parenth e then parens doc else doc
