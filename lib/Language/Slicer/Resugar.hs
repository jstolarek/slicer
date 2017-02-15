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
          -- References
          | RRef | RDeref RExp | RAssign RExp RExp | RSeq RExp RExp
          | RTrace RExp
          -- holes
          | RHole
            deriving (Show, Eq, Ord, Generic, NFData)

data RCode = RRec Var [Var] RExp -- name, args, body
             deriving (Show, Eq, Ord, Generic, NFData)

data RMatch = RMatch [ ( Con, Maybe Var, RExp ) ]
              deriving (Show, Eq, Ord, Generic, NFData)

resugar :: Resugarable a => TyCtx -> a -> SlM RExp
resugar decls expr = runDesugarM decls emptyEnv (resugarM expr)

class Resugarable a where
   resugarM :: a -> DesugarM RExp

instance Resugarable Exp where
    resugarM (EVar v) = return (RVar v)
    resugarM (ELet v e1 e2) = do e1' <- resugarM e1
                                 e2' <- resugarM e2
                                 return (RLet v e1' e2')
    resugarM  EUnit = return RUnit
    resugarM (EBool   b) = return (RBool   b)
    resugarM (EInt    i) = return (RInt    i)
    resugarM (EString s) = return (RString s)
    resugarM (EOp f args) = do args' <- mapM resugarM args
                               return (ROp f args')
    resugarM (EPair e1 e2) = do e1' <- resugarM e1
                                e2' <- resugarM e2
                                return (RPair e1' e2')
    resugarM (EFst e) = do e' <- resugarM e
                           return (RFst e')
    resugarM (ESnd e) = do e' <- resugarM e
                           return (RSnd e')
    resugarM (EIf c e1 e2) = do c'  <- resugarM c
                                e1' <- resugarM e1
                                e2' <- resugarM e2
                                return (RIf c' e1' e2')
    resugarM (ECase (EUnroll dataty e) m)
        = do e' <- resugarM e
             m' <- resugarMatch dataty m
             return (RCase e' m')
    resugarM (ECase e _)
        = resugarError ("Case scrutinee not wrapped in unroll, can't resugar "
                        ++ show e)
    resugarM (ERoll dataty (EInL e))
        = do e' <- resugarM e
             decls <- getDecls
             case getTyDeclByName decls dataty of
               Just decl -> return (RCon (conL decl) e')
               Nothing -> resugarError ("Unknown data type: " ++ show dataty)
    resugarM (ERoll dataty (EInR e))
        = do e' <- resugarM e
             decls <- getDecls
             case getTyDeclByName decls dataty of
               Just decl -> return (RCon (conR decl) e')
               Nothing -> resugarError ("Unknown data type: " ++ show dataty)
    resugarM (EFun code@(Rec name' _ _ _))
        = -- Functions in Core are single-argument.  Need to traverse body to
          -- reconstruct multi-argument functions
          do let (args, body) = resugarMultiFun code
             body' <- resugarM body
             return (RFun (RRec name' (reverse args) body'))
    resugarM (EApp e1 e2)  = do e1' <- resugarM e1
                                e2' <- resugarM e2
                                return (RApp e1' e2')
    resugarM EHole      = return RHole
    resugarM (ETrace e) = do e' <- resugarM e
                             return (RTrace e')
    resugarM (ERef _)   = return RRef
    resugarM (EDeref e) = do e' <- resugarM e
                             return (RDeref e')
    resugarM (EAssign e1 e2) = do e1' <- resugarM e1
                                  e2' <- resugarM e2
                                  return (RAssign e1' e2')
    resugarM (ESeq e1 e2) = do e1' <- resugarM e1
                               e2' <- resugarM e2
                               return (RSeq e1' e2')
    -- These should never happen in a well-formed program
    resugarM (EInL e)
        = resugarError ("Left data constructor not wrapped in roll, can't resugar "
                        ++ show e)
    resugarM (EInR e)
        = resugarError ("Right data constructor not wrapped in roll, can't resugar "
                        ++ show e)
    resugarM (ERoll _ e)
        = resugarError ("Non-constructor expression wrapped in a roll, can't resugar "
                        ++ show e)
    resugarM (EUnroll _ e)
        = resugarError ("Unroll outside of case scrutinee, can't resugar "
                        ++ show e)
    -- This should never happen but it seems that GHC exhaustiveness checker
    -- does not recognize that
    resugarM e = error ("Impossible happened during resugaring: " ++ show e)

resugarMatch :: TyVar -> Match -> DesugarM RMatch
resugarMatch dataty (Match (v1, e1) (v2, e2))
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
    resugarM VHole = return RHole
    resugarM VUnit = return RUnit
    resugarM (VBool b) = return (RBool b)
    resugarM (VInt i)  = return (RInt i)
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
    resugarM (VStoreLoc _)  = return RRef
    resugarM (VExp v _)     = resugarM v
    resugarM (VTrace v _ _)
        = do e <- resugarM v
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
    pPrint RRef            = text "<ref>"
    pPrint (RDeref e)      = text "!" <> partial_parensOpt e
    pPrint (RAssign e1 e2) = pPrint e1 <+> text ":=" <+> pPrint e2
    pPrint (RSeq e1 e2)    = pPrint e1 <+> text ";;" <+> pPrint e2
    pPrint (RTrace e)      = text "trace" <+> partial_parensOpt e

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
