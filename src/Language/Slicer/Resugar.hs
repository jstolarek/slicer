module Language.Slicer.Resugar
    ( resugar, resugarValue
    )  where

import           Language.Slicer.Absyn ( Con, TyCtx, getTyDeclByName
                                       , conL, conR )
import           Language.Slicer.Core
import           Language.Slicer.Env
import           Language.Slicer.Error
import           Language.Slicer.Monad
import           Language.Slicer.Monad.Desugar
import           Language.Slicer.Primitives
import           Language.Slicer.PrettyPrinting

import           Text.PrettyPrint

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
            deriving (Eq,Show,Ord)

data RCode = RRec Var [Var] RExp -- name, args, body
             deriving (Eq,Show,Ord)

data RMatch = RMatch [ ( Con, Maybe Var, RExp ) ]
              deriving (Eq,Show,Ord)

resugar :: TyCtx -> Exp -> SlM RExp
resugar decls expr = runDesugarM decls emptyEnv (resugarM expr)

resugarValue :: TyCtx -> Value -> SlM RExp
resugarValue decls val = runDesugarM decls emptyEnv (resugarValueM val)

resugarM :: Exp -> DesugarM RExp
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
-- Functions in Core are single-argument.  Need to traverse body to reconstruct
-- multi-argument function
resugarM (EFun code@(Rec name' _ _ _))
    = do let (args, body) = resugarMultiFun code
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
-- This should never happen but it seems that GHC exhaustiveness checker does
-- not recognize that
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


resugarValueM :: Value -> DesugarM RExp
resugarValueM VHole = return RHole
resugarValueM VUnit = return RUnit
resugarValueM (VBool b) = return (RBool b)
resugarValueM (VInt i)  = return (RInt i)
resugarValueM (VString s) = return (RString s)
resugarValueM (VPair v1 v2)
    = do e1 <- resugarValueM v1
         e2 <- resugarValueM v2
         return (RPair e1 e2)
resugarValueM (VRoll dataty (VInL v))
    = do e <- resugarValueM v
         decls <- getDecls
         case getTyDeclByName decls dataty of
           Just decl -> return (RCon (conL decl) e)
           Nothing -> resugarError ("Unknown data type: " ++ show dataty)
resugarValueM (VRoll dataty (VInR v))
    = do e <- resugarValueM v
         decls <- getDecls
         case getTyDeclByName decls dataty of
           Just decl -> return (RCon (conR decl) e)
           Nothing -> resugarError ("Unknown data type: " ++ show dataty)
resugarValueM (VClosure v _) = resugarM (EFun v)
resugarValueM (VStoreLoc _)  = return RRef
resugarValueM (VExp v _)     = resugarM v
resugarValueM (VTrace v _ _)
    = do e <- resugarValueM v
         return (RTrace e)
resugarValueM (VInL v)
    = resugarError ("Left data value not wrapped in roll, can't resugar "
                    ++ show v)
resugarValueM (VInR v)
    = resugarError ("Right data value not wrapped in roll, can't resugar "
                    ++ show v)
resugarValueM (VRoll _ v)
    = resugarError ("Non-constructor value wrapped in a roll, can't resugar "
                    ++ show v)
resugarValueM VStar
    = resugarError ("Don't know how to desugar stars. " ++
                    "Where did you get this value from?" )

instance PP RExp where
    pp e = pp_partial e e

    pp_partial RHole RHole = text "_"
    pp_partial RHole e     = sb (pp e)
    pp_partial RUnit RUnit = text "()"
    pp_partial (RInt    i) (RInt    i') | i == i' = int i
    pp_partial (RString s) (RString s') | s == s' = text (show s)
    pp_partial (RVar    x) (RVar    x') | x == x' = pp x
    pp_partial (RLet x e1 e2) (RLet x' e1' e2')
        | x == x'
        = text "let" <+> pp x <+> equals <+> pp_partial e1 e1' $$
          text "in" <+> pp_partial e2 e2'
    pp_partial (RBool b) (RBool b')
        | b == b'
        = if b then text "true" else text "false"
    pp_partial (RIf e e1 e2) (RIf e' e1' e2')
        = text "if" <+> pp_partial e e'
                $$ text "then" <+> pp_partial e1 e1'
                $$ text "else" <+> pp_partial e2 e2'
    pp_partial (ROp f es) (ROp f' es')
        | f == f'
        = case (isInfixOp f, es, es') of
            (True, [e1, e2], [e1', e2']) ->
                partial_parensOpt e1 e1' <+> pp f <+>
                partial_parensOpt e2 e2'
            _ -> pp f <> parens (hcat (punctuate comma
                                                (zipWith pp_partial es es')))
    pp_partial (RPair e1 e2) (RPair e1' e2')
        = parens (pp_partial e1 e1' <> comma <+> pp_partial e2 e2')
    pp_partial (RFst e) (RFst e') = text "fst" <+> partial_parensOpt e e'
    pp_partial (RSnd e) (RSnd e') = text "snd" <+> partial_parensOpt e e'
    -- Special case to handle nullary constructors
    pp_partial (RCon c RUnit) (RCon c' RUnit)
        | c == c'
        = text (show c)
    pp_partial (RCon c e) (RCon c' e')
        | c == c'
        = text (show c) <+> partial_parensOpt e e'
    pp_partial (RCase e m) (RCase e' m')
        = text "case" <+> pp_partial e e' <+> text "of" $$
          nest 2 ( pp_partial m m')
    pp_partial (RFun k) (RFun k') = pp_partial k k'
    pp_partial (RApp e1 e2) (RApp e1' e2')
        = sep [ pp_partial e1 e1', pp_partial e2 e2' ]
    pp_partial RRef RRef
        = text "<ref>"
    pp_partial (RDeref e) (RDeref e')
        = text "!" <> partial_parensOpt e e'
    pp_partial (RAssign e1 e2) (RAssign e1' e2')
        = pp_partial e1 e1' <+> text ":=" <+> pp_partial e2 e2'
    pp_partial (RSeq e1 e2) (RSeq e1' e2')
        = pp_partial e1 e1' <+> text ";;" <+> pp_partial e2 e2'
    pp_partial (RTrace e) (RTrace e')
        = text "trace" <+> partial_parensOpt e e'
    pp_partial e e' = error ("Error pretty-printing resugared expression: e is "
                             ++ show e ++ " and e' is " ++ show e')

instance PP RMatch where
    pp_partial (RMatch ms) (RMatch ms') =
        vcat (punctuate semi (zipWith pp_match ms ms'))
        where pp_match (con, var, expr) (_, var', expr')
                   = text (show con) <+> pp_partial var var' <+> text "->" <+>
                     pp_partial expr expr'

instance PP RCode where
    pp_partial (RRec n args body) (RRec n' args' body')
        | n == n' && args == args'
        = text "fun" <+> pp n <+> sep (map pp args) <+> text "=>" <+>
          nest 2 (pp_partial body body')
    pp_partial v v' = error ("Error pretty-printing RCode: v is " ++ show v ++
                             " and v' is " ++ show v')

parenth :: RExp -> Bool
parenth RHole         = False
parenth (RBool _)     = False
parenth (RInt _)      = False
parenth (RString _)   = False
parenth RUnit         = False
parenth (RPair _ _)   = False
parenth (RVar _)      = False
parenth (RDeref _)    = False
parenth _             = True

partial_parensOpt :: RExp -> RExp -> Doc
partial_parensOpt e1 e1' =
   let doc = pp_partial e1 e1' in
   if parenth e1 then parens doc else doc
