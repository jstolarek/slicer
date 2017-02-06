{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE UndecidableInstances   #-}

module Language.Slicer.Core
    ( -- * Abstract syntax
      Syntax(..), Value(..), Type(..), Ctx, Code(..), Match(..)
    , Exp( EVar, ELet, EUnit, EBool, EInt, EOp, EString, EPair, EFst, ESnd
         , EInL, EInR, EFun, ERoll, EUnroll, EHole, ERef, EDeref, EAssign, ESeq
         , .. )
    , Trace ( TVar, TLet, TUnit, TBool, TInt, TOp, TString, TPair, TFst, TSnd
            , TInL, TInR, TFun, TRoll, TUnroll, THole, TRef, TDeref, TAssign
            , TSeq, .. )

    -- * Helper functions for AST
    , isRefTy, isFunTy

    , Pattern(extract)

      -- * Built-in operators
    , commonOps, intBinOps, intRelOps, boolRelOps, boolUnOps
    , isCommonOp, isIntBinOp, isIntRelOp, isBoolRelOp, isBoolUnOp

      -- * Lables
    , Lab( unL ), mkL

      -- * Free variables
    , FVs(..)
    ) where


import           Language.Slicer.Env
import           Language.Slicer.PrettyPrinting
import           Language.Slicer.Primitives
import           Language.Slicer.UpperSemiLattice

import           Data.Map as Map ( Map, fromList, mapWithKey, keys, member )
import           Data.Maybe
import           Data.List       ( union, delete )
import qualified Data.Hashable as H ( hash )
import           Text.PrettyPrint

data Type = IntTy | BoolTy | UnitTy | StringTy
          | PairTy Type Type | SumTy Type Type | FunTy Type Type
          | RecTy TyVar Type | TyVar TyVar
          | HoleTy
          -- Reference type
          | RefTy Type
          -- Trace types
          | TraceTy Type
            deriving (Eq,Ord,Show)

isRefTy :: Type -> Bool
isRefTy (RefTy _) = True
isRefTy _         = False

isFunTy :: Type -> Bool
isFunTy (FunTy _ _) = True
isFunTy _           = False

instance UpperSemiLattice Type where
    bot = HoleTy

    leq  HoleTy           _                 = True
    leq  IntTy            IntTy             = True
    leq  BoolTy           BoolTy            = True
    leq  UnitTy           UnitTy            = True
    leq  StringTy         StringTy          = True
    leq (PairTy ty1 ty2) (PairTy ty1' ty2') = ty1 `leq` ty1' && ty2 `leq` ty2'
    leq (SumTy  ty1 ty2) (SumTy  ty1' ty2') = ty1 `leq` ty1' && ty2 `leq` ty2'
    leq (FunTy  ty1 ty2) (FunTy  ty1' ty2') = ty1 `leq` ty1' && ty2 `leq` ty2'
    leq (RecTy  a ty   ) (RecTy  a' ty'   ) = a == a' && ty `leq` ty'
    leq (TyVar  a      ) (TyVar  b        ) = a == b
    leq (RefTy   ty    ) (RefTy   ty'     ) = ty `leq` ty'
    leq (TraceTy ty    ) (TraceTy ty'     ) = ty `leq` ty'
    leq _                _                  = error "UpperSemiLattice Type: leq"

    lub HoleTy   ty       = ty
    lub ty       HoleTy   = ty
    lub IntTy    IntTy    = IntTy
    lub BoolTy   BoolTy   = BoolTy
    lub UnitTy   UnitTy   = UnitTy
    lub StringTy StringTy = StringTy
    lub (TyVar a)    (TyVar b)      | a == b  = TyVar a
    lub (RecTy a ty) (RecTy a' ty') | a == a' = RecTy a  (ty `lub` ty')
    lub (PairTy ty1 ty2) (PairTy ty1' ty2')
        = PairTy (ty1 `lub` ty1') (ty2 `lub` ty2')
    lub (SumTy ty1 ty2) (SumTy ty1' ty2')
        = SumTy (ty1 `lub` ty1') (ty2 `lub` ty2')
    lub (FunTy ty1 ty2) (FunTy ty1' ty2')
        = FunTy (ty1 `lub` ty1') (ty2 `lub` ty2')
    lub (RefTy ty) (RefTy ty')
        = RefTy (ty `lub` ty')
    lub (TraceTy ty) (TraceTy ty')
        = TraceTy (ty `lub` ty')
    lub a b = error $ "UpperSemiLattice Type: error taking lub of " ++
                      show a ++ " and " ++ show b

instance PP Type where
    pp v = pp_partial v v

    pp_partial BoolTy   BoolTy   = text "bool"
    pp_partial IntTy    IntTy    = text "int"
    pp_partial StringTy StringTy = text "string"
    pp_partial UnitTy   UnitTy   = text "unit"
    pp_partial HoleTy   HoleTy   = sb (text "_")
    pp_partial HoleTy   v        = sb (pp v)
    pp_partial (SumTy ty1 ty2) (SumTy ty1' ty2') =
        parens (pp_partial ty1 ty1' <+> text "+" <+> pp_partial ty2 ty2')
    pp_partial (PairTy ty1 ty2) (PairTy ty1' ty2') =
        parens (pp_partial ty1 ty1' <+> text "*" <+> pp_partial ty2 ty2')
    pp_partial (FunTy ty1 ty2) (FunTy ty1' ty2') =
        parens (pp_partial ty1 ty1' <+> text "->" <+> pp_partial ty2 ty2')
    pp_partial (TyVar v) (TyVar v') = pp_partial v v'
    pp_partial (RecTy a ty) (RecTy a' ty')
        | a == a' = text "rec" <+> pp a <+> text "." <+> pp_partial ty ty'
    pp_partial (RefTy ty) (RefTy ty')
        = text "ref" <> parens (pp_partial ty ty')
    pp_partial (TraceTy ty) (TraceTy ty')
        = text "trace" <> parens (pp_partial ty ty')
    pp_partial v v' = error ("Error pretty-printing Type: v is " ++ show v ++
                             " and v' is " ++ show v')

type Ctx = Env Type

data Lab = L { unL  :: String
             , hash :: Int }

instance Eq Lab where
    l1 == l2 = hash l1 == hash l2

instance Show Lab where
    showsPrec _ l = showString (unL l)

instance Ord Lab where
    compare (L s h) (L s' h') = case compare h h' of
                                  EQ -> compare s s'
                                  o  -> o

mkL :: String -> Lab
mkL s = L s (H.hash s)

data Syntax a = Var Var
              | Let Var a a
              | Unit
              | CBool Bool
              | CInt Int
              | CString String
              | Op Primitive [a]
              | Pair a a | Fst a | Snd a
              | InL a | InR a
              | Fun (Code Exp)
              | Roll (Maybe TyVar) a | Unroll (Maybe TyVar) a
              | Hole
              -- References
              | Ref a  | Deref a | Assign a a | Seq a a
                deriving (Show, Eq, Ord)

data Exp = Exp (Syntax Exp)
         | EIf Exp Exp Exp
         | ECase Exp Match
         | EApp Exp Exp
           -- run-time tracing
         | ETrace Exp
           deriving (Show, Eq, Ord)

pattern EVar :: Var -> Exp
pattern EVar v = Exp (Var v)

pattern ELet :: Var -> Exp -> Exp -> Exp
pattern ELet v t1 t2 = Exp (Let v t1 t2)

pattern EUnit :: Exp
pattern EUnit = Exp Unit

pattern EBool :: Bool -> Exp
pattern EBool b = Exp (CBool b)

pattern EInt :: Int -> Exp
pattern EInt i = Exp (CInt i)

pattern EOp :: Primitive -> [Exp] -> Exp
pattern EOp op args = Exp (Op op args)

pattern EString :: String -> Exp
pattern EString s = Exp (CString s)

pattern EPair :: Exp -> Exp -> Exp
pattern EPair t1 t2 = Exp (Pair t1 t2)

pattern EFst :: Exp -> Exp
pattern EFst t = Exp (Fst t)

pattern ESnd :: Exp -> Exp
pattern ESnd t = Exp (Snd t)

pattern EInL :: Exp -> Exp
pattern EInL t = Exp (InL t)

pattern EInR :: Exp -> Exp
pattern EInR t = Exp (InR t)

pattern EFun :: Code Exp -> Exp
pattern EFun code = Exp (Fun code)

pattern ERoll :: Maybe TyVar -> Exp -> Exp
pattern ERoll tv t = Exp (Roll tv t)

pattern EUnroll :: Maybe TyVar -> Exp -> Exp
pattern EUnroll tv t = Exp (Unroll tv t)

pattern EHole :: Exp
pattern EHole = Exp Hole

pattern ERef :: Exp -> Exp
pattern ERef t = Exp (Ref t)

pattern EDeref :: Exp -> Exp
pattern EDeref t = Exp (Deref t)

pattern EAssign :: Exp -> Exp -> Exp
pattern EAssign t1 t2 = Exp (Assign t1 t2)

pattern ESeq :: Exp -> Exp -> Exp
pattern ESeq t1 t2 = Exp (Seq t1 t2)

data Trace = TExp (Syntax Trace)
           | TIfThen Trace Exp Exp Trace
           | TIfElse Trace Exp Exp Trace
           | TCaseL Trace (Maybe Var) Trace
           | TCaseR Trace (Maybe Var) Trace
           | TCall Trace Trace (Maybe Lab) (Code Trace)
             deriving (Show, Eq, Ord)

pattern TVar :: Var -> Trace
pattern TVar v = TExp (Var v)

pattern TLet :: Var -> Trace -> Trace -> Trace
pattern TLet v t1 t2 = TExp (Let v t1 t2)

pattern TUnit :: Trace
pattern TUnit = TExp Unit

pattern TBool :: Bool -> Trace
pattern TBool b = TExp (CBool b)

pattern TInt :: Int -> Trace
pattern TInt i = TExp (CInt i)

pattern TOp :: Primitive -> [Trace] -> Trace
pattern TOp op args = TExp (Op op args)

pattern TString :: String -> Trace
pattern TString s = TExp (CString s)

pattern TPair :: Trace -> Trace -> Trace
pattern TPair t1 t2 = TExp (Pair t1 t2)

pattern TFst :: Trace -> Trace
pattern TFst t = TExp (Fst t)

pattern TSnd :: Trace -> Trace
pattern TSnd t = TExp (Snd t)

pattern TInL :: Trace -> Trace
pattern TInL t = TExp (InL t)

pattern TInR :: Trace -> Trace
pattern TInR t = TExp (InR t)

pattern TFun :: Code Exp -> Trace
pattern TFun code = TExp (Fun code)

pattern TRoll :: Maybe TyVar -> Trace -> Trace
pattern TRoll tv t = TExp (Roll tv t)

pattern TUnroll :: Maybe TyVar -> Trace -> Trace
pattern TUnroll tv t = TExp (Unroll tv t)

pattern THole :: Trace
pattern THole = TExp Hole

pattern TRef :: Trace -> Trace
pattern TRef t = TExp (Ref t)

pattern TDeref :: Trace -> Trace
pattern TDeref t = TExp (Deref t)

pattern TAssign :: Trace -> Trace -> Trace
pattern TAssign t1 t2 = TExp (Assign t1 t2)

pattern TSeq :: Trace -> Trace -> Trace
pattern TSeq t1 t2 = TExp (Seq t1 t2)

data Code a = Rec { funName  :: Var
                  , funArg   :: Var
                  , funBody  :: a
                  , funLabel :: Maybe Lab}
                  deriving (Show, Eq, Ord)

data Match = Match { inL :: (Maybe Var, Exp)
                   , inR :: (Maybe Var, Exp) }
                   deriving (Show, Eq, Ord)

data Value = VBool Bool | VInt Int | VUnit | VString String
           | VPair Value Value
           | VInL Value | VInR Value
           | VRoll (Maybe TyVar) Value
           | VClosure (Code Exp) (Env Value)
           | VHole | VStar
           | VExp Exp (Env Value)
           -- mutable store locations
           | VStoreLoc Int
           -- run-time traces
           | VTrace Value Trace (Env Value)
           deriving (Show, Eq, Ord)

class Valuable a where
    to_val :: a -> Value
    from_val :: Value -> a

instance Valuable Int where
    to_val i = VInt i
    from_val (VInt i) = i
    from_val _ = error "Cannot convert to an Int value"

instance Valuable Bool where
    to_val b = VBool b
    from_val (VBool b) = b
    from_val _ = error "Cannot convert to an Bool value"

instance Valuable () where
    to_val () = VUnit
    from_val VUnit = ()
    from_val _ = error "Cannot convert to a () value"

-- JSTOLAREK: these instances are not used
instance (Valuable a, Valuable b) => Valuable (a,b) where
    to_val (a, b) = VPair (to_val a) (to_val b)
    from_val (VPair a b) = (from_val a, from_val b)
    from_val _ = error "Cannot convert to a pait value"

instance (Valuable a, Valuable b) => Valuable (Either a b) where
    to_val (Left a )  = VInL (to_val a)
    to_val (Right b) = VInR (to_val b)
    from_val (VInL a) = from_val a
    from_val (VInR b) = from_val b
    from_val _ = error "Cannot convert to an Either value"

instance Valuable a => Valuable (Maybe a) where
    to_val Nothing = VInL VUnit
    to_val (Just a) = VInR (to_val a)
    from_val (VInL VUnit) = Nothing
    from_val (VInR a) = from_val a
    from_val _ = error "Cannot convert to a Maybe value"

-- fvsK.  Calculates free vars of closure.
-- TODO: use ordered sets
class FVs a where
    fvs :: a -> [Var]

instance FVs a => FVs (Syntax a) where
    fvs (Var x)        = [x]
    fvs (Let x e1 e2)  = delete x (fvs e1 `union` fvs e2)
    fvs  Unit          = []
    fvs (Op _ exps)    = concat (Prelude.map fvs exps)
    fvs (CBool _)      = []
    fvs (CInt _)       = []
    fvs (CString _)    = []
    fvs (Pair e1 e2)   = fvs e1 `union` fvs e2
    fvs (Fst e)        = fvs e
    fvs (Snd e)        = fvs e
    fvs (InL e)        = fvs e
    fvs (InR e)        = fvs e
    fvs (Fun k)        = fvs k
    fvs (Roll _ e)     = fvs e
    fvs (Unroll _ e)   = fvs e
    fvs (Ref e)        = fvs e
    fvs (Deref e)      = fvs e
    fvs (Assign e1 e2) = fvs e1 `union` fvs e2
    fvs (Seq    e1 e2) = fvs e1 `union` fvs e2
    fvs  Hole          = []

instance FVs Exp where
    fvs (EIf e1 e2 e3) = fvs e1 `union` fvs e2 `union` fvs e3
    fvs (ECase e m)    = fvs e `union` fvs m
    fvs (EApp e1 e2)   = fvs e1 `union` fvs e2
    fvs (ETrace e)     = fvs e
    fvs (Exp e)        = fvs e

instance FVs Match where
    fvs (Match (x, e1) (y, e2)) =
        let f1 = if isJust x
                 then delete (fromJust x) (fvs e1)
                 else fvs e1
            f2 = if isJust y
                 then delete (fromJust y) (fvs e2)
                 else fvs e2
        in f1 `union` f2

instance FVs a => FVs (Code a) where
    fvs k = let vs = fvs (funBody k)
            in delete (funName k) (delete (funArg k) vs)


instance FVs Trace where
    fvs (TIfThen t e1 e2 t1) = fvs t `union` fvs e1 `union` fvs e2 `union` fvs t1
    fvs (TIfElse t e1 e2 t2) = fvs t `union` fvs e1 `union` fvs e2 `union` fvs t2
    fvs (TCaseL t v t1)      = fvs t `union` if isJust v
                                             then (delete (fromJust v) (fvs t1))
                                             else fvs t1
    fvs (TCaseR t v t2)      = fvs t `union` if isJust v
                                             then (delete (fromJust v) (fvs t2))
                                             else fvs t2
    fvs (TCall t1 t2 _ t)    = fvs t1 `union` fvs t2 `union` fvs t
    fvs (TExp e)             = fvs e

promote :: Value -> Value
promote VStar            = VStar
promote VHole            = VStar
promote VUnit            = VUnit
promote (VBool b)        = VBool b
promote (VInt i)         = VInt i
promote (VString s)      = VString s
promote (VPair v1 v2)    = VPair (promote v1) (promote v2)
promote (VInL v)         = VInL (promote v)
promote (VInR v)         = VInR (promote v)
promote (VRoll tv v)     = VRoll tv (promote v)
promote (VStoreLoc l)    = VStoreLoc l
promote (VClosure k env) = VClosure k (fmap promote env)
promote (VTrace v t env) = VTrace (promote v) t (fmap promote env)
promote (VExp     e env) = VExp e (fmap promote env)

instance UpperSemiLattice Value where
    bot                               = VHole

    leq VHole _                       = True
    leq VStar VHole                   = False
    leq VStar v                       = promote v == v
    leq VUnit VUnit                   = True
    leq (VBool b) (VBool b')          = b == b'
    leq (VInt i) (VInt i')            = i == i'
    leq (VString i) (VString i')      = i == i'
    leq (VPair v1 v2) (VPair v1' v2') = v1 `leq` v1' && v2 `leq` v2'
    leq (VInL v) (VInL v')            = v `leq` v'
    leq (VInR v) (VInR v')            = v `leq` v'
    leq (VRoll tv v) (VRoll tv' v')   | tv == tv' = v `leq` v'
    leq (VStoreLoc i) (VStoreLoc i')  = i == i'
    leq (VClosure k env) (VClosure k' env')
        = k `leq` k' && env `leq` env'
    leq a b = error $ "UpperSemiLattice Value: error taking leq of " ++
                      show a ++ " and " ++ show b

    lub  VHole         v              = v
    lub  v             VHole          = v
    lub  VStar         v              = promote v
    lub  v             VStar          = promote v
    lub  VUnit         VUnit          = VUnit
    lub (VBool b)     (VBool b')      | b == b' = VBool b
    lub (VInt i)      (VInt i')       | i == i' = VInt i
    lub (VString i)   (VString i')    | i == i' = VString i
    lub (VPair v1 v2) (VPair v1' v2') = VPair (v1 `lub` v1') (v2 `lub` v2')
    lub (VInL v)      (VInL v')       = VInL (v `lub` v')
    lub (VInR v)      (VInR v')       = VInR (v `lub` v')
    lub (VRoll tv v)  (VRoll tv' v')  | tv == tv' = VRoll tv (v `lub` v')
    lub (VStoreLoc i) (VStoreLoc i')  | i == i' = VStoreLoc i
    lub (VClosure k env) (VClosure k' env')
        = VClosure (k `lub` k') (env `lub` env')
    lub a b = error $ "UpperSemiLattice Value: error taking lub of " ++
                      show a ++ " and " ++ show b

instance (UpperSemiLattice a, Show a) => UpperSemiLattice (Syntax a) where
    bot                                = Hole

    leq Hole _                        = True
    leq (Var x) (Var x')               = x `leq` x'
    leq (Let x e1 e2) (Let x' e1' e2') = x `leq` x' && e1 `leq` e1' && e2 `leq` e2'
    leq (CInt i) (CInt j)              = i == j
    leq (CString i) (CString j)        = i == j
    leq (Op f es) (Op f' es')          | f == f' && length es == length es'
                                       = all (\(x,y) -> x `leq` y) (zip es es')
    leq Unit Unit                      = True
    leq (CBool _) (CBool _)            = True
    leq (Pair e1 e2) (Pair e1' e2')    = e1 `leq` e1' && e2 `leq` e2'
    leq (Fst e) (Fst e')               = e `leq` e'
    leq (Snd e) (Snd e')               = e `leq` e'
    leq (InL e) (InL e')               = e `leq` e'
    leq (InR e) (InR e')               = e `leq` e'
    leq (Fun k) (Fun k')               = k `leq` k'
    leq (Roll tv e) (Roll tv' e')      | tv == tv' = e `leq` e'
    leq (Unroll tv e) (Unroll tv' e')  | tv == tv' = e `leq` e'
    leq a b = error $ "UpperSemiLattice Syntax: error taking leq of " ++
                      show a ++ " and " ++ show b


    lub Hole e                         = e
    lub e Hole                         = e
    lub (Var x) (Var x')               = Var (x `lub` x')
    lub (Let x e1 e2) (Let x' e1' e2') = Let (x `lub` x') (e1 `lub` e1') (e2 `lub` e2')
    lub (CInt i) (CInt j)              | i == j = CInt i
    lub (CString i) (CString j)        | i == j = CString i
    lub (Op f es) (Op f' es')          | f == f' && length es == length es'
                                       = Op f (map (\(x,y) -> x `lub` y) (zip es es'))
    lub Unit Unit                      = Unit
    lub (CBool b) (CBool b')           | b == b'
                                       = CBool b
    lub (Pair e1 e2) (Pair e1' e2')    = Pair (e1 `lub` e1') (e2 `lub` e2')
    lub (Fst e) (Fst e')               = Fst (e `lub` e')
    lub (Snd e) (Snd e')               = Snd (e `lub` e')
    lub (InL e) (InL e')               = InL (e `lub` e')
    lub (InR e) (InR e')               = InR (e `lub` e')
    lub (Fun k) (Fun k')               = Fun (k `lub` k')
    lub (Roll tv e) (Roll tv' e')      | tv == tv' = Roll tv (e `lub` e')
    lub (Unroll tv e) (Unroll tv' e')  | tv == tv' = Unroll tv (e `lub` e')
    lub a b = error $ "UpperSemiLattice Syntax: error taking lub of " ++
                      show a ++ " and " ++ show b

instance UpperSemiLattice Exp where
    bot                                = Exp Hole

    leq (Exp Hole) _                   = True
    leq (Exp e1) (Exp e2)              = e1 `leq` e2
    leq (EIf e e1 e2) (EIf e' e1' e2') = e `leq` e' && e1 `leq` e1' && e2 `leq` e2'
    leq (ECase e m) (ECase e' m')      = e `leq` e' && m `leq` m'
    leq (EApp e1 e2) (EApp e1' e2')    = e1 `leq`  e1' && e2 `leq` e2'
    leq (ETrace e) (ETrace e')
        = e `leq` e'
    leq a b = error $ "UpperSemiLattice Exp: error taking leq of " ++
                      show a ++ " and " ++ show b

    lub (Exp Hole) e                   = e
    lub e (Exp Hole)                   = e
    lub (Exp e1) (Exp e2)              = Exp (e1 `lub` e2)
    lub (EIf e e1 e2) (EIf e' e1' e2') = EIf (e `lub` e') (e1 `lub` e1') (e2 `lub` e2')
    lub (ECase e m) (ECase e' m')      = ECase (e `lub` e') (m `lub` m')
    lub (EApp e1 e2) (EApp e1' e2')    = EApp (e1 `lub` e1') (e2 `lub` e2')
    lub (ETrace e) (ETrace e')
        = ETrace (e `lub` e')
    lub a b = error $ "UpperSemiLattice Exp: error taking lub of " ++
                      show a ++ " and " ++ show b

instance UpperSemiLattice a => UpperSemiLattice (Code a) where
    bot = Rec bot bot bot Nothing

    leq (Rec f x e l) (Rec f' x' e' l') =
        f `leq` f' && x `leq` x' && e `leq` e' && l `leq` l'

    lub (Rec f x e l) (Rec f' x' e' l')
        = Rec (f `lub` f') (x `lub` x') (e `lub` e') (l `lub` l')


instance UpperSemiLattice Match where
    bot = Match (bot, bot) (bot, bot)

    leq (Match (x,m1) (y,m2)) (Match (x',m1') (y', m2'))
        = x `leq` x' && y `leq` y' && m1 `leq` m1' && m2 `leq` m2'

    lub (Match (x,m1) (y,m2)) (Match (x',m1') (y', m2'))
        = Match (x `lub` x',m1 `lub` m1') (y `lub` y', m2 `lub` m2')


instance UpperSemiLattice Trace where
    bot                = TExp Hole

    leq (TExp Hole) _ = True
    leq (TIfThen t e1 e2 t1) (TIfThen t' e1' e2' t1')
        = t `leq` t' && e1 `leq` e1' && e2 `leq` e2' && t1 `leq` t1'
    leq (TIfElse t e1 e2 t2) (TIfElse t' e1' e2' t2')
        = t `leq` t' && e1 `leq` e1' && e2 `leq` e2' && t2 `leq` t2'
    leq (TCaseL t x t1) (TCaseL t' x' t1')
        = t `leq` t' && x == x' && t1 `leq` t1'
    leq (TCaseR t x t2) (TCaseR t'  x' t2')
        = t `leq` t' && x == x' && t2 `leq` t2'
    leq (TCall t1 t2 k t) (TCall t1' t2' k' t')
        = t1 `leq` t1' && t2 `leq` t2' && k `leq` k' && t `leq` t'
    leq a b = error $ "UpperSemiLattice Trace: error taking leq of " ++
                      show a ++ " and " ++ show b

    lub (TExp Hole) e       = e
    lub e (TExp Hole)       = e
    lub (TExp e1) (TExp e2) = TExp (e1 `lub` e2)
    lub (TIfThen t e1 e2 t1) (TIfThen t' e1' e2' t1')
        = TIfThen (t `lub` t') (e1 `lub` e1') (e2 `lub` e2') (t1 `lub` t1')
    lub (TIfElse t e1 e2 t2) (TIfElse t' e1' e2' t2')
        = TIfElse (t `lub` t') (e1 `lub` e1') (e2 `lub` e2') (t2 `lub` t2')
    lub (TCaseL t x t1) (TCaseL t' x' t1')
        = TCaseL (t `lub` t') (x `lub` x') (t1 `lub` t1')
    lub (TCaseR t x t2) (TCaseR t' x' t2')
        = TCaseR (t `lub` t') (x `lub` x') (t2 `lub` t2')
    lub (TCall t1 t2 k t) (TCall t1' t2' k' t')
        = TCall (t1 `lub` t1') (t2 `lub` t2') (k `lub` k') (t `lub` t')
    lub a b = error $ "UpperSemiLattice Trace: error taking lub of " ++
                      show a ++ " and " ++ show b

class Pattern a where
    match :: a -> a -> a -> Bool
    extract :: a -> a -> a

instance Pattern Value where
    match VStar          v             v'             = v == v'
    match VHole          _             _              = True
    match VUnit          VUnit         VUnit          = True
    match (VBool bp)    (VBool b)     (VBool b')      = bp == b && bp == b'
    match (VInt ip)     (VInt i)      (VInt i')       = ip == i && ip == i'
    match (VString ip)  (VString i)   (VString i')    = ip == i && ip == i'
    match (VPair p1 p2) (VPair v1 v2) (VPair v1' v2') = match p1 v1 v1' && match p2 v2 v2'
    match (VInL p)      (VInL v)      (VInL v')       = match p v v'
    match (VInR p)      (VInR v)      (VInR v')       = match p v v'
    match (VRoll tv p)  (VRoll tv' v) (VRoll tv'' v')
        | tv == tv' && tv' == tv''
        = match p v v'
    -- JSTOLAREK: What about VStoreLoc?
    match _ _ _ = False

    extract  VStar          v              = v
    extract  VHole          _              = VHole
    extract  VUnit          VUnit          = VUnit
    extract (VBool bp)     (VBool b)       | bp == b = VBool b
    extract (VInt ip)      (VInt i)        | ip == i = VInt i
    extract (VString ip)   (VString i)     | ip == i = VString i
    extract (VPair p1 p2)  (VPair v1 v2)   = VPair (extract p1 v1)
                                                   (extract p2 v2)
    extract (VInL p)       (VInL v)        = VInL (extract p v)
    extract (VInR p)       (VInR v)        = VInR (extract p v)
    extract (VRoll tv p)   (VRoll tv' v)   | tv == tv' = VRoll tv (extract p v)
    extract (VClosure _ p) (VClosure k' v) = VClosure k' (extract p v)
    extract (VStoreLoc i ) (VStoreLoc i' ) | i == i' = VStoreLoc i
    extract p v = error ("extract only defined if p <= v, but p is " ++
                         show p ++ " and v is " ++ show v)

instance (Pattern a, UpperSemiLattice a) => Pattern (Env a) where
    match (penv@(Env penv')) env1 env2
        = all (\x -> match (lookupEnv' penv x) (lookupEnv' env1 x)
                           (lookupEnv' env2 x)) (Map.keys penv')
    extract (Env penv') env
        = Env (Map.mapWithKey (\x p -> extract p (lookupEnv' env x)) penv')

commonOps :: Eq a => Map Primitive ((a, a) -> Value)
commonOps = fromList
   [ (OpEq , to_val . uncurry (==))
   , (OpNeq, to_val . uncurry (/=))
   ]

intBinOps :: Map Primitive ((Int, Int) -> Value)
intBinOps = fromList
   [ (OpPlus , to_val . uncurry (+))
   , (OpMinus, to_val . uncurry (-))
   , (OpTimes, to_val . uncurry (*))
   , (OpDiv  , to_val . uncurry div)
   , (OpMod  , to_val . uncurry mod)
   ]

intRelOps :: Map Primitive ((Int, Int) -> Value)
intRelOps = fromList
   [ (OpLt   , to_val . uncurry (<) )
   , (OpGt   , to_val . uncurry (>) )
   , (OpLeq  , to_val . uncurry (<=))
   , (OpGeq  , to_val . uncurry (>=))
   ]

boolRelOps :: Map Primitive ((Bool, Bool) -> Value)
boolRelOps = fromList
   [ (OpAnd, to_val . uncurry (&&))
   , (OpOr , to_val . uncurry (||))
   ]

boolUnOps :: Map Primitive (Bool -> Value)
boolUnOps = fromList
   [ (OpNot, to_val . not) ]

isCommonOp :: Primitive -> Bool
-- instantiate type variable in commonOps to () to avoid type ambiguity
isCommonOp op = op `member` (commonOps :: Map Primitive (((), ()) -> Value))

isIntBinOp :: Primitive -> Bool
isIntBinOp op = op `member` intBinOps

isIntRelOp :: Primitive -> Bool
isIntRelOp op = op `member` intRelOps

isBoolRelOp :: Primitive -> Bool
isBoolRelOp op = op `member` boolRelOps

isBoolUnOp :: Primitive -> Bool
isBoolUnOp op = op `member` boolUnOps
