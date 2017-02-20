{-# LANGUAGE DeriveAnyClass         #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE UndecidableInstances   #-}

module Language.Slicer.Core
    ( -- * Abstract syntax
      Syntax(..), Value(..), Type(..), Ctx, Code(..), Match(..)
    , Store, StoreLabel, StoreLabels, ReturnType(..)
    , Exp( EVar, ELet, EUnit, EBool, EInt, EOp, EString, EPair, EFst, ESnd
         , EInL, EInR, EFun, ERoll, EUnroll, EHole, ESeq
         , .. )
    , Trace ( TVar, TLet, TUnit, TBool, TInt, TOp, TString, TPair, TFst, TSnd
            , TInL, TInR, TFun, TRoll, TUnroll, THole, TSeq, .. )

    -- * Helper functions for AST
    , isRefTy, isFunTy, isCondTy, isExnTy, isPairTy, fstTy, sndTy
    , isException, isRaise

    , Pattern(extract)

    , uneval

      -- * Built-in operators
    , commonOps, intBinOps, intRelOps, boolRelOps, boolUnOps
    , isCommonOp, isIntBinOp, isIntRelOp, isBoolRelOp, isBoolUnOp

      -- * Lables
    , Lab( unL ), mkL

      -- * Free variables
    , FVs(..)
    ) where


import           Language.Slicer.Env
import           Language.Slicer.Primitives
import           Language.Slicer.UpperSemiLattice

import           Control.DeepSeq    ( NFData                                  )
import           Data.Map as Map    ( Map, fromList, mapWithKey, keys, member )
import           Data.Maybe
import qualified Data.IntMap as M
import           Data.List          ( union, delete, (\\)                     )
import qualified Data.Hashable as H ( hash                                    )
import           GHC.Generics       ( Generic                                 )
import           Text.PrettyPrint.HughesPJClass

data Type = IntTy | BoolTy | UnitTy | StringTy
          | PairTy Type Type | SumTy Type Type | FunTy Type Type
          | RecTy TyVar Type | TyVar TyVar
          | HoleTy
          -- Reference type
          | RefTy Type
          -- Exception type
          | ExnTy
          -- Trace types
          | TraceTy Type
            deriving (Show, Generic, NFData)

-- We need a hand-written instance of Eq, because ExnTy is equal to every type
instance Eq Type where
    ExnTy        == _              = True
    _            == ExnTy          = True
    IntTy        == IntTy          = True
    BoolTy       == BoolTy         = True
    UnitTy       == UnitTy         = True
    StringTy     == StringTy       = True
    PairTy t1 t2 == PairTy t1' t2' = t1 == t1' && t2 == t2'
    SumTy  t1 t2 == SumTy  t1' t2' = t1 == t1' && t2 == t2'
    FunTy  t1 t2 == FunTy  t1' t2' = t1 == t1' && t2 == t2'
    RecTy  t1 t2 == RecTy  t1' t2' = t1 == t1' && t2 == t2'
    TyVar t      == TyVar t'       = t == t'
    RefTy t      == RefTy t'       = t == t'
    TraceTy t    == TraceTy t'     = t == t'
    _            == _              = False

deriving instance Ord Type

-- | Is reference type?
isRefTy :: Type -> Bool
isRefTy (RefTy _) = True
isRefTy ExnTy     = True
isRefTy _         = False

-- | Is function type?
isFunTy :: Type -> Bool
isFunTy (FunTy _ _) = True
isFunTy ExnTy       = True
isFunTy _           = False

-- | Is conditional type?
isCondTy :: Type -> Bool
isCondTy BoolTy = True
isCondTy ExnTy  = True
isCondTy _      = False

-- | Is pair type?
isPairTy :: Type -> Bool
isPairTy (PairTy _ _) = True
isPairTy ExnTy        = True
isPairTy _            = False

-- | Is exception type?
isExnTy :: Type -> Bool
isExnTy ExnTy = True
isExnTy _     = False

-- | Get first type field of a type, but propagare exception type
fstTy :: Type -> Type
fstTy  ExnTy       = ExnTy
fstTy (PairTy t _) = t
fstTy (SumTy  t _) = t
fstTy (FunTy  t _) = t
fstTy (RefTy  t  ) = t
fstTy (TraceTy t ) = t
fstTy _  =
    error "Impossible happened: type does not have a first component"

-- | Get second type field of a type, but propagare exception type
sndTy :: Type -> Type
sndTy  ExnTy = ExnTy
sndTy (PairTy _ t) = t
sndTy (SumTy _ t) = t
sndTy (FunTy _ t) = t
sndTy _  =
    error "Impossible happened: type does not have a second component"

instance UpperSemiLattice Type where
    bot = HoleTy

    leq  HoleTy           _                 = True
    leq  IntTy            IntTy             = True
    leq  BoolTy           BoolTy            = True
    leq  UnitTy           UnitTy            = True
    leq  StringTy         StringTy          = True
    leq  ExnTy            ExnTy             = True
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
    lub ExnTy    ExnTy    = ExnTy
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

instance Pretty Type where
    pPrint BoolTy   = text "bool"
    pPrint IntTy    = text "int"
    pPrint StringTy = text "string"
    pPrint UnitTy   = text "unit"
    pPrint HoleTy   = text "_"
    pPrint ExnTy    = text "<exn>"
    pPrint (SumTy ty1 ty2) =
        parens (pPrint ty1 <+> text "+" <+> pPrint ty2)
    pPrint (PairTy ty1 ty2) =
        parens (pPrint ty1 <+> text "*" <+> pPrint ty2 )
    pPrint (FunTy ty1 ty2) =
        parens (pPrint ty1 <+> text "->" <+> pPrint ty2)
    pPrint (TyVar v) = pPrint v
    pPrint (RecTy a ty) = text "rec" <+> pPrint a <+> text "." <+> pPrint ty
    pPrint (RefTy ty)   = text "ref" <> parens (pPrint ty)
    pPrint (TraceTy ty) = text "trace" <> parens (pPrint ty)

-- | Internal labels used during runtime to identify store locations
type StoreLabel  = Int
type StoreLabels = [ StoreLabel ]

-- | Reference store
type Store = M.IntMap Value

type Ctx = Env Type

data Lab = L { unL  :: String
             , hash :: Int }
           deriving (Generic, NFData)

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
              | Roll TyVar a | Unroll TyVar a
              | Seq a a
              | Hole
                deriving (Show, Eq, Ord, Generic, NFData)

data Exp = Exp (Syntax Exp)
         | EIf Exp Exp Exp
         | ECase Exp Match
         | EApp Exp Exp
           -- run-time tracing
         | ETrace Exp
         -- References
         | ERef Exp | EDeref Exp | EAssign Exp Exp
         -- Exceptions
         | ERaise Exp | ECatch Exp Var Exp
           deriving (Show, Eq, Ord, Generic, NFData)

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

pattern ERoll :: TyVar -> Exp -> Exp
pattern ERoll tv t = Exp (Roll tv t)

pattern EUnroll :: TyVar -> Exp -> Exp
pattern EUnroll tv t = Exp (Unroll tv t)

pattern EHole :: Exp
pattern EHole = Exp Hole

pattern ESeq :: Exp -> Exp -> Exp
pattern ESeq e1 e2 = Exp (Seq e1 e2)

data Trace = TExp (Syntax Trace)
           | TIfThen Trace Trace            -- ^ Take "then" branch of if
           | TIfElse Trace Trace            -- ^ Take "else" branch of if
           | TIfExn Trace                   -- ^ Condition raises exception
           | TCaseL Trace (Maybe Var) Trace -- ^ Take "left constructor"
                                            -- alternative in a case expression
           | TCaseR Trace (Maybe Var) Trace -- ^ Take "right constructor"
                                            -- alternative in a case expression
           | TCallExn Trace Trace -- ^ Any of application arguments raises an
                                  -- exception
           | TCall Trace Trace (Maybe Lab) (Code Trace)
           -- Annotated hole
           | TSlicedHole StoreLabels ReturnType
           -- References.  See Note [Maybe trace labels]
           | TRef (Maybe StoreLabel) Trace | TDeref (Maybe StoreLabel) Trace
           | TAssign (Maybe StoreLabel) Trace Trace
            -- Exceptions
           | TRaise Trace             -- ^ Raise exception
           | TTry Trace               -- ^ Not throwing an exception in a
                                      --   try-with block
           | TTryWith Trace Var Trace -- ^ Throwing exception in a try-with
                                      --   block
             deriving (Show, Eq, Ord, Generic, NFData)

-- | Did computations returned a result or raised an exception?
data ReturnType = RetValue | RetRaise
                  deriving (Show, Eq, Ord, Generic, NFData)

isRaise :: Trace -> Bool
isRaise (TRaise _) = True
isRaise _          = False

-- Note [Maybe trace labels]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- Labels in reference trace constructs are Maybes because it is possible that
-- the the enclosed expression raises an exception instead of evaluating to a
-- label value.

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

pattern TString :: String -> Trace
pattern TString s = TExp (CString s)

pattern TOp :: Primitive -> [Trace] -> Trace
pattern TOp op args = TExp (Op op args)

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

pattern TRoll :: TyVar -> Trace -> Trace
pattern TRoll tv t = TExp (Roll tv t)

pattern TUnroll :: TyVar -> Trace -> Trace
pattern TUnroll tv t = TExp (Unroll tv t)

pattern THole :: Trace
pattern THole = TExp Hole

pattern TSeq :: Trace -> Trace -> Trace
pattern TSeq e1 e2 = TExp (Seq e1 e2)

data Code a = Rec { funName  :: Var
                  , funArg   :: Var
                  , funBody  :: a
                  , funLabel :: Maybe Lab}
                  deriving (Show, Eq, Ord, Generic, NFData)

data Match = Match { inL :: (Maybe Var, Exp)
                   , inR :: (Maybe Var, Exp) }
                   deriving (Show, Eq, Ord, Generic, NFData)

data Value = VBool Bool | VInt Int | VUnit | VString String
           | VPair Value Value
           | VInL Value | VInR Value
           | VRoll TyVar Value
           | VClosure (Code Exp) (Env Value)
           | VHole | VStar
           | VExp Exp (Env Value)
           -- mutable store locations
           | VStoreLoc StoreLabel
           -- Exceptions.  Used only for tracing
           | VException Value
           -- run-time traces
           | VTrace Value Trace (Env Value) Store
           deriving (Show, Eq, Ord, Generic, NFData)

isException :: Value -> Bool
isException (VException _) = True
isException _              = False

class Valuable a where
    to_val :: a -> Value

instance Valuable Int where
    to_val i = VInt i

instance Valuable Bool where
    to_val b = VBool b

instance Valuable () where
    to_val () = VUnit

-- Enevaluation.  Squash trace back down into expression.
class Uneval a b | a -> b where
    uneval :: a -> b

instance Uneval Trace Exp where
    uneval (TCaseL t x t1)   = ECase (uneval t) (Match (x, uneval t1) (bot, bot))
    uneval (TCaseR t x t2)   = ECase (uneval t) (Match (bot, bot) (x, uneval t2))
    uneval (TIfThen t t1)    = EIf (uneval t) (uneval t1) bot
    uneval (TIfElse t t2)    = EIf (uneval t) bot (uneval t2)
    uneval (TIfExn t)        = EIf (uneval t) bot bot
    uneval (TCall t1 t2 _ _) = EApp (uneval t1) (uneval t2)
    uneval (TCallExn t1 t2)  = EApp (uneval t1) (uneval t2)
    uneval (TRef _ t)        = ERef (uneval t)
    uneval (TDeref _ t)      = EDeref (uneval t)
    uneval (TAssign _ t1 t2) = EAssign (uneval t1) (uneval t2)
    uneval (TRaise t)        = ERaise (uneval t)
    uneval (TTry t)          = ECatch (uneval t) bot bot
    uneval (TTryWith t x h)  = ECatch (uneval t) x (uneval h)
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

-- fvsK.  Calculates free vars of closure.
-- TODO: use ordered sets
class FVs a where
    fvs :: a -> [Var]

instance FVs a => FVs (Syntax a) where
    fvs (Var x)       = [x]
    fvs (Let x e1 e2) = delete x (fvs e1 `union` fvs e2)
    fvs  Unit         = []
    fvs (Op _ exps)   = concat (Prelude.map fvs exps)
    fvs (CBool _)     = []
    fvs (CInt _)      = []
    fvs (CString _)   = []
    fvs (Pair e1 e2)  = fvs e1 `union` fvs e2
    fvs (Fst e)       = fvs e
    fvs (Snd e)       = fvs e
    fvs (InL e)       = fvs e
    fvs (InR e)       = fvs e
    fvs (Fun k)       = fvs k
    fvs (Roll _ e)    = fvs e
    fvs (Unroll _ e)  = fvs e
    fvs (Seq e1 e2)   = fvs e1 `union` fvs e2
    fvs  Hole         = []

instance FVs Exp where
    fvs (EIf e1 e2 e3)  = fvs e1 `union` fvs e2 `union` fvs e3
    fvs (ECase e m)     = fvs e `union` fvs m
    fvs (EApp e1 e2)    = fvs e1 `union` fvs e2
    fvs (ETrace e)      = fvs e
    fvs (ERaise e)      = fvs e
    fvs (ECatch e x e1) = fvs e `union` (delete x (fvs e1))
    fvs (ERef e)        = fvs e
    fvs (EDeref e)      = fvs e
    fvs (EAssign e1 e2) = fvs e1 `union` fvs e2
    fvs (Exp e)         = fvs e

instance FVs Match where
    fvs (Match (x, e1) (y, e2)) =
        (fvs e1 \\ maybeToList x) `union` (fvs e2 \\ maybeToList y)

instance FVs a => FVs (Code a) where
    fvs k = let vs = fvs (funBody k)
            in delete (funName k) (delete (funArg k) vs)

instance FVs Trace where
    fvs (TIfThen t t1)     = fvs t `union` fvs t1
    fvs (TIfElse t t2)     = fvs t `union` fvs t2
    fvs (TIfExn t)         = fvs t
    fvs (TCaseL t v t1)    = fvs t `union` (fvs t1 \\ maybeToList v)
    fvs (TCaseR t v t2)    = fvs t `union` (fvs t2 \\ maybeToList v)
    fvs (TCall t1 t2 _ t)  = fvs t1 `union` fvs t2 `union` fvs t
    fvs (TCallExn t1 t2)   = fvs t1 `union` fvs t2
    fvs (TRef _ t)         = fvs t
    fvs (TDeref _ t)       = fvs t
    fvs (TAssign _ t1 t2)  = fvs t1 `union` fvs t2
    fvs (TRaise t)         = fvs t
    fvs (TTry t)           = fvs t
    fvs (TTryWith t1 x t2) = fvs t1 `union` (delete x (fvs t2))
    fvs (TExp e)           = fvs e
    fvs (TSlicedHole _ _)  = []

promote :: Value -> Value
promote VStar               = VStar
promote VHole               = VStar
promote VUnit               = VUnit
promote (VException e)      = VException e
promote (VBool b)           = VBool b
promote (VInt i)            = VInt i
promote (VString s)         = VString s
promote (VPair v1 v2)       = VPair (promote v1) (promote v2)
promote (VInL v)            = VInL (promote v)
promote (VInR v)            = VInR (promote v)
promote (VRoll tv v)        = VRoll tv (promote v)
promote (VStoreLoc l)       = VStoreLoc l
promote (VClosure k env)    = VClosure k (fmap promote env)
promote (VTrace v t env st) = VTrace (promote v) t (fmap promote env)
                                     (fmap promote st)
promote (VExp     e env)    = VExp e (fmap promote env)

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

-- JSTOLAREK: instances below completely ignore new constructors related to
-- references and exceptions.  I'm leaving them out for now to make sure that
-- their absence indeed causes an error when it should
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
    leq (TIfThen t t1) (TIfThen t' t1')
        = t `leq` t' && t1 `leq` t1'
    leq (TIfElse t t2) (TIfElse t' t2')
        = t `leq` t' && t2 `leq` t2'
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
    lub (TIfThen t t1) (TIfThen t' t1')
        = TIfThen (t `lub` t') (t1 `lub` t1')
    lub (TIfElse t t2) (TIfElse t' t2')
        = TIfElse (t `lub` t') (t2 `lub` t2')
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
    match (VStoreLoc l) (VStoreLoc l') (VStoreLoc l'') = l == l' && l == l''
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
    extract (VStoreLoc  l) (VStoreLoc  l') | l == l' = VStoreLoc l
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
