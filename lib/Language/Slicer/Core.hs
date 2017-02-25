{-# LANGUAGE DeriveAnyClass         #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE PatternSynonyms        #-}

module Language.Slicer.Core
    ( -- * Abstract syntax
      Syntax(..), Value(..), Outcome(..)
    , Type(..), Ctx, Code(..), Match(..), ReturnType(..)
    , Exp( EVar, ELet, EUnit, EBool, EInt, EDouble, EString, EPair, EFst, ESnd
         , EInL, EInR, EFun, ERoll, EUnroll, EHole, ESeq
         , .. )
    , Trace ( TVar, TLet, TUnit, TBool, TInt, TDouble, TString, TPair, TFst
            , TSnd, TInL, TInR, TFun, TRoll, TUnroll, THole, TSeq, .. )

    -- * Helper functions for AST
    , isRefTy, isArrTy, isFunTy, isCondTy, isExnTy, isPairTy, fstTy, sndTy
    , isRaise, isExn, isTHole

    , getVal, getExn
    -- * Store abstraction
    , Store, StoreLabel, StoreLabels, emptyStore, singletonStoreLabel
    , storeDeref, storeInsert, storeUpdate, storeUpdateHole
    , existsInStore, storeLookup, storeWrites, allStoreHoles

    , Pattern(extract), Valuable(..)

      -- * Built-in operators
    , commonOps, intBinOps, doubleBinOps, ordOps, boolRelOps, boolUnOps
    , isCommonOp, isIntBinOp, isDoubleBinOp, isOrdOp, isBoolRelOp, isBoolUnOp

      -- * Lables
    , Lab( unL ), mkL

      -- * Free variables
    , FVs(..)
    ) where


import           Language.Slicer.Env
import           Language.Slicer.Primitives
import           Language.Slicer.UpperSemiLattice

import           Control.DeepSeq    ( NFData                                  )
import           Control.Exception ( assert      )
import           Data.Map as Map    ( Map, fromList, mapWithKey, keys, member )
import           Data.Maybe
import qualified Data.Foldable as F ( all                                     )
import qualified Data.IntMap as M
import           Data.List          ( union, delete, (\\)                     )
import qualified Data.Hashable as H ( hash                                    )
import qualified Data.Set as S
import           GHC.Generics       ( Generic                                 )
import           Text.PrettyPrint.HughesPJClass

data Type = IntTy | BoolTy | UnitTy | StringTy | DoubleTy
          | PairTy Type Type | SumTy Type Type | FunTy Type Type
          | RecTy TyVar Type | TyVar TyVar
          | HoleTy
          -- Reference type
          | RefTy Type
          -- Array type
          | ArrTy Type
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
    DoubleTy     == DoubleTy       = True
    PairTy t1 t2 == PairTy t1' t2' = t1 == t1' && t2 == t2'
    SumTy  t1 t2 == SumTy  t1' t2' = t1 == t1' && t2 == t2'
    FunTy  t1 t2 == FunTy  t1' t2' = t1 == t1' && t2 == t2'
    RecTy  t1 t2 == RecTy  t1' t2' = t1 == t1' && t2 == t2'
    TyVar t      == TyVar t'       = t == t'
    RefTy t      == RefTy t'       = t == t'
    ArrTy t      == ArrTy t'       = t == t'
    TraceTy t    == TraceTy t'     = t == t'
    _            == _              = False

-- | Is reference type?
isRefTy :: Type -> Bool
isRefTy (RefTy _) = True
isRefTy ExnTy     = True
isRefTy _         = False

-- | Is array type?
isArrTy :: Type -> Bool
isArrTy (ArrTy _) = True
isArrTy ExnTy     = True
isArrTy _         = False

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
fstTy (ArrTy  t  ) = t
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
    leq  DoubleTy         DoubleTy          = True
    leq  ExnTy            ExnTy             = True
    leq (PairTy ty1 ty2) (PairTy ty1' ty2') = ty1 `leq` ty1' && ty2 `leq` ty2'
    leq (SumTy  ty1 ty2) (SumTy  ty1' ty2') = ty1 `leq` ty1' && ty2 `leq` ty2'
    leq (FunTy  ty1 ty2) (FunTy  ty1' ty2') = ty1 `leq` ty1' && ty2 `leq` ty2'
    leq (RecTy  a ty   ) (RecTy  a' ty'   ) = a == a' && ty `leq` ty'
    leq (TyVar  a      ) (TyVar  b        ) = a == b
    leq (RefTy   ty    ) (RefTy   ty'     ) = ty `leq` ty'
    leq (ArrTy   ty    ) (ArrTy   ty'     ) = ty `leq` ty'
    leq (TraceTy ty    ) (TraceTy ty'     ) = ty `leq` ty'
    leq _                _                  = error "UpperSemiLattice Type: leq"

    lub HoleTy   ty       = ty
    lub ty       HoleTy   = ty
    lub IntTy    IntTy    = IntTy
    lub BoolTy   BoolTy   = BoolTy
    lub UnitTy   UnitTy   = UnitTy
    lub DoubleTy DoubleTy = DoubleTy
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
    lub (ArrTy ty) (ArrTy ty')
        = ArrTy (ty `lub` ty')
    lub (TraceTy ty) (TraceTy ty')
        = TraceTy (ty `lub` ty')
    lub a b = error $ "UpperSemiLattice Type: error taking lub of " ++
                      show a ++ " and " ++ show b

instance Pretty Type where
    pPrint BoolTy   = text "bool"
    pPrint IntTy    = text "int"
    pPrint DoubleTy = text "double"
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
    pPrint (ArrTy ty)   = text "array" <> parens (pPrint ty)
    pPrint (TraceTy ty) = text "trace" <> parens (pPrint ty)

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
              | CDouble Double
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
         | EOp Primitive [Exp]
           -- run-time tracing
         | ETrace Exp
         -- References
         | ERef Exp | EDeref Exp | EAssign Exp Exp
         | EWhile Exp Exp
         -- Arrays
         | EArr Exp Exp | EArrGet Exp Exp | EArrSet Exp Exp Exp
         -- Exceptions
         | ERaise Exp | ETryWith Exp Var Exp
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

pattern EDouble :: Double -> Exp
pattern EDouble d = Exp (CDouble d)

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
           | TOp Bool Primitive [Trace]
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

-- JSTOLAREK: rename to TRaise
isRaise :: Trace -> Bool
isRaise (TRaise _) = True
isRaise _          = False

isExn :: Trace -> Bool
isExn (TVar _)                 = False
isExn (TLet _ t1 t2)           = isExn t1 || isExn t2
isExn (TUnit)                  = False
isExn (TBool _)                = False
isExn (TInt _)                 = False
isExn (TDouble _)              = False
isExn (TString _)              = False
isExn (TOp f _ ts)             = f || any isExn ts
isExn (TPair t1 t2)            = isExn t1 || isExn t2
isExn (TFst t)                 = isExn t
isExn (TSnd t)                 = isExn t
isExn (TInL t)                 = isExn t
isExn (TInR t)                 = isExn t
isExn (TFun _)                 = False
isExn (TRoll _tv t)            = isExn t
isExn (TUnroll _tv t)          = isExn t
isExn (THole)                  = False
isExn (TSeq t1 t2)             = isExn t1 || isExn t2
isExn (TIfThen t1 t2)          = isExn t1 || isExn t2
isExn (TIfElse t1 t2)          = isExn t1 || isExn t2
isExn (TIfExn t)               = isExn t
isExn (TCaseL t1 _ t2)         = isExn t1 || isExn t2
isExn (TCaseR t1 _ t2)         = isExn t1 || isExn t2
isExn (TCall t1 t2 _ k)        = isExn t1 || isExn t2 || isExn (funBody k)
isExn (TCallExn t1 t2)         = isExn t1 || isExn t2
isExn (TSlicedHole _ RetRaise) = True
isExn (TSlicedHole _ RetValue) = False
isExn (TRef _ t)               = isExn t
isExn (TDeref _ t)             = isExn t
isExn (TAssign _ t1 t2)        = isExn t1 || isExn t2
isExn (TRaise _)               = True     -- whether or not subtrace raises
isExn (TTry _)                 = False    -- subtrace is masked
isExn (TTryWith _ _ t2)        = isExn t2 -- first subtrace is masked
isExn e                        = error ("isExn: this case should be impossible, e = " ++ show e)


isTHole :: Trace -> Bool
isTHole THole             = True
isTHole (TSlicedHole _ _) = True
isTHole _                 = False

-- Note [Maybe trace labels]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- Labels in reference trace constructs are Maybes because it is possible that
-- the the enclosed expression raises an exception instead of evaluating to a
-- label value.  In case of assignment StoreLabel is Nothing only if LHS of the
-- assignment raises an exception.  If the RHS of the assignment that raises an
-- exception we store tha label.  This is required for backwards slicing.

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

pattern TDouble :: Double -> Trace
pattern TDouble d = TExp (CDouble d)

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

data Value = VBool Bool | VInt Int | VDouble Double | VUnit | VString String
           | VPair Value Value
           | VInL Value | VInR Value
           | VRoll TyVar Value
           | VClosure (Code Exp) (Env Value)
           | VHole | VStar
           | VExp Exp (Env Value)
           -- mutable store locations
           | VStoreLoc StoreLabel
           -- run-time traces
           | VTrace Outcome Trace (Env Value) Store
           deriving (Show, Eq, Ord, Generic, NFData)

data Outcome = ORet Value | OExn Value | OHole | OStar
             deriving (Show, Eq, Ord, Generic, NFData)

getVal :: Outcome -> Value
getVal (ORet v) = v
getVal _ = VHole

getExn :: Outcome -> Value
getExn (OExn v) = v
getExn _ = VHole

class Valuable a where
    toValue :: a -> Value

instance Valuable Int where
    toValue i = VInt i

instance Valuable Bool where
    toValue b = VBool b

instance Valuable Double where
    toValue d = VDouble d

instance Valuable () where
    toValue () = VUnit

-- fvsK.  Calculates free vars of closure.
-- TODO: use ordered sets
class FVs a where
    fvs :: a -> [Var]

instance FVs a => FVs (Syntax a) where
    fvs (Var x)       = [x]
    fvs (Let x e1 e2) = delete x (fvs e1 `union` fvs e2)
    fvs  Unit         = []
    fvs (CBool _)     = []
    fvs (CInt _)      = []
    fvs (CDouble _)   = []
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
    fvs (EIf e1 e2 e3)    = fvs e1 `union` fvs e2 `union` fvs e3
    fvs (ECase e m)       = fvs e `union` fvs m
    fvs (EApp e1 e2)      = fvs e1 `union` fvs e2
    fvs (EOp _ exps)      = concat (Prelude.map fvs exps)
    fvs (ETrace e)        = fvs e
    fvs (ERaise e)        = fvs e
    fvs (ETryWith e x e1) = fvs e `union` (delete x (fvs e1))
    fvs (ERef e)          = fvs e
    fvs (EDeref e)        = fvs e
    fvs (EAssign e1 e2)   = fvs e1 `union` fvs e2
    fvs (EWhile e1 e2)    = fvs e1 `union` fvs e2
    fvs (EArr e1 e2)      = fvs e1 `union` fvs e2
    fvs (EArrGet e1 e2)   = fvs e1 `union` fvs e2
    fvs (EArrSet e1 e2 e3)= fvs e1 `union` fvs e2 `union` fvs e3
    fvs (Exp e)           = fvs e

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
    fvs (TOp _ _ exps)     = concat (Prelude.map fvs exps)
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
promote (VBool b)           = VBool b
promote (VInt i)            = VInt i
promote (VDouble d)         = VDouble d
promote (VString s)         = VString s
promote (VPair v1 v2)       = VPair (promote v1) (promote v2)
promote (VInL v)            = VInL (promote v)
promote (VInR v)            = VInR (promote v)
promote (VRoll tv v)        = VRoll tv (promote v)
promote (VStoreLoc l)       = VStoreLoc l
promote (VClosure k env)    = VClosure k (fmap promote env)
promote (VTrace r t env (Store refs refCount)) =
    VTrace (promoteOutcome r) t (fmap promote env) (Store (fmap promote refs) refCount)
promote (VExp     e env)    = VExp e (fmap promote env)

promoteOutcome :: Outcome -> Outcome
promoteOutcome OStar = OStar
promoteOutcome OHole = OStar
promoteOutcome (OExn v) = OExn (promote v)
promoteOutcome (ORet v) = ORet (promote v)

instance UpperSemiLattice Value where
    bot                                = VHole

    leq VHole _                        = True
    leq VStar VHole                    = False
    leq VStar v                        = promote v == v
    leq VUnit VUnit                    = True
    leq (VBool b) (VBool b')           = b == b'
    leq (VInt i) (VInt i')             = i == i'
    leq (VDouble d) (VDouble d')       = d == d'
    leq (VString i) (VString i')       = i == i'
    leq (VPair v1 v2) (VPair v1' v2')  = v1 `leq` v1' && v2 `leq` v2'
    leq (VInL v) (VInL v')             = v `leq` v'
    leq (VInR v) (VInR v')             = v `leq` v'
    leq (VRoll tv v) (VRoll tv' v')    | tv == tv' = v `leq` v'
    leq (VStoreLoc i) (VStoreLoc i')   = i == i'
    leq (VClosure k env) (VClosure k' env')
        = k `leq` k' && env `leq` env'
    leq a b = error $ "UpperSemiLattice Value: error taking leq of " ++
                      show a ++ " and " ++ show b

    lub  VHole         v               = v
    lub  v             VHole           = v
    lub  VStar         v               = promote v
    lub  v             VStar           = promote v
    lub  VUnit         VUnit           = VUnit
    lub (VBool b)     (VBool b')       | b == b' = VBool b
    lub (VInt i)      (VInt i')        | i == i' = VInt i
    lub (VDouble d) (VDouble d')       | d == d' = VDouble d
    lub (VString i)   (VString i')     | i == i' = VString i
    lub (VPair v1 v2) (VPair v1' v2')  = VPair (v1 `lub` v1') (v2 `lub` v2')
    lub (VInL v)      (VInL v')        = VInL (v `lub` v')
    lub (VInR v)      (VInR v')        = VInR (v `lub` v')
    lub (VRoll tv v)  (VRoll tv' v')   | tv == tv' = VRoll tv (v `lub` v')
    lub (VStoreLoc i) (VStoreLoc i')   | i == i' = VStoreLoc i
    lub (VClosure k env) (VClosure k' env')
        = VClosure (k `lub` k') (env `lub` env')
    lub a b = error $ "UpperSemiLattice Value: error taking lub of " ++
                      show a ++ " and " ++ show b


instance UpperSemiLattice Outcome where
    leq (ORet v) (ORet v') = leq v v'
    leq (OExn v) (OExn v') = leq v v'
    leq (OHole) _ = True
    leq (OStar) (OHole) = False -- order matters
    leq (OStar) _ = True
    leq _ _ = False

    lub (ORet v) (ORet v') = ORet (lub v v')
    lub (OExn v) (OExn v') = OExn (lub v v')
    lub (OHole) v = v
    lub v (OHole) = v
    lub (OStar) v = promoteOutcome v  -- order matters here
    lub v (OStar) = promoteOutcome v
    lub a b = error $ "UpperSemiLattice Value: error taking lub of " ++
                      show a ++ " and " ++ show b
    bot = OHole


instance (UpperSemiLattice a, Show a) => UpperSemiLattice (Syntax a) where
    bot                                = Hole

    leq Hole _                        = True
    leq (Var x) (Var x')               = x `leq` x'
    leq (Let x e1 e2) (Let x' e1' e2') = x `leq` x' && e1 `leq` e1' && e2 `leq` e2'
    leq (CBool b) (CBool b')           = b == b'
    leq (CInt i) (CInt j)              = i == j
    leq (CDouble d) (CDouble d')       = d == d'
    leq (CString i) (CString j)        = i == j
    leq Unit Unit                      = True
    leq (Pair e1 e2) (Pair e1' e2')    = e1 `leq` e1' && e2 `leq` e2'
    leq (Fst e) (Fst e')               = e `leq` e'
    leq (Snd e) (Snd e')               = e `leq` e'
    leq (InL e) (InL e')               = e `leq` e'
    leq (InR e) (InR e')               = e `leq` e'
    leq (Fun k) (Fun k')               = k `leq` k'
    leq (Roll tv e) (Roll tv' e')      | tv == tv' = e `leq` e'
    leq (Unroll tv e) (Unroll tv' e')  | tv == tv' = e `leq` e'
    leq (Seq e1 e2) (Seq e1' e2')      = e1 `leq` e1' && e2 `leq` e2'
    leq a b = error $ "UpperSemiLattice Syntax: error taking leq of " ++
                      show a ++ " and " ++ show b


    lub Hole e                         = e
    lub e Hole                         = e
    lub (Var x) (Var x')               = Var (x `lub` x')
    lub (Let x e1 e2) (Let x' e1' e2') = Let (x `lub` x') (e1 `lub` e1') (e2 `lub` e2')
    lub (CInt i) (CInt j)              | i == j  = CInt i
    lub (CDouble d) (CDouble d')       | d == d' = CDouble d
    lub (CString i) (CString j)        | i == j  = CString i
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
    lub (Seq e1 e2) (Seq e1' e2')      = Seq (e1 `lub` e1') (e2 `lub` e2')
    lub a b = error $ "UpperSemiLattice Syntax: error taking lub of " ++
                      show a ++ " and " ++ show b

instance UpperSemiLattice Exp where
    bot                                = Exp Hole

    leq EHole _                        = True
    leq (Exp e1) (Exp e2)              = e1 `leq` e2
    leq (EIf e e1 e2) (EIf e' e1' e2') = e `leq` e' && e1 `leq` e1' && e2 `leq` e2'
    leq (ECase e m) (ECase e' m')      = e `leq` e' && m `leq` m'
    leq (EApp e1 e2) (EApp e1' e2')    = e1 `leq`  e1' && e2 `leq` e2'
    leq (EOp op es) (EOp op' es')
        | op == op' && length es == length es'
        = all (\(x,y) -> x `leq` y) (zip es es')
    leq (ETrace e) (ETrace e')
        = e `leq` e'
    leq (ERef   e1) (ERef   e2)        = e1 `leq` e2
    leq (EDeref e1) (EDeref e2)        = e1 `leq` e2
    leq (EAssign e1 e2) (EAssign e1' e2')
        = e1 `leq`  e1' && e2 `leq` e2'
    leq (EWhile e1 e2) (EWhile e1' e2')
        = e1 `leq`  e1' && e2 `leq` e2'
    leq (EArr   e1 e2) (EArr   e1' e2')
        = e1 `leq`  e1' && e2 `leq` e2'
    leq (EArrGet e1 e2) (EArrGet e1' e2')
        = e1 `leq`  e1' && e2 `leq` e2'
    leq (EArrSet e1 e2 e3) (EArrSet e1' e2' e3')
        = e1 `leq`  e1' && e2 `leq` e2' && e3 `leq` e3'
    leq (ERaise e1) (ERaise e2)        = e1 `leq` e2
    leq (ETryWith e1 x e2) (ETryWith e1' x' e2')
        = e1 `leq` e1' && x `leq` x' && e2 `leq` e2'
    leq a b = error $ "UpperSemiLattice Exp: error taking leq of " ++
                      show a ++ " and " ++ show b

    lub EHole e                        = e
    lub e EHole                        = e
    lub (Exp e1) (Exp e2)              = Exp (e1 `lub` e2)
    lub (EIf e e1 e2) (EIf e' e1' e2') = EIf (e `lub` e') (e1 `lub` e1') (e2 `lub` e2')
    lub (ECase e m) (ECase e' m')      = ECase (e `lub` e') (m `lub` m')
    lub (EApp e1 e2) (EApp e1' e2')    = EApp (e1 `lub` e1') (e2 `lub` e2')
    lub (EOp op es) (EOp op' es')
        | op == op' && length es == length es'
        = EOp op (map (\(x,y) -> x `lub` y) (zip es es'))
    lub (ETrace e) (ETrace e')
        = ETrace (e `lub` e')
    lub (ERef   e1) (ERef   e2)        = ERef   (e1 `lub` e2)
    lub (EDeref e1) (EDeref e2)        = EDeref (e1 `lub` e2)
    lub (EAssign e1 e2) (EAssign e1' e2')
        = EAssign (e1 `lub` e1') (e2 `lub` e2')
    lub (EWhile e1 e2) (EWhile e1' e2')
        = EWhile (e1 `lub` e1') (e2 `lub` e2')
    lub (EArr e1 e2) (EArr e1' e2')    = EArr   (e1 `lub` e1') (e2 `lub` e2')
    lub (EArrGet e1 e2) (EArrGet e1' e2')
        = EArrGet (e1 `lub` e1') (e2 `lub` e2')
    lub (EArrSet e1 e2 e3) (EArrSet e1' e2' e3')
        = EArrSet (e1 `lub` e1') (e2 `lub` e2') (e3 `lub` e3')
    lub (ERaise e1) (ERaise e2)        = ERaise (e1 `lub` e2)
    lub (ETryWith e1 x e2) (ETryWith e1' x' e2')
        = ETryWith (e1 `lub` e1') (x `lub` x') (e2 `lub` e2')
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
    bot                = THole

    leq t _ | isTHole t = True
    leq (TExp t1) (TExp t2) = t1 `leq`  t2
    leq (TIfThen t t1) (TIfThen t' t1')
        = t `leq` t' && t1 `leq` t1'
    leq (TIfElse t t2) (TIfElse t' t2')
        = t `leq` t' && t2 `leq` t2'
    leq (TIfExn t) (TIfExn t')
        = t `leq` t'
    leq (TOp f op es) (TOp f' op' es')
        | f == f' && op == op' && length es == length es'
        = all (\(x,y) -> x `leq` y) (zip es es')
    leq (TCaseL t x t1) (TCaseL t' x' t1')
        = t `leq` t' && x == x' && t1 `leq` t1'
    leq (TCaseR t x t2) (TCaseR t'  x' t2')
        = t `leq` t' && x == x' && t2 `leq` t2'
    leq (TCall t1 t2 k t) (TCall t1' t2' k' t')
        = t1 `leq` t1' && t2 `leq` t2' && k `leq` k' && t `leq` t'
    leq (TCallExn t1 t2) (TCallExn t1' t2')
        = t1 `leq` t1' && t2 `leq` t2'
    leq (TRef l t) (TRef l' t') | l == l' = t `leq` t'
    leq (TDeref l t) (TDeref l' t') | l == l' = t `leq` t'
    leq (TAssign l t1 t2) (TAssign l' t1' t2') | l == l'
        = t1 `leq` t1' && t2 `leq` t2'
    leq (TRaise t) (TRaise t') = t `leq` t'
    leq (TTry t) (TTry t') = t `leq` t'
    leq (TTryWith t1 x t2) (TTryWith t1' x' t2')
        = t1 `leq` t1' && x `leq` x' && t2 `leq` t2'
    leq a b = error $ "UpperSemiLattice Trace: error taking leq of " ++
                      show a ++ " and " ++ show b

    lub t1 t2 | isTHole t1 = t2
    lub t1 t2 | isTHole t2 = t1
    lub (TExp e1) (TExp e2) = TExp (e1 `lub` e2)
    lub (TIfThen t t1) (TIfThen t' t1')
        = TIfThen (t `lub` t') (t1 `lub` t1')
    lub (TIfElse t t2) (TIfElse t' t2')
        = TIfElse (t `lub` t') (t2 `lub` t2')
    lub (TIfExn t) (TIfExn t')
        = TIfExn (t `lub` t')
    lub (TOp f op es) (TOp f' op' es')
        | f == f' && op == op' && length es == length es'
        = TOp f op (map (\(x,y) -> x `lub` y) (zip es es'))
    lub (TCaseL t x t1) (TCaseL t' x' t1')
        = TCaseL (t `lub` t') (x `lub` x') (t1 `lub` t1')
    lub (TCaseR t x t2) (TCaseR t' x' t2')
        = TCaseR (t `lub` t') (x `lub` x') (t2 `lub` t2')
    lub (TCall t1 t2 k t) (TCall t1' t2' k' t')
        = TCall (t1 `lub` t1') (t2 `lub` t2') (k `lub` k') (t `lub` t')
    lub (TCallExn t1 t2) (TCallExn t1' t2')
        = TCallExn (t1 `lub` t1') (t2 `lub` t2')
    lub (TRef l t) (TRef l' t') | l == l' = TRef l (t `lub` t')
    lub (TDeref l t) (TDeref l' t') | l == l' = TDeref l (t `lub` t')
    lub (TAssign l t1 t2) (TAssign l' t1' t2') | l == l'
        = TAssign l (t1 `lub` t1') (t2 `lub` t2')
    lub (TRaise t) (TRaise t') = TRaise (t `lub` t')
    lub (TTry t) (TTry t') = TTry (t `lub` t')
    lub (TTryWith t1 x t2) (TTryWith t1' x' t2')
        = TTryWith (t1 `lub` t1') (x `lub` x') (t2 `lub` t2')
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
    match (VDouble dp)  (VDouble d)   (VDouble d')    = dp == d && dp == d'
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
    extract (VDouble dp)   (VDouble d)     | dp == d = VDouble d
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


instance Pattern Outcome where
    match (OStar) v v' = v == v'
    match (OHole) _ _ = True
    match (ORet p) (ORet v1) (ORet v2) = (match p v1 v2)
    match (OExn p) (OExn v1) (OExn v2) = (match p v1 v2)
    match _ _ _ = False

    extract (OStar) v = v
    extract (OHole) _ = OHole
    extract (ORet p) (ORet v) = ORet (extract p v)
    extract (OExn p) (OExn v) = OExn (extract p v)
    extract p v = error ("extract only defined if p <= v, but p is " ++
                         show p ++ " and v is " ++ show v)


instance (Pattern a, UpperSemiLattice a) => Pattern (Env a) where
    match (penv@(Env penv')) env1 env2
        = all (\x -> match (lookupEnv' penv x) (lookupEnv' env1 x)
                           (lookupEnv' env2 x)) (Map.keys penv')
    extract (Env penv') env
        = Env (Map.mapWithKey (\x p -> extract p (lookupEnv' env x)) penv')

--------------------------------------------------------------------------------
--                           REFERENCE STORE                                  --
--------------------------------------------------------------------------------

-- | Internal labels used during runtime to identify store locations
newtype StoreLabel  = StoreLabel Int
    deriving ( Show, Eq, Ord, Generic, NFData )

-- | A set of store labels
newtype StoreLabels = StoreLabels (S.Set StoreLabel)
    deriving ( Show, Eq, Ord, Generic, NFData )

instance Valuable StoreLabel where
    toValue = VStoreLoc

-- | Reference store
data Store = Store (M.IntMap Value) Int
             deriving ( Show, Eq, Ord, Generic, NFData )

-- | Empty reference store
emptyStore :: Store
emptyStore = Store M.empty 0

-- | Dereference a label.  If label is absent in the store return bottom
storeDeref :: Store -> StoreLabel -> Value
storeDeref (Store refs _) (StoreLabel label) =
    if (label `M.member` refs)
    then refs M.! label
    else bot

storeLookup :: Store -> StoreLabel -> Maybe Value
storeLookup (Store refs _) (StoreLabel label) =
    M.lookup label refs

-- | Insert new value into a store.  Return new store and label under which the
-- value was allocated
storeInsert :: Store -> Value -> (Store, StoreLabel)
storeInsert (Store refs refCount) v =
    (Store (M.insert refCount v refs) (refCount + 1), StoreLabel refCount)

-- | Update a label already present in a store
storeUpdate :: Store -> StoreLabel -> Value -> Store
storeUpdate (Store refs refCount) (StoreLabel l) v =
    assert (l `M.member` refs)   $
    Store (M.insert l v refs) refCount

-- | Update a label already present in a store to contain hole
storeUpdateHole :: Store -> StoreLabel -> Store
storeUpdateHole store label =
    storeUpdate store label VHole

-- | Check if a label is allocated in a store
existsInStore :: Store -> StoreLabel -> Bool
existsInStore (Store refs _) (StoreLabel label) =
    label `M.member` refs

-- | Return true if a label does not exists in a store or exsists and points to
-- a hole
isStoreHole :: Store -> StoreLabel -> Bool
isStoreHole (Store refs _) (StoreLabel label) =
    not (label `M.member` refs) || refs M.! label == VHole

-- | Check if all store labels are store holes (according to `isStoreHole`)
allStoreHoles :: Store -> StoreLabels -> Bool
allStoreHoles store (StoreLabels labels) =
    F.all (isStoreHole store) labels

-- | An empty set of store labels
emptyStoreLabels :: StoreLabels
emptyStoreLabels = StoreLabels S.empty

singletonStoreLabel :: StoreLabel -> StoreLabels
singletonStoreLabel l = StoreLabels (S.singleton l)

-- | Insert a label into a set of store labels
insertStoreLabel :: Maybe StoreLabel -> StoreLabels -> StoreLabels
insertStoreLabel Nothing   ls              = ls
insertStoreLabel (Just l) (StoreLabels ls) = StoreLabels (l `S.insert` ls)

-- | Union of two store label sets
unionStoreLabels :: StoreLabels -> StoreLabels -> StoreLabels
unionStoreLabels (StoreLabels ls1) (StoreLabels ls2) =
    StoreLabels (ls1 `S.union` ls2)

-- | Get list of labels that a trace writes to
storeWrites :: Trace -> StoreLabels
-- relevant store assignments
storeWrites (TRef l t) =
    l `insertStoreLabel` storeWrites t
storeWrites (TAssign l t1 t2) =
    l `insertStoreLabel` storeWrites t1 `unionStoreLabels`  storeWrites t2
-- sliced hole annotated with store labels
storeWrites (TSlicedHole ls _) = ls
storeWrites (TIfThen t1 t2)    =
    storeWrites t1 `unionStoreLabels` storeWrites t2
storeWrites (TIfElse t1 t2)    =
    storeWrites t1 `unionStoreLabels` storeWrites t2
storeWrites (TIfExn t)         =
    storeWrites t
storeWrites (TCaseL t1 _ t2)   =
    storeWrites t1 `unionStoreLabels` storeWrites t2
storeWrites (TCaseR t1 _ t2)   =
    storeWrites t1 `unionStoreLabels` storeWrites t2
storeWrites (TCall t1 t2 _ (Rec _ _ t3 _)) =
    storeWrites t1 `unionStoreLabels` storeWrites t2
                   `unionStoreLabels` storeWrites t3
storeWrites (TCallExn t1 t2)   =
    storeWrites t1 `unionStoreLabels` storeWrites t2
storeWrites (TDeref _ t)       = storeWrites t
storeWrites (TRaise t)         = storeWrites t
storeWrites (TTry t)           = storeWrites t
storeWrites (TTryWith t1 _ t2) =
    storeWrites t1 `unionStoreLabels` storeWrites t2
storeWrites (TLet _ t1 t2)     =
    storeWrites t1 `unionStoreLabels` storeWrites t2
storeWrites (TPair t1 t2)      =
    storeWrites t1 `unionStoreLabels` storeWrites t2
storeWrites (TSeq t1 t2)       =
    storeWrites t1 `unionStoreLabels` storeWrites t2
storeWrites (TOp _ _ ts)       =
    foldl (\acc t -> acc `unionStoreLabels` storeWrites t) emptyStoreLabels ts
storeWrites (TFst t)           = storeWrites t
storeWrites (TSnd t)           = storeWrites t
storeWrites (TInL t)           = storeWrites t
storeWrites (TInR t)           = storeWrites t
storeWrites (TRoll _ t)        = storeWrites t
storeWrites (TUnroll _ t)      = storeWrites t
storeWrites TUnit              = emptyStoreLabels
storeWrites (TVar _)           = emptyStoreLabels
storeWrites (TBool _)          = emptyStoreLabels
storeWrites (TInt _)           = emptyStoreLabels
storeWrites (TString _)        = emptyStoreLabels
storeWrites (TFun _)           = emptyStoreLabels
storeWrites THole              = emptyStoreLabels
storeWrites (TExp e)
    = error ("Impossible happened at storeWrites: " ++ show e)

--------------------------------------------------------------------------------
--              BUILT-IN ARITHMETIC AND LOGICAL OPERATORS                     --
--------------------------------------------------------------------------------

commonOps :: Eq a => Map Primitive ((a, a) -> Value)
commonOps = fromList
   [ (OpEq , toValue . uncurry (==))
   , (OpNeq, toValue . uncurry (/=))
   ]

intBinOps :: Map Primitive ((Int, Int) -> Value)
intBinOps = fromList
   [ (OpPlus , toValue . uncurry (+))
   , (OpMinus, toValue . uncurry (-))
   , (OpTimes, toValue . uncurry (*))
   , (OpDiv  , toValue . uncurry div)
   , (OpMod  , toValue . uncurry mod)
   ]

doubleBinOps :: Map Primitive ((Double, Double) -> Value)
doubleBinOps = fromList
   [ (OpPlus , toValue . uncurry (+))
   , (OpMinus, toValue . uncurry (-))
   , (OpTimes, toValue . uncurry (*))
   , (OpDiv  , toValue . uncurry (/))
   ]

ordOps :: Ord a => Map Primitive ((a, a) -> Value)
ordOps = fromList
   [ (OpLt , toValue . uncurry (<) )
   , (OpGt , toValue . uncurry (>) )
   , (OpLeq, toValue . uncurry (<=))
   , (OpGeq, toValue . uncurry (>=))
   ]

boolRelOps :: Map Primitive ((Bool, Bool) -> Value)
boolRelOps = fromList
   [ (OpAnd, toValue . uncurry (&&))
   , (OpOr , toValue . uncurry (||))
   ]

boolUnOps :: Map Primitive (Bool -> Value)
boolUnOps = fromList
   [ (OpNot, toValue . not) ]

isCommonOp :: Primitive -> Bool
-- instantiate type variable in commonOps to () to avoid type ambiguity
isCommonOp op = op `member` (commonOps :: Map Primitive (((), ()) -> Value))

isIntBinOp :: Primitive -> Bool
isIntBinOp op = op `member` intBinOps

isDoubleBinOp :: Primitive -> Bool
isDoubleBinOp op = op `member` doubleBinOps

isOrdOp :: Primitive -> Bool
isOrdOp op = op `member` (ordOps :: Map Primitive (((), ()) -> Value))

isBoolRelOp :: Primitive -> Bool
isBoolRelOp op = op `member` boolRelOps

isBoolUnOp :: Primitive -> Bool
isBoolUnOp op = op `member` boolUnOps
