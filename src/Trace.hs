module Trace where
import List(union, delete, (\\), intersperse,elem)

import Env
import LowerSemiLattice
import Data.Map as Map (Map, fromList, mapWithKey,keys, (!))
import Data.Int
import Data.HashTable(hashString)
import Text.PrettyPrint
import Util

import qualified Data.Set as Set



data Type = IntTy | BoolTy | UnitTy | StringTy
          | PairTy Type Type | SumTy Type Type | FunTy Type Type
          | RecTy TyVar Type | TyVar TyVar
          | HoleTy --
            -- Trace types
          | TraceTy Ctx Type
            deriving (Eq,Ord,Show)

instance LowerSemiLattice Type where
    bot = HoleTy
    leq HoleTy _ = True
    leq IntTy IntTy = True
    leq BoolTy BoolTy = True
    leq UnitTy UnitTy = True
    leq StringTy StringTy = True
    leq (PairTy ty1 ty2) (PairTy ty1' ty2') = ty1 `leq` ty1' && ty2 `leq` ty2'
    leq (SumTy ty1 ty2) (SumTy ty1' ty2') = ty1 `leq` ty1' && ty2 `leq` ty2'
    leq (FunTy ty1 ty2) (FunTy ty1' ty2') = ty1 `leq` ty1' && ty2 `leq` ty2'
    leq (RecTy a ty) (RecTy a' ty') = a == a' && ty `leq` ty'
    leq (TyVar a) (TyVar b) = a == b
    leq (TraceTy ctx ty) (TraceTy ctx' ty') = ctx `leq` ctx' && ty `leq` ty'
    lub HoleTy ty = ty
    lub ty HoleTy = ty
    lub IntTy IntTy = IntTy
    lub BoolTy BoolTy = BoolTy
    lub UnitTy UnitTy = UnitTy
    lub StringTy StringTy = StringTy
    lub (PairTy ty1 ty2) (PairTy ty1' ty2')
        = PairTy (ty1 `lub` ty1') (ty2 `lub` ty2')
    lub (SumTy ty1 ty2) (SumTy ty1' ty2')
        = SumTy (ty1 `lub` ty1') (ty2 `lub` ty2')
    lub (FunTy ty1 ty2) (FunTy ty1' ty2')
        = FunTy (ty1 `lub` ty1') (ty2 `lub` ty2')
    lub (RecTy a ty) (RecTy a' ty')
        | a == a'
        = (RecTy a  (ty `lub` ty'))
    lub (TyVar a) (TyVar b) | a == b = TyVar a
    lub (TraceTy ctx ty) (TraceTy ctx' ty')
        = TraceTy (ctx `lub` ctx') (ty `lub` ty')

instance PP Type where
    pp_partial (BoolTy) (BoolTy)  = text "bool"
    pp_partial IntTy IntTy = text "int"
    pp_partial StringTy StringTy = text "string"
    pp_partial UnitTy UnitTy = text "unit"
    pp_partial HoleTy HoleTy = sb (text "_")
    pp_partial (SumTy ty1 ty2) (SumTy ty1' ty2') =
        parens (pp_partial ty1 ty1' <+> text "+" <+> pp_partial ty2 ty2')
    pp_partial (PairTy ty1 ty2) (PairTy ty1' ty2') =
        parens (pp_partial ty1 ty1' <+> text "*" <+> pp_partial ty2 ty2')
    pp_partial (FunTy ty1 ty2) (FunTy ty1' ty2') =
        parens (pp_partial ty1 ty1' <+> text "->" <+> pp_partial ty2 ty2')
    pp_partial (TyVar v) (TyVar v') = pp_partial v v'
    pp_partial (RecTy a ty) (RecTy a' ty')
        | a == a'
        = text "rec" <+> pp a <+> text "." <+> pp_partial ty ty'
    pp_partial (TraceTy gamma ty) (TraceTy gamma' ty')
        = text "trace" <> parens (pp_partial gamma gamma' <> comma <> pp_partial ty ty')
    pp_partial HoleTy v = sb (pp v)
    pp v = pp_partial v v

type Ctx = Env Type


data Lab = L {unL ::String, hash::Int32}

instance Eq Lab where
    l1 == l2 = hash l1 == hash l2

instance Show Lab where
    showsPrec _ l = showString (unL l)


instance Ord Lab where
    compare (L s h ) (L s' h') = case compare h h'
                                 of EQ -> compare s s'
                                    o -> o

mkL :: String -> Lab
mkL s = L s (hashString s)

data Op = O String [Type] Type deriving (Show,Eq,Ord)


-- TODO: Get rid of type args?

opPlus = O "+" [IntTy, IntTy] IntTy
opMinus = O "-" [IntTy, IntTy] IntTy
opTimes = O "*" [IntTy, IntTy] IntTy
opDiv = O "/" [IntTy, IntTy] IntTy
opMod = O "mod" [IntTy, IntTy] IntTy
opIntEq = O "=" [IntTy, IntTy] BoolTy
opLt = O "<" [IntTy, IntTy] BoolTy
opGt = O ">" [IntTy, IntTy] BoolTy
opIntNeq = O "/=" [IntTy, IntTy] BoolTy
opLeq = O "<=" [IntTy, IntTy] BoolTy
opGeq = O ">=" [IntTy, IntTy] BoolTy

opAnd = O "&&" [BoolTy, BoolTy] BoolTy
opOr = O "||" [BoolTy, BoolTy] BoolTy
opBoolEq = O "=" [BoolTy, BoolTy] BoolTy
opNot = O "not" [BoolTy] BoolTy

optable = [opPlus, opMinus, opTimes, opDiv, opMod, opIntEq, opLt, opGt,
           opAnd, opOr, opBoolEq, opNot]



data Exp = Var Var | Let Var Exp Exp
         | Unit
         | CBool Bool | If Exp Exp Exp
         | CInt Int | Op Op [Exp]
         | CString String
         | Pair Exp Exp | Fst Exp | Snd Exp
         | InL Exp | InR Exp | Case Exp Match
         | Fun Code | App Exp Exp
         | Roll (Maybe TyVar) Exp | Unroll (Maybe TyVar) Exp
         -- trace forms
         | IfThen Trace Exp Exp Trace | IfElse Trace Exp Exp Trace
         | CaseL Trace Match Var Trace | CaseR Trace Match Var Trace
         | Call Trace Trace Code Code
         | Hole
           -- run-time tracing
         | Trace Exp
         | TraceVar Exp Var
         | TraceUpd Exp Var Exp
{-       | TraceVal Exp
         | TraceReplay Exp
-}
-- labels
         | Lab Exp Lab
         | EraseLab Exp Lab
           deriving (Eq,Show,Ord)



data Code = Rec {fn :: Var, arg :: Var, body ::Exp, label::Maybe Lab}
           deriving (Eq,Show,Ord)
data Match = Match {inL :: (Var,Exp), inR :: (Var,Exp)}
           deriving (Eq,Show,Ord)

data Value = VBool Bool | VInt Int | VUnit | VString String
           | VPair Value Value
           | VInL Value | VInR Value
           | VRoll (Maybe TyVar) Value
           | VClosure Code (Env Value)
           | VHole | VStar | VLabel Value Lab
             -- run-time traces
           | VTrace Value Trace (Env Value)
           deriving (Eq,Show,Ord)

instance PP Value where
    pp_partial (VBool b) (VBool b')
        | b == b'
        = text (if b then "true" else "false")
    pp_partial (VInt i) (VInt i')
        | i == i'
        = int i
    pp_partial (VString s) (VString s')
        | s == s'
        = text (show s)
    pp_partial (VUnit) (VUnit) = text "()"
    pp_partial (VPair v1 v2) (VPair v1' v2') =
        parens (pp_partial v1 v1' <> comma <> pp_partial v2 v2')
    pp_partial (VInL v) (VInL v') = text "inl" <> parens (pp_partial v v')
    pp_partial (VInR v) (VInR v') = text "inr"  <> parens (pp_partial v v')
    pp_partial (VRoll _ v) (VRoll _ v') = text "roll"<> parens (pp_partial v v')
    pp_partial (VClosure _ _) (VClosure _ _) = text "<fun>"
    pp_partial (VTrace _ _ _) (VTrace _ _ _) = text "<trace>"
    pp_partial VHole VHole = sb (text "_")
    pp_partial VHole v = sb (pp v)
    pp v = pp_partial v v

unlabel :: Value -> Value
unlabel (VLabel v l) = unlabel v
unlabel v            = v


erase_lab :: Value -> Lab -> Value
erase_lab VUnit l = VUnit
erase_lab (VBool b) l = VBool b
erase_lab (VInt i) l = VInt i
erase_lab (VPair v1 v2) l = VPair (erase_lab v1 l) (erase_lab v2 l)
erase_lab (VInL v) l = VInL (erase_lab v l)
erase_lab (VInR v) l = VInR (erase_lab v l)
erase_lab (VRoll tv v) l = VRoll tv (erase_lab v l)
erase_lab (VHole) l = VHole
erase_lab (VStar) l = VStar
erase_lab (VLabel v l') l = if l == l' then VHole else (VLabel (erase_lab v l) l')
erase_lab (VClosure k env) l = VClosure k (fmap (\x -> erase_lab x l) env)
erase_lab (VTrace v t env) l = VTrace (erase_lab v l) t (fmap (\x -> erase_lab x l) env)

-- convert first-order value-patterns to expressions
val2exp :: Value -> Exp
val2exp VHole = Hole
val2exp VUnit = Unit
val2exp (VBool b) = CBool b
val2exp (VInt i) = CInt i
val2exp (VString s) = CString s
val2exp (VPair v1 v2) = Pair (val2exp v1) (val2exp v2)
val2exp (VInL v) = InL (val2exp v)
val2exp (VInR v) = InR (val2exp v)
val2exp (VRoll tv v) = Roll tv (val2exp v)
val2exp (VLabel v l) = Lab (val2exp v) l

-- convert expressions which happens to be first-order value-patterns to value-patterns.
exp2val :: Exp -> Value
exp2val Hole = VHole
exp2val Unit = VUnit
exp2val (CBool b) = VBool b
exp2val (CInt i) = VInt i
exp2val (CString i) = VString i
exp2val (Pair v1 v2) = VPair (exp2val v1) (exp2val v2)
exp2val (InL v) = VInL (exp2val v)
exp2val (InR v) = VInR (exp2val v)
exp2val (Roll tv v) = VRoll tv (exp2val v)
exp2val (Lab v l) = VLabel (exp2val v) l

type Trace = Exp



instance PP Lab where
    pp (L x _) = text x
    pp_partial l l' | l == l' = pp l

instance PP Op where
    pp (O f _ _) = text f
    pp_partial op op' | op == op' = pp op

instance PP Exp where
    pp e = pp_partial e e
    pp_partial Hole Hole = sb (text "_")
    pp_partial Hole e = sb (pp e)
    pp_partial (Var x) (Var x') | x == x' = pp x
    pp_partial (Let x e1 e2) (Let x' e1' e2')
        | x == x'
        = text "let" <+> pp x <+> equals <+> pp_partial e1 e1' $$
          text "in" <+> pp_partial e2 e2'
    pp_partial Unit Unit = text "()"
    pp_partial (CBool b) (CBool b')
        | b == b'
        = if b then text "true" else text "false"
    pp_partial (If e e1 e2) (If e' e1' e2')
        = text "if" <+> pp_partial e e'
                $$ text "then" <+> pp_partial e1 e1'
                $$ text "else" <+> pp_partial e2 e2'
    pp_partial (CInt i) (CInt  i')
        | i == i'
        = int i
    pp_partial (CString s) (CString s')
        | s == s'
        = text ( show s)
    pp_partial (Op f es) (Op f' es')
        | f == f'
        = pp f <> parens (hcat (punctuate comma (map (\(e,e') -> pp_partial e e') (zip es es'))))
    pp_partial (Pair e1 e2) (Pair e1' e2')
        = parens (pp_partial e1 e1' <> comma <> pp_partial e2 e2')
    pp_partial (Fst e) (Fst e') = text "fst" <> parens(pp_partial e e')
    pp_partial (Snd e) (Snd e') = text "snd" <> parens(pp_partial e e')
    pp_partial (InL e) (InL e') = text "inl" <> parens(pp_partial e e')
    pp_partial (InR e) (InR e') = text "inr" <> parens(pp_partial e e')
    pp_partial (Case e m) (Case e' m') = text "case" <+> pp_partial e e' $$ (nest 2 ( pp_partial m m'))
    pp_partial (Fun k)  (Fun k') = pp_partial k k'
    pp_partial (App e1 e2) (App e1' e2') = parens (sep [pp_partial e1 e1',pp_partial e2 e2'])
    pp_partial (Roll tv e) (Roll tv' e')
        | tv == tv'
        = text "roll" <> parens (pp_partial e e')
    pp_partial (Unroll a e) (Unroll a' e')
        | a == a'
        = text "unroll" <> parens (pp_partial e e')
    pp_partial (Trace e) (Trace e') = text "trace" <> parens (pp_partial e e')
--    pp_partial (TraceReplay e) (TraceReplay e') = text "replay" <> parens (pp_partial e e')
--    pp_partial (TraceVal e) (TraceVal e') = text "val" <> parens (pp_partial e e')
    pp_partial (Lab e l) (Lab e' l')
        = (pp_partial e e') <+> text "@" <+> brackets( pp_partial l l')
    pp_partial (EraseLab e l) (EraseLab e' l')
        = (pp_partial e e') <+> text "//" <+> brackets( pp_partial l l')
    pp_partial (TraceVar e x) (TraceVar e' x')
        = (pp_partial e e') <> brackets( pp_partial x x')
    pp_partial (TraceUpd e1 x e2) (TraceUpd e1' x' e2')
        = (pp_partial e1 e1') <> brackets( pp_partial x x' <+> text ":=" <+> pp_partial e2 e2')
    pp_partial (IfThen t e1 e2 t1) (IfThen t' e1' e2' t1')
        = text "IF" <+> pp_partial t t'
          $$ text "THEN" <+> nest 2 (--pp_partial e1 e1' <+>
                                     brackets (pp_partial t1 t1'))
    -- $$ text "else" <+> nest 2 (pp_partial e2 e2')
    pp_partial (IfElse t e1 e2 t2) (IfElse t' e1' e2' t2')
        = text "IF" <+> pp_partial t t'
          -- $$ text "then" <+> pp_partial e1 e1'
          <+> text "ELSE" <+> nest 2 (--pp_partial e2 e2' $$
                                      brackets (pp_partial t2 t2'))
    pp_partial (CaseL t m x t1) (CaseL t' m' x' t1')
        | x == x'
        = text "CASE" <+> pp_partial t t' $$ nest 2 ( --pp_partial m m' $$
                                                      brackets( text "inl" <> parens (pp x) <> text "." <> pp_partial t1 t1'))
    pp_partial (CaseR t m x t2) (CaseR t' m' x' t2')
        | x == x'
        = text "CASE" <+> pp_partial t t' $$ nest 2 (
                                                     --pp_partial m m' $$
                                                      brackets( text "inr" <> parens (pp x) <> text "." <> pp_partial t2 t2'))
    pp_partial (Call t1 t2 k t) (Call t1' t2' k' t') =
        text "CALL" <> parens (pp_partial t1 t1' $$ nest 2 (pp_partial t2 t2')) $$ nest 2 ( brackets (--pp_partial k k' <+>
                                                                                                  pp_partial t t'))

instance PP Match where
    pp m = pp_partial m m
    pp_partial (Match (x,e1) (y,e2)) (Match (x',e1') (y',e2'))
        | x == x' && y == y'
        -- Omit 'braces' because we use these as an escape character inside fancyvrb.
        = ((text "inl" <> parens (pp x) <> text "." <> pp_partial e1 e1') <>
           semi $$
           (text "inr" <> parens (pp y) <> text "." <> pp_partial e2 e2'))

instance PP Code where
    pp k = pp_partial k k
    pp_partial (Rec f x e Nothing) (Rec f' x' e' Nothing)
        | f == f' && x == x'
        = text "fun" <+> pp f <> parens (pp x) <> text "." $$ nest 2 ( pp_partial e e')
    pp_partial (Rec f x e (Just l)) (Rec f' x' e' (Just l'))
        | f == f' && x == x' && l == l'
        = text (unL l)

class Valuable a where
    to_val :: a -> Value
    from_val :: Value -> a

instance Valuable Int where
    to_val i = VInt i
    from_val (VInt i) = i

instance Valuable Bool where
    to_val b = VBool b
    from_val (VBool b) = b

instance Valuable () where
    to_val () = VUnit
    from_val VUnit = ()

instance (Valuable a, Valuable b) => Valuable (a,b) where
    to_val (a,b) = VPair (to_val a) (to_val b)
    from_val (VPair a b) = (from_val a, from_val b)

instance (Valuable a, Valuable b) => Valuable (Either a b) where
    to_val (Left a) = VInL (to_val a)
    to_val (Right b) = VInR (to_val b)
    from_val (VInL a) = from_val a
    from_val (VInR b) = from_val b

instance Valuable a => Valuable (Maybe a) where
    to_val Nothing = VInL VUnit
    to_val (Just a) = VInR (to_val a)
    from_val (VInL VUnit) = Nothing
    from_val (VInR a) = from_val a






-- fvsK.  Calculates free vars of closure.
-- TODO: use ordered sets
class FVs a where
    fvs :: a -> [Var]


instance FVs Exp where
    fvs (Var x) = [x]
    fvs (Let x e1 e2) = delete x (fvs e1 `union` fvs e2)
    fvs (Unit) = []
    fvs (CBool b) = []
    fvs (If e1 e2 e3) = fvs e1 `union` fvs e2 `union` fvs e3
    fvs (CInt i) = []
    fvs (CString s) = []
    fvs (Pair e1 e2) = fvs e1 `union` fvs e2
    fvs (Fst e) = fvs e
    fvs (Snd e) = fvs e
    fvs (InL e) = fvs e
    fvs (InR e) = fvs e
    fvs (Case e m) = fvs e `union` fvs m
    fvs (Fun k) = fvs k
    fvs (App e1 e2) = fvs e1 `union` fvs e2
    fvs (Roll _ e) = fvs e
    fvs (Unroll _ e) = fvs e
    fvs (IfThen t e1 e2 t1) = fvs t `union` fvs e1 `union` fvs e2 `union` fvs t1
    fvs (IfElse t e1 e2 t2) = fvs t `union` fvs e1 `union` fvs e2 `union` fvs t2
    fvs (CaseL t m v t1) = fvs t `union` fvs m `union` (delete v (fvs t1))
    fvs (CaseR t m v t2) = fvs t `union` fvs m `union` (delete v (fvs t2))
    fvs (Call t1 t2 k t) = fvs t `union` fvs t2 `union` fvs k `union` fvs t
    fvs (Trace e) = fvs e
--    fvs (TraceVal e) = fvs e
--    fvs (TraceReplay e) = fvs e
    fvs (TraceVar e x) = fvs e `union` [x]
    fvs (TraceUpd e x e') = fvs e `union` [x] `union` fvs e'
    fvs (Lab e l) = fvs e
    fvs (EraseLab e l) = fvs e
    fvs Hole = []

instance FVs Match where
    fvs (Match (x,e1) (y,e2)) = (delete x (fvs e1)) `union` (delete y (fvs e2))

instance FVs Code where
    fvs k = let vs = fvs (body k)
            in delete (fn k) (delete (arg k) vs)


promote VStar = VStar
promote VHole = VStar
promote VUnit = VUnit
promote (VBool b) = VBool b
promote (VInt i) = VInt i
promote (VString s) = VString s
promote (VPair v1 v2) = VPair (promote v1) (promote v2)
promote (VInL v) = VInL (promote v)
promote (VInR v) = VInR (promote v)
promote (VRoll tv v) = VRoll tv (promote v)
promote (VClosure k env) = VClosure k (fmap promote env)

instance LowerSemiLattice Value where
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
    leq (VRoll tv v) (VRoll tv' v')   | tv == tv'
                                      = v `leq` v'
    leq (VClosure k env) (VClosure k' env')
        = k `leq` k' && env `leq` env'
    lub VHole v                       = v
    lub v VHole                       = v
    lub VStar v                       = promote v
    lub v VStar                       = promote v
    lub VUnit VUnit                   = VUnit
    lub (VBool b) (VBool b')          | b == b'
                                      = VBool b
    lub (VInt i) (VInt i')            | i == i'
                                      = VInt i
    lub (VString i) (VString i')      | i == i'
                                      = VString i
    lub (VPair v1 v2) (VPair v1' v2') = VPair (v1 `lub` v1') (v2 `lub` v2')
    lub (VInL v) (VInL v')            = VInL (v `lub` v')
    lub (VInR v) (VInR v')            = VInR (v `lub` v')
    lub (VRoll tv v) (VRoll tv' v')   | tv == tv'
                                      = VRoll tv (v `lub` v')
    lub (VClosure k env) (VClosure k' env')
        = VClosure (k `lub` k') (env `lub` env')

instance LowerSemiLattice Exp where
    bot                                = Hole
    leq Hole e                         = True
    leq (Var x) (Var x')               = x `leq` x'
    leq (Let x e1 e2) (Let x' e1' e2') = x `leq` x' && e1 `leq` e1' && e2 `leq` e2'
    leq (CInt i) (CInt j)              = i == j
    leq (CString i) (CString j)        = i == j
    leq (Op f es) (Op f' es')          | f == f' && length es == length es'
                                       = all (\(x,y) -> x `leq` y) (zip es es')
    leq Unit Unit                      = True
    leq (CBool b) (CBool b')           = True
    leq (If e e1 e2) (If e' e1' e2')   = e `leq` e' && e1 `leq` e1' && e2 `leq` e2'
    leq (Pair e1 e2) (Pair e1' e2')    = e1 `leq` e1' && e2 `leq` e2'
    leq (Fst e) (Fst e')               = e `leq` e'
    leq (Snd e) (Snd e')               = e `leq` e'
    leq (InL e) (InL e')               = e `leq` e'
    leq (InR e) (InR e')               = e `leq` e'
    leq (Case e m) (Case e' m')        = e `leq` e' && m `leq` m'
    leq (Fun k) (Fun k')               = k `leq` k'
    leq (App e1 e2) (App e1' e2')      = e1 `leq`  e1' && e2 `leq` e2'
    leq (Roll tv e) (Roll tv' e')      | tv == tv' = e `leq` e'
    leq (Unroll tv e) (Unroll tv' e')  | tv == tv' = e `leq` e'
    leq (IfThen t e1 e2 t1) (IfThen t' e1' e2' t1')
        = t `leq` t' && e1 `leq` e1' && e2 `leq` e2' && t1 `leq` t1'
    leq (IfElse t e1 e2 t2) (IfElse t' e1' e2' t2')
        = t `leq` t' && e1 `leq` e1' && e2 `leq` e2' && t2 `leq` t2'
    leq (CaseL t m x t1) (CaseL t' m' x' t1')
        = t `leq` t' && m `leq` m' && x == x' && t1 `leq` t1'
    leq (CaseR t m x t2) (CaseR t' m' x' t2')
        = t `leq` t' && m `leq` m' && x == x' && t2 `leq` t2'
    leq (Call t1 t2 k t) (Call t1' t2' k' t')
        = t1 `leq` t1' && t2 `leq` t2' && k `leq` k' && t `leq` t'
    leq (Trace e) (Trace e')
        = e `leq` e'
    leq (TraceVar e x) (TraceVar e' x')
        = e `leq` e' && x `leq` x'
    leq (TraceUpd e1 x e2) (TraceUpd e1' x' e2')
        = e1 `leq` e1' && x `leq` x' && e2 `leq` e2'
    leq (Lab e l) (Lab e' l')
        | l == l' = e `leq` e'
    leq (EraseLab e l) (EraseLab e' l')
        | l == l' = e `leq` e'

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
    lub (If e e1 e2) (If e' e1' e2')   = If (e `lub` e') (e1 `lub` e1') (e2 `lub` e2')
    lub (Pair e1 e2) (Pair e1' e2')    = Pair (e1 `lub` e1') (e2 `lub` e2')
    lub (Fst e) (Fst e')               = Fst (e `lub` e')
    lub (Snd e) (Snd e')               = Snd (e `lub` e')
    lub (InL e) (InL e')               = InL (e `lub` e')
    lub (InR e) (InR e')               = InR (e `lub` e')
    lub (Case e m) (Case e' m')        = Case (e `lub` e') (m `lub` m')
    lub (Fun k) (Fun k')               = Fun (k `lub` k')
    lub (App e1 e2) (App e1' e2')      = App (e1 `lub` e1') (e2 `lub` e2')
    lub (Roll tv e) (Roll tv' e')      | tv == tv' = Roll tv (e `lub` e')
    lub (Unroll tv e) (Unroll tv' e')  | tv == tv' = Unroll tv (e `lub` e')
    lub (IfThen t e1 e2 t1) (IfThen t' e1' e2' t1')
        = IfThen (t `lub` t') (e1 `lub` e1') (e2 `lub` e2') (t1 `lub` t1')
    lub (IfElse t e1 e2 t2) (IfElse t' e1' e2' t2')
        = IfElse (t `lub` t') (e1 `lub` e1') (e2 `lub` e2') (t2 `lub` t2')
    lub (CaseL t m x t1) (CaseL t' m' x' t1')
        = CaseL (t `lub` t') (m `lub` m') (x `lub` x') (t1 `lub` t1')
    lub (CaseR t m x t2) (CaseR t' m' x' t2')
        = CaseR (t `lub` t') (m `lub` m') (x `lub` x') (t2 `lub` t2')
    lub (Call t1 t2 k t) (Call t1' t2' k' t')
        = Call (t1 `lub` t1') (t2 `lub` t2') (k `lub` k') (t `lub` t')
    lub (Trace e) (Trace e')
        = Trace(e `lub` e')
    lub (TraceVar e x) (TraceVar e' x')
        = TraceVar(e `lub` e') (x `lub` x')
    lub (TraceUpd e1 x e2) (TraceUpd e1' x' e2')
        = TraceUpd(e1 `lub` e1') (x `lub` x') (e2 `lub` e2')
    lub (Lab e l) (Lab e' l')
        | l == l' = Lab (e `lub` e') l
    lub (EraseLab e l) (EraseLab e' l')
        | l == l' = EraseLab (e `lub` e') l
    lub x y = error (show x ++ "\n\n" ++ show y)




instance LowerSemiLattice Code where
    bot = Rec bot bot bot Nothing
    leq (Rec f x e l) (Rec f' x' e' l') =
        f `leq` f' && x `leq` x' && e `leq` e' && l `leq` l'
    lub (Rec f x e l) (Rec f' x' e' l')
        = Rec (f `lub` f') (x `lub` x') (e `lub` e') (l `lub` l')


instance LowerSemiLattice Match where
    bot = Match (bot, bot) (bot, bot)
    leq (Match (x,m1) (y,m2)) (Match (x',m1') (y', m2'))
        = x `leq` x' && y `leq` y' && m1 `leq` m1' && m2 `leq` m2'
    lub (Match (x,m1) (y,m2)) (Match (x',m1') (y', m2'))
        = Match (x `lub` x',m1 `lub` m1') (y `lub` y', m2 `lub` m2')


class Pattern a where
    match :: a -> a -> a -> Bool
    extract :: a -> a -> a

instance Pattern Value where
    match VStar v v' = v == v'
    match VHole v v' = True
    match VUnit VUnit VUnit = True
    match (VBool pb) (VBool b) (VBool b') = pb == b && pb == b'
    match (VInt pi) (VInt i) (VInt i') = pi == i && pi == i'
    match (VString pi) (VString i) (VString i') = pi == i && pi == i'
    match (VPair p1 p2) (VPair v1 v2) (VPair v1' v2') = match p1 v1 v1' && match p2 v2 v2'
    match (VInL p) (VInL v) (VInL v') = match p v v'
    match (VInR p) (VInR v) (VInR v') = match p v v'
    match (VRoll tv p) (VRoll tv' v) (VRoll tv'' v')
        | tv == tv' && tv' == tv''
        = match p v v'
    match (VLabel p l) (VLabel v' l') (VLabel v'' l'')
        | l == l' && l == l''
        = match p v' v''
    match p v v' = False

    extract VStar v = v
    extract VHole v = VHole
    extract VUnit VUnit = VUnit
    extract (VBool pb) (VBool b) | pb == b = VBool b
    extract (VInt pi) (VInt i) | pi == i = VInt i
    extract (VString pi) (VString i) | pi == i = VString i
    extract (VPair p1 p2) (VPair v1 v2) = VPair (extract p1 v1) (extract p2 v2)
    extract (VInL p) (VInL v) = VInL (extract p v)
    extract (VInR p) (VInR v) = VInR (extract p v)
    extract (VRoll tv p) (VRoll tv' v) | tv == tv' = VRoll tv (extract p v)
    extract (VClosure k p) (VClosure k' v)  = VClosure k' (extract p v)
    extract (VLabel p l) (VLabel v l')
        | l == l'
        = VLabel (extract p v) l
    extract p v = error "extract only defined if p <= v"

instance (Pattern a, LowerSemiLattice a) => Pattern (Env a) where
    match (penv@(Env penv')) env1 env2
        = all (\x -> match (lookupEnv' penv x) (lookupEnv' env1 x) (lookupEnv' env2 x)) (Map.keys penv')
    extract (Env penv') env
        = Env (Map.mapWithKey (\x p -> extract p (lookupEnv' env x)) penv')




intOps :: Map Op ((Int, Int) -> Value)
intOps = fromList [
      (opPlus, to_val . uncurry (+)),
      (opMinus, to_val . uncurry (-)),
      (opTimes, to_val . uncurry (*)),
      (opDiv, to_val . uncurry div),
      (opMod, to_val . uncurry mod),
      (opIntEq, to_val . uncurry (==)),
      (opLt, to_val . uncurry (<)),
      (opGt, to_val . uncurry (>)),
      (opIntNeq, to_val . uncurry (/=)),
      (opLeq, to_val . uncurry (<=)),
      (opGeq, to_val . uncurry (>=))
   ]

boolOps :: Map Op ((Bool, Bool) -> Value)
boolOps = fromList [
      (opAnd, to_val . uncurry (&&)),
      (opOr, to_val . uncurry (||)),
      (opBoolEq, to_val . uncurry (==))
   ]

evalIntBinop :: Op -> Int -> Int -> Value
evalIntBinop op i j = intOps!op $ (i, j)

evalBoolBinop :: Op -> Bool -> Bool -> Value
evalBoolBinop op i j = boolOps!op $ (i, j)

evalOp :: Op -> [Value] -> Value
evalOp f [VInt i, VInt j] = evalIntBinop f i j
evalOp f [VBool i, VBool j] = evalBoolBinop f i j
evalOp (O "not" _ _) [VBool b] = VBool (not b)
evalOp f vs | List.elem VHole vs = VHole
evalOp f vs | List.elem VStar vs = VStar
evalOp f vs = error ("Op "++show f++ " not defined for "++ show vs)
