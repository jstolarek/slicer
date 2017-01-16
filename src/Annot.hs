module Annot
    ( expr, make_expr, dep, make_dep, whr, make_where

    , ErasableToValue(erase_to_v)
    ) where

import           Env
import           PrettyPrinting
import           Trace
import           UpperSemiLattice

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Traversable as T
import           Text.PrettyPrint ( (<>), parens, hcat, punctuate, braces, comma
                                  , text, (<+>), int, Doc )

-- TODO: Symbolically evaluate values over patterns

data RValue a = RBool Bool | RInt Int | RUnit | RString String
              | RPair (AValue a) (AValue a)
              | RInL (AValue a) | RInR (AValue a)
              | RRoll (AValue a)
              | RClosure Code (Env (AValue a))
              | RHole | RStar
           deriving (Eq,Show)

data AValue a = AValue (RValue a) a
              | AVHole
              | AVStar
           deriving (Eq,Show)

instance (UpperSemiLattice a, PP a) => PP (RValue a) where
    pp_partial RHole RHole = sb (text "_")
    pp_partial RHole v = sb (pp v)
    pp_partial RStar RStar = sb (text "<star>")
    pp_partial RStar v = pp v
    pp_partial (RBool b) (RBool b')
        | b == b'
        = text (if b then "true" else "false")
    pp_partial (RInt i) (RInt i')
        | i == i'
        = int i
    pp_partial (RString s) (RString s')
        | s == s'
        = text (show s)
    pp_partial (RUnit) (RUnit) = text "()"
    pp_partial (RPair v1 v2) (RPair v1' v2') =
        parens (pp_partial v1 v1' <> comma <> pp_partial v2 v2')
    pp_partial (RInL v) (RInL v') = text "inl" <> parens (pp_partial v v')
    pp_partial (RInR v) (RInR v') = text "inr"  <> parens (pp_partial v v')
    pp_partial (RRoll v) (RRoll v') = text "roll"<> parens (pp_partial v v')
    pp_partial (RClosure _ _) (RClosure _ _) = text "<fun>"
    pp_partial _ _ = error "Pretty-printing error: RValue a"
    pp v = pp_partial v v

instance (UpperSemiLattice a,PP a) => PP (AValue a) where
    pp_partial AVStar AVStar = sb (text "<star>")
    pp_partial AVStar v = sb (pp v)
    pp_partial AVHole AVHole = sb (text "_")
    pp_partial AVHole v = sb (pp v)
    pp_partial (AValue v a) (AValue v' a') =
        if a' == bot then pp_partial v v'
        else pp_partial v v' <+> text "@" <+> pp_partial a a'
    pp_partial _ _ = error "Pretty-printing error: AValue a"
    pp v = pp_partial v v

class ErasableToValue a where
    erase_to_v :: a -> Value

instance UpperSemiLattice a => ErasableToValue (AValue a) where
    erase_to_v AVHole       = VHole
    erase_to_v (AVStar)     = VStar
    erase_to_v (AValue v _) = erase_to_v v

instance UpperSemiLattice a => ErasableToValue (RValue a) where
    erase_to_v (RBool b)        = VBool b
    erase_to_v RUnit            = VUnit
    erase_to_v RStar            = VStar
    erase_to_v RHole            = VHole
    erase_to_v (RInt i)         = VInt i
    erase_to_v (RString i)      = VString i
    erase_to_v (RPair v1 v2)    = VPair (erase_to_v v1) (erase_to_v v2)
    erase_to_v (RInL v)         = VInL (erase_to_v v)
    erase_to_v (RInR v)         = VInR (erase_to_v v)
    erase_to_v (RRoll v)        = VRoll Nothing (erase_to_v v)
    erase_to_v (RClosure k env) = VClosure k (fmap erase_to_v env)

instance Functor RValue where
    fmap _ (RBool b)        = RBool b
    fmap _ RUnit            = RUnit
    fmap _ RHole            = RHole
    fmap _ RStar            = RStar
    fmap _ (RInt i)         = RInt i
    fmap _ (RString s)      = RString s
    fmap f (RPair v1 v2)    = RPair (fmap f v1) (fmap f v2)
    fmap f (RInL v)         = RInL (fmap f v)
    fmap f (RInR v)         = RInR (fmap f v)
    fmap f (RRoll v)        = RRoll (fmap f v)
    fmap f (RClosure k env) = RClosure k (fmap (fmap f) env)

instance Functor AValue where
    fmap _ AVHole       = AVHole
    fmap _ AVStar       = AVStar
    fmap f (AValue r a) = AValue (fmap f r) (f a)

instance UpperSemiLattice a => UpperSemiLattice (AValue a) where
    bot                             = AVHole

    leq AVHole _                    = True
    leq (AValue v _) (AValue v' _) = v `leq` v'
    leq _ _ = error $ "UpperSemiLattice (AValue a): error taking leq"

    lub AVHole v                    = v
    lub v AVHole                    = v
    lub (AValue v a) (AValue v' a') = AValue (v `lub` v') (a `lub` a')
    lub _ _ = error $ "UpperSemiLattice (AValue a): error taking lub"

apromote :: AValue a -> AValue a
apromote AVHole       = AVStar
apromote AVStar       = AVStar
apromote (AValue v a) = AValue (rpromote v) a

rpromote :: RValue a -> RValue a
rpromote RHole            = RStar
rpromote RStar            = RStar
rpromote RUnit            = RUnit
rpromote (RBool b)        = RBool b
rpromote (RInt i)         = RInt i
rpromote (RString s)      = RString s
rpromote (RPair v1 v2)    = RPair (apromote v1) (apromote v2)
rpromote (RInL v)         = RInL (apromote v)
rpromote (RInR v)         = RInR (apromote v)
rpromote (RRoll v)        = RRoll (apromote v)
rpromote (RClosure k env) = RClosure k (fmap apromote env)

instance UpperSemiLattice a => UpperSemiLattice (RValue a) where
    bot                               = RHole

    leq RHole _                       = True
    leq RStar v                       = v == rpromote v
    leq RUnit RUnit                   = True
    leq (RBool b) (RBool b')          = b == b'
    leq (RInt i) (RInt i')            = i == i'
    leq (RString i) (RString i')            = i == i'
    leq (RPair v1 v2) (RPair v1' v2') = v1 `leq` v1' && v2 `leq` v2'
    leq (RInL v) (RInL v')            = v `leq` v'
    leq (RInR v) (RInR v')            = v `leq` v'
    leq (RRoll v) (RRoll v')          = v `leq` v'
    leq (RClosure k env) (RClosure k' env')
        = k `leq` k' && env `leq` env'
    leq _ _ = error $ "UpperSemiLattice (Rvalue a): error taking leq"

    lub RHole v                       = v
    lub v RHole                       = v
    lub RStar v                       = rpromote v
    lub v RStar                       = rpromote v
    lub RUnit RUnit                   = RUnit
    lub (RBool b) (RBool b')          | b == b'
                                      = RBool b
    lub (RInt i) (RInt i')            | i == i'
                                      = RInt i
    lub (RString i) (RString i')      | i == i'
                                      = RString i
    lub (RPair v1 v2) (RPair v1' v2') = RPair (v1 `lub` v1') (v2 `lub` v2')
    lub (RInL v) (RInL v')            = RInL (v `lub` v')
    lub (RInR v) (RInR v')            = RInR (v `lub` v')
    lub (RRoll v) (RRoll v')          = RRoll (v `lub` v')
    lub (RClosure k env) (RClosure k' env')
        = RClosure (k `lub` k') (env `lub` env')
    lub _ _ = error $ "UpperSemiLattice (RValue a): error taking lub"

newtype Gensym a = G {unG :: Int -> (a,Int)}

instance Functor Gensym where
    fmap f (G x) = G (\s -> let (x', s') = x s
                            in (f x', s'))


instance Applicative Gensym where
    pure a = G (\i -> (a,i))
    (G f) <*> (G x) = G (\s -> let (f', s' ) = f s
                                   (x', s'') = x s'
                               in (f' x', s''))

instance Monad Gensym where
    return a = G (\i -> (a,i))
    (G f) >>= g = G (\i -> let (a,j) = f i in unG (g a) j)

gensym :: Gensym Int
gensym = G (\i -> (i,i+1))


uniq :: Value -> Gensym (AValue Int)
uniq VHole = return AVHole
uniq VStar = return AVStar
uniq val = do i <- gensym
              v' <- uniq' val
              return (AValue v' i)
    where uniq' VUnit = return RUnit
          uniq' (VInt i) = return (RInt i)
          uniq' (VString s) = return (RString s)
          uniq' (VBool b) = return (RBool b)
          uniq' (VPair v1 v2) = do v1' <- uniq v1
                                   v2' <- uniq v2
                                   return (RPair v1' v2')
          uniq' (VInL v) = do v' <- uniq v
                              return (RInL v')
          uniq' (VInR v) = do v' <- uniq v
                              return (RInR v')
          uniq' (VRoll _ v) = do v' <- uniq v
                                 return (RRoll v')
          uniq' (VClosure k (Env env)) = do env' <- T.mapM uniq env
                                            return (RClosure k (Env env'))

          uniq' (VLabel v _) = uniq' v
          uniq' v  = error ("uniq': "++ show v)

runGensym :: Gensym a -> a
runGensym (G f) = fst (f 0)

inject :: UpperSemiLattice a => Value -> AValue a
inject VHole = AVHole
inject VStar = AVStar
inject v     = AValue (rinject v) bot

rinject :: UpperSemiLattice a => Value -> RValue a
rinject VUnit            = RUnit
rinject VHole            = RHole
rinject VStar            = RStar
rinject (VInt i)         = RInt i
rinject (VString s)      = RString s
rinject (VBool b)        = RBool b
rinject (VPair v1 v2)    = RPair (inject v1) (inject v2)
rinject (VInL v)         = RInL (inject v)
rinject (VInR v)         = RInR (inject v)
rinject (VRoll _ v)      = RRoll (inject v)
rinject (VClosure k env) = RClosure k (fmap inject env)
rinject v = error $ "Cannot rinject value " ++ show v

annots :: Ord a => AValue a -> Set.Set a
annots AVHole       = Set.empty
annots AVStar       = Set.empty
annots (AValue r a) = Set.insert a (rannots r)

rannots :: Ord a => RValue a -> Set.Set a
rannots (RUnit)                = Set.empty
rannots (RStar)                = Set.empty
rannots (RHole)                = Set.empty
rannots (RBool _)              = Set.empty
rannots (RInt _)               = Set.empty
rannots (RString _)            = Set.empty
rannots (RPair v1 v2)          = Set.union (annots v1) (annots v2)
rannots (RInL v)               = annots v
rannots (RInR v)               = annots v
rannots (RRoll v)              = annots v
rannots (RClosure _ (Env env)) = Set.unions (map annots (Map.elems env))

-- type class of provenance semantics
-- specifies one transfer function for each syntax case

class Prov a where
    unit :: AValue a
    cbool :: Bool -> AValue a
    ifthen :: a -> AValue a -> AValue a
    ifelse :: a -> AValue a -> AValue a
    cint :: Int -> AValue a
    cstring :: String -> AValue a
    op :: Op -> [AValue a] -> AValue a
    pair :: AValue a -> AValue a -> AValue a
    first ::  a -> AValue a -> AValue a
    second ::  a -> AValue a -> AValue a
    inl :: AValue a -> AValue a
    inr :: AValue a -> AValue a
    casel :: a -> AValue a -> AValue a
    caser :: a -> AValue a -> AValue a
    fun :: Code -> Env (AValue a) -> AValue a
    app :: a -> AValue a -> AValue a
    roll :: AValue a -> AValue a
    unroll :: a -> AValue a -> AValue a

prov :: Prov a => Env (AValue a) -> Exp -> AValue a
prov _   Hole = AVHole
prov env (Var x) = lookupEnv env x (error ("prov: unbound " ++ show x))
prov env (Let x t1 t2) = prov (bindEnv env x (prov env t1)) t2
prov _   Unit = unit
prov _   (CBool b) = cbool b
prov env (IfThen t _ _ t1)
    = let (AValue (RBool True) a) = prov env t
      in ifthen a (prov env t1)
prov env (IfElse t _ _ t2)
    = let (AValue (RBool False) a) = prov env t
      in ifelse a (prov env t2)
prov _   (CInt i)
    = cint i
prov _   (CString s)
    = cstring s
prov env (Op f ts)
    = op f (map (prov env) ts)
prov env (Pair e1 e2) = pair (prov env e1) (prov env e2)
prov env (Fst e)
    = let (AValue (RPair v1 _) a) = prov env e
      in first a v1
prov env (Snd e)
    = let (AValue (RPair _ v2) a) = prov env e
      in second a v2
prov env (InL e) = inl (prov env e)
prov env (InR e) = inr (prov env e)
prov env (Fun k) =  fun k env
prov env (CaseL t _ x t1)
    = let (AValue (RInL v) a) = prov env t
          v' = prov (bindEnv env x v) t1
      in casel a v'
prov env (CaseR t _ x t2)
    = let (AValue (RInR v) a) = prov env t
          v' = prov (bindEnv env x v) t2
      in caser a v'
prov env (Call t1 t2 _ t)
    = let v1@(AValue (RClosure _ env0) a) = prov env t1
          v2                              = prov env t2
          v = prov (bindEnv (bindEnv env0 (funArg t) v2 ) (funName t) v1)
                   (funBody t)
      in app a v
prov env (Roll _ t) = roll (prov env t)
prov env (Unroll _ t) =
    let AValue (RRoll v) a = prov env t
    in unroll a v
prov _ e = error $ "Provenance not supported for " ++ show e

-- where provenance semantics
make_where :: Value -> AValue (Where Int)
make_where v = fmap (\x -> W(Just x)) (runGensym $ uniq v)

data Where a = W (Maybe a)
               deriving (Show, Eq)

instance (Eq a, Show a) => PP (Where a) where
    pp_partial (W Nothing) (W Nothing) = sb (text "_")
    pp_partial (W Nothing) w = sb(pp w)
    pp_partial (W (Just x)) (W (Just y)) | x == y = text (show x)
    pp_partial _ _ = error "Pretty-printing error: Where a"
    pp w = pp_partial w w

instance Eq a => UpperSemiLattice (Where a) where
    bot = W bot
    leq (W x) (W y) = x == y
    lub (W x) (W y) = W (x `lub` y)

instance (Eq a) => Prov (Where a) where
    unit       = AValue RUnit bot
    cbool b    = AValue (RBool b) bot
    ifthen _ v = v
    ifelse _ v = v
    cint i     = AValue (RInt i) bot
    cstring s  = AValue (RString s) bot
    op f avs   =
        let (vs, _) = unzip (map (\(AValue v a) -> (erase_to_v v,a)) avs)
        in inject (evalOp f vs)
    pair v1 v2 = AValue (RPair v1 v2) bot
    first _ v  = v
    second _ v = v
    inl v      = AValue (RInL v) bot
    inr v      = AValue (RInR v) bot
    casel _ v  = v
    caser _ v  = v
    fun k env  = AValue (RClosure k env) bot
    app _ v    = v
    roll v     = AValue( RRoll v) bot
    unroll _ v = v

whr :: (Eq a) => Env (AValue (Where a)) -> Exp -> AValue (Where a)
whr env t = prov env t

-- expression provenance semantics
instance Prov Exp where
    unit       = AValue RUnit bot
    cbool b    = AValue (RBool b) (CBool b)
    ifthen _ v = v
    ifelse _ v = v
    cint i     = AValue (RInt i) (CInt i)
    cstring i  = AValue (RString i) (CString i)

    op f avs   =
        let (vs,as) = unzip (map (\(AValue v a) -> (erase_to_v v,a)) avs)
        in AValue (rinject (evalOp f vs)) (Op f as)
    pair v1 v2 = AValue (RPair v1 v2) bot
    first _ v  = v
    second _ v = v
    inl v      = AValue (RInL v) bot
    inr v      = AValue (RInR v) bot
    casel _ v  = v
    caser _ v  = v
    fun k env  = AValue (RClosure k env) bot
    app _ v    = v
    roll v     = AValue( RRoll v) bot
    unroll _ v = v

expr :: Env (AValue Exp) -> Exp -> AValue Exp
expr env t = prov env t

make_expr :: Value -> AValue ( Exp)
make_expr v = fmap (\x -> (Var (V ("x_" ++ show x)))) (runGensym $ uniq v)


-- dependency provenance semantics

newtype Dep a = D (Set.Set a)
    deriving (Eq,Show,Ord)

instance (Ord a,Eq a) => UpperSemiLattice (Dep a) where
    bot = D (Set.empty)
    leq (D x) (D y) = Set.isSubsetOf x y
    lub (D x) (D y) = D (Set.union x y)

ppset :: Show a => Set.Set a -> Doc
ppset s = braces (hcat (punctuate comma (map (text.show) (Set.toList s))))

instance (Eq a, Show a) => PP (Dep a) where
    pp_partial (D s) (D s') =
        if s == s' then ppset s
        else ppset s' <+> sb( ppset s)
    pp (D s) = ppset s

addAnnot :: UpperSemiLattice a => AValue a -> a -> AValue a
addAnnot (AValue rv a) a' = AValue rv (a `lub` a')
addAnnot (AVHole) _ = AVHole
addAnnot (AVStar) _ = AVStar

instance (Ord a) => Prov (Dep a) where
    unit       = AValue RUnit bot
    cbool b    = AValue (RBool b) bot
    ifthen a v = addAnnot v a
    ifelse a v = addAnnot v a
    cint i     = AValue (RInt i) bot
    cstring i  = AValue (RString i) bot
    op f avs   =
        let (vs,as) = unzip (map (\v -> (erase_to_v v,annots v)) avs)
        in AValue (rinject (evalOp f vs))  (Set.fold lub bot (Set.unions as))
    pair v1 v2 = AValue (RPair v1 v2) bot
    first a v  = addAnnot v a
    second a v = addAnnot v a
    inl v      = AValue (RInL v) bot
    inr v      = AValue (RInR v) bot
    casel a v  = addAnnot v a
    caser a v  = addAnnot v a
    fun k env  = AValue (RClosure k env) bot
    app a v    = addAnnot v a
    roll v     = AValue( RRoll v) bot
    unroll a v = addAnnot v a

make_dep :: Value -> AValue (Dep Int)
make_dep v = fmap (\x -> D (Set.singleton x)) (runGensym $ uniq v)

dep :: Ord a => Env (AValue (Dep a)) -> Exp -> AValue (Dep a)
dep env t = prov env t
