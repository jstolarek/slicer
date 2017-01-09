module Env
    ( -- * Variables and type variables
      Var(..), TyVar(..)

      -- * Environment operations
    , Env(..), emptyEnv, singletonEnv, constEnv, lookupEnv, lookupEnv', bindEnv
    , unbindEnv, updateEnv
    ) where
import UpperSemiLattice
import Text.PrettyPrint
import PrettyPrinting
import qualified Data.Map as Map
newtype Var = V {unV::String} deriving (Eq,Ord)

instance UpperSemiLattice Var where
    bot = V "_"
    leq (V "_") v = True
    leq v v' = v == v'
    lub (V "_") v = v
    lub v (V "_") = v
    lub v v' | v == v' = v

instance Show Var where
    showsPrec i (V x) = showString x

instance PP Var where
    pp (V x) = text x
    pp_partial (V "_") v = sb (pp v)
    pp_partial v v' | v == v' = pp v

newtype TyVar = TV {unTV::String} deriving (Eq,Ord)

instance Show TyVar where
    showsPrec i (TV x) = showString x


instance PP TyVar where
    pp (TV x) = text x
    pp_partial (TV "_") v = sb (pp v)
    pp_partial v v' | v == v' = pp v

newtype Env a = Env (Map.Map Var a)
    deriving (Eq,Show,Ord)

instance (UpperSemiLattice a,PP a) => PP (Env a) where
    pp_partial (Env env) (Env env') =
         brackets (hcat (punctuate comma (map ppp (Map.keys env'))))
            where ppp x =
                      case (Map.lookup x env,Map.lookup x env')
                      of (Nothing,Just a) -> pp x <+> text "->" <+> sb (pp a);
                         (Just a, Just a') ->
                             pp x <+> text "->"<+> pp_partial a a'


instance Functor Env where
    fmap f (Env env) = Env (fmap f env)

emptyEnv :: Env a
emptyEnv = Env Map.empty

singletonEnv :: Var -> a -> Env a
singletonEnv v a = Env (Map.singleton v a)

constEnv :: [Var] -> a -> Env a
constEnv vs a = Env (foldl (\m x -> Map.insert x a m) Map.empty vs)


lookupEnv :: Env a -> Var -> a -> a
lookupEnv (Env env) x a = case Map.lookup x env
                          of Just v -> v
                             Nothing -> a

lookupEnv' :: UpperSemiLattice a => Env a -> Var  -> a
lookupEnv' env x = lookupEnv env x bot

bindEnv :: Env a -> Var -> a -> Env a
bindEnv (Env env) var val = val `seq` Env (Map.insert var val env)

updateEnv :: Env a -> Var -> a -> Env a
updateEnv env x val = bindEnv (unbindEnv env x) x val

unbindEnv :: Env a -> Var -> Env a
unbindEnv (Env env) x = Env (Map.delete x env)


unbind [] x = []
unbind ((x,v):env) y = if x == y
                       then env
                       else (x,v):unbind env y


instance (UpperSemiLattice a) => UpperSemiLattice (Env a) where
    bot                                = Env Map.empty
    leq (Env env1) (Env env2)          = Map.isSubmapOfBy leq env1 env2
    lub (Env env1) (Env env2)          = Env (Map.unionWith lub env1 env2)



