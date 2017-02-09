{-# LANGUAGE DeriveAnyClass   #-}
{-# LANGUAGE DeriveGeneric    #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}

module Language.Slicer.Env
    ( -- * Variables and type variables
      Var(..), TyVar(..)

      -- * Environment operations
    , Env(..), emptyEnv, singletonEnv, constEnv
    , lookupEnv, lookupEnv', maybeLookupEnv', lookupEnvMaybe
    , bindEnv, unbindEnv, maybeUnbindEnv, updateEnv
    ) where

import           Language.Slicer.UpperSemiLattice

import           Control.DeepSeq ( NFData  )
import qualified Data.Map as Map
import           GHC.Generics    ( Generic )
import           Text.PrettyPrint.HughesPJClass

newtype Var = V (Maybe String)
    deriving (Eq, Ord, Generic, NFData)

instance Show Var where
    showsPrec _ (V (Just x)) = showString x
    showsPrec _ (V Nothing ) = showString "_"

instance UpperSemiLattice Var where
    bot = V Nothing

    lub (V Nothing) v       = v
    lub v       (V Nothing) = v
    lub v v' | v == v'  = v
    lub v v' = error $ "UpperSemiLattice Var: error taking lub of " ++
                        show v ++ " and " ++ show v'

    leq (V Nothing) _  = True
    leq v           v' = v == v'

instance Pretty Var where
    pPrint (V (Just x)) = text x
    pPrint (V Nothing ) = text "_"

-- This instance is overlapping the default Pretty (Maybe a) instance provided
-- by the pretty library.  Pragma required to resolve instances correctly.
instance {-# OVERLAPPING #-} Pretty (Maybe Var) where
    pPrint (Just v) = pPrint v
    pPrint Nothing  = empty

newtype TyVar = TV String
    deriving (Eq, Ord, Generic, NFData)

instance Show TyVar where
    showsPrec _ (TV x) = showString x

instance Pretty TyVar where
    pPrint (TV x) = text x

newtype Env a = Env (Map.Map Var a)
    deriving (Show, Eq, Ord, Foldable, Traversable, Generic, NFData)

instance (Pretty a) => Pretty (Env a) where
    pPrint (Env env) =
        brackets (hcat (punctuate comma (map pp (Map.toList env))))
            where pp (key, value) = pPrint key <+> text "->" <+> pPrint value

instance Functor Env where
    fmap f (Env env) = Env (fmap f env)

emptyEnv :: Env a
emptyEnv = Env Map.empty

singletonEnv :: Var -> a -> Env a
singletonEnv v a = Env (Map.singleton v a)

constEnv :: [Var] -> a -> Env a
constEnv vs a = Env (foldl (\m x -> Map.insert x a m) Map.empty vs)

lookupEnv :: Env a -> Var -> a -> a
lookupEnv (Env env) x a = Map.findWithDefault a x env

lookupEnvMaybe :: Env a -> Var -> Maybe a
lookupEnvMaybe (Env env) x = Map.lookup x env

lookupEnv' :: UpperSemiLattice a => Env a -> Var -> a
lookupEnv' env x = lookupEnv env x bot

maybeLookupEnv' :: UpperSemiLattice a => Env a -> Maybe Var -> a
maybeLookupEnv' env (Just x) = lookupEnv env x bot
maybeLookupEnv' _   Nothing  = bot

bindEnv :: Env a -> Var -> a -> Env a
bindEnv (Env env) var val = val `seq` Env (Map.insert var val env)

updateEnv :: Env a -> Var -> a -> Env a
updateEnv env x val = bindEnv (unbindEnv env x) x val

unbindEnv :: Env a -> Var -> Env a
unbindEnv (Env env) x = Env (Map.delete x env)

maybeUnbindEnv :: Env a -> Maybe Var -> Env a
maybeUnbindEnv (Env env) (Just x) = Env (Map.delete x env)
maybeUnbindEnv      env   Nothing = env

instance (UpperSemiLattice a) => UpperSemiLattice (Env a) where
    bot                                = Env Map.empty
    leq (Env env1) (Env env2)          = Map.isSubmapOfBy leq env1 env2
    lub (Env env1) (Env env2)          = Env (Map.unionWith lub env1 env2)
