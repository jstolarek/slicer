{-# LANGUAGE NamedFieldPuns #-}

module Absyn
    ( -- * Abstract syntax
      Code(..), Con(..), Exp(..), Lab(..), Match(..), Type(..), Ctx

      -- * Type declarations
    , TyDecl(..), addTyDecl, getTyDeclByCon, getTyDeclByName, getConstrs

      -- * Type context
    , TyCtx(..), emptyTyCtx
    ) where

import           Env
import           Primitives

import           Data.Maybe
import qualified Data.Map as Map

newtype Lab = L String deriving (Show, Eq, Ord)
newtype Con = C String deriving (Eq, Ord)

instance Show Con where
    show (C s) = s

data Code = Rec { funName  :: Var
                , funArgs  :: [(Var,Type)]
                , funRetTy :: Type
                , funBody  :: Exp
                , funLabel :: Maybe String}
           deriving (Show, Eq, Ord)

data Match = Match (Map.Map Con ([Var], Exp))
           deriving (Show, Eq, Ord)

-- Synonym for a recursive type of the form rec alpha.tau1 + tau2 and its
-- constructors.
data TyDecl = TyDecl
    { name    :: TyVar
    , constrs :: [(Con, Type)]
    } deriving (Show, Eq, Ord)

data TyCtx = TyCtx
    { tydecls   :: Map.Map TyVar TyDecl
    , constrmap :: Map.Map Con (Type,TyVar)
    } deriving (Show, Eq, Ord)

emptyTyCtx :: TyCtx
emptyTyCtx = TyCtx Map.empty Map.empty

addTyDecl :: TyCtx -> TyDecl -> TyCtx
addTyDecl (TyCtx tydecls constrmap) (decl@(TyDecl name constrs)) =
    let tydecls' = Map.insert name decl tydecls
        constrmap' = foldl (\cmap (k,tys) -> Map.insert k (tys,name) cmap)
                            constrmap constrs
    in TyCtx tydecls' constrmap'


-- get the declaration that defines the given constructor
-- assumes we don't reuse ctor names
getTyDeclByCon :: TyCtx -> Con -> Maybe (TyDecl, Type)
getTyDeclByCon decls k = do (tys,ty) <- Map.lookup k (constrmap decls)
                            decl <- getTyDeclByName decls ty
                            return (decl,tys)
getTyDeclByName :: TyCtx -> TyVar -> Maybe TyDecl
getTyDeclByName decls a = Map.lookup a (tydecls decls)

-- Convenient shorthand.
getConstrs :: TyCtx -> TyVar -> [Con]
getConstrs tyCtx = map fst . constrs . fromJust . getTyDeclByName tyCtx

data Exp = Var Var | Let Var Exp Exp | LetR Var Exp
         | Unit
         | CBool Bool | If Exp Exp Exp
         | CInt Int | Op Primitive [Exp]
         | CString String
         | Pair Exp Exp | Fst Exp | Snd Exp
         | Con Con [Exp] | Case Exp Match
         | Fun Code | App Exp Exp
           -- run-time tracing
         | Trace Exp
         -- labels, holes
         | Hole Type
           deriving (Eq,Show,Ord)

data Type = IntTy | BoolTy | UnitTy | StringTy
          | PairTy Type Type | SumTy Type Type | FunTy Type Type
          | TyVar TyVar
            -- Trace types
          | TraceTy Ctx Type
            deriving (Eq,Ord,Show)

type Ctx = Env Type
