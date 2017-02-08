{-# LANGUAGE DeriveAnyClass   #-}
{-# LANGUAGE DeriveGeneric    #-}
{-# LANGUAGE NamedFieldPuns #-}

module Language.Slicer.Absyn
    ( -- * Abstract syntax
      Code(..), Con(..), Exp(..), Match(..), Type(..), Ctx

      -- * Type declarations
    , TyDecl(..), conL, conR, constrs, addTyDecl, getTyDeclByCon, getTyDeclByName

      -- * Type context
    , TyCtx(..), emptyTyCtx, nullTyCtx, unionTyCtx
    ) where

import           Language.Slicer.Env
import           Language.Slicer.Primitives

import           Control.DeepSeq ( NFData  )
import qualified Data.Map as Map
import           GHC.Generics    ( Generic )

newtype Con = C String deriving (Eq, Ord, Generic, NFData)

instance Show Con where
    show (C s) = s

data Code = Rec { funName  :: Var
                , funArgs  :: [(Var,Type)]
                , funRetTy :: Type
                , funBody  :: Exp
                , funLabel :: Maybe String}
           deriving (Show, Eq, Ord)

data Match = Match (Map.Map Con (Maybe Var, Exp))
           deriving (Show, Eq, Ord)

-- Synonym for a recursive type of the form rec alpha.tau1 + tau2 and its
-- constructors.
data TyDecl = TyDecl
    { dataName :: TyVar
    , constrL  :: (Con, Type)
    , constrR  :: (Con, Type)
    } deriving (Show, Eq, Ord, Generic, NFData)

conL :: TyDecl -> Con
conL = fst . constrL

conR :: TyDecl -> Con
conR = fst . constrR

constrs :: TyDecl -> (Con, Con)
constrs (TyDecl _ (con1, _) (con2, _)) = (con1, con2)

data TyCtx = TyCtx
    { tydecls   :: Map.Map TyVar TyDecl
    , constrmap :: Map.Map Con (Type, TyVar)
    } deriving (Show, Eq, Ord, Generic, NFData)

emptyTyCtx :: TyCtx
emptyTyCtx = TyCtx Map.empty Map.empty

unionTyCtx :: TyCtx -> TyCtx -> TyCtx
unionTyCtx (TyCtx tydecls1 constrmap1) (TyCtx tydecls2 constrmap2) =
   TyCtx (Map.union tydecls1 tydecls2) (Map.union constrmap1 constrmap2)

nullTyCtx :: TyCtx -> Bool
nullTyCtx (TyCtx tydecls constrmap) = Map.null tydecls && Map.null constrmap

addTyDecl :: TyCtx -> TyDecl -> TyCtx
addTyDecl (TyCtx tydecls constrmap) (decl@(TyDecl name lCon rCon)) =
    let tydecls' = Map.insert name decl tydecls
        constrmap' = foldl (\cmap (k,tys) -> Map.insert k (tys,name) cmap)
                            constrmap [lCon, rCon]
    in TyCtx tydecls' constrmap'

-- get the declaration that defines the given constructor
-- assumes we don't reuse ctor names
getTyDeclByCon :: TyCtx -> Con -> Maybe (TyDecl, Type)
getTyDeclByCon decls k = do (tys,ty) <- Map.lookup k (constrmap decls)
                            decl <- getTyDeclByName decls ty
                            return (decl,tys)

getTyDeclByName :: TyCtx -> TyVar -> Maybe TyDecl
getTyDeclByName decls a = Map.lookup a (tydecls decls)

data Exp = Var Var | Let Var Exp Exp | LetR Var Exp
         | Unit
         | CBool Bool | If Exp Exp Exp
         | CInt Int | Op Primitive [Exp]
         | CString String
         | Pair Exp Exp | Fst Exp | Snd Exp
         | Con Con Exp | Case Exp Match
         | Fun Code | App Exp Exp
         -- References
         | Ref Exp  | Deref Exp | Assign Exp Exp | Seq Exp Exp
         -- run-time tracing
         | Trace Exp
         -- holes
         | Hole Type
           deriving (Show, Eq, Ord)

data Type = IntTy | BoolTy | UnitTy | StringTy
          | PairTy Type Type | SumTy Type Type | FunTy Type Type
          | TyVar TyVar
          -- References
          | RefTy Type
          -- Trace types
          | TraceTy Type
            deriving (Show, Eq, Ord, Generic, NFData)

type Ctx = Env Type
