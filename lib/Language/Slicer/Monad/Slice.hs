{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving         #-}

module Language.Slicer.Monad.Slice
    ( SliceM, runSliceM
    , allStoreHolesM, existsInStoreM, storeUpdateHoleM, storeDerefM
    , storeUpdateM
    , storeUpdateArrIdxM, storeUpdateArrHoleM, storeUpdateArrIdxHoleM
    , storeDerefArrM
    , storeDerefArrIdxM

    , setEnv, withEmptyEnv, resetEnv, setSingletonEnv
    , lookupAndUnbind, maybeLookupAndUnbind
    ) where

import           Language.Slicer.Env
import           Language.Slicer.Core
import           Language.Slicer.UpperSemiLattice

import           Control.Monad.State.Strict

type SliceM = State (Env Value, Store)

runSliceM :: Store -> SliceM (Exp, Trace) -> (Env Value, Store, Exp, Trace)
runSliceM store thing =
    let ((e, t), (env, store')) = runState thing (emptyEnv, store)
    in (env, store', e, t)

getEnv :: SliceM (Env Value)
getEnv = do
  (env, _) <- get
  return env

setEnv :: Env Value -> SliceM ()
setEnv env = do
  store <- getStore
  put (env, store)

-- | Returns current environment and empties it.
resetEnv :: SliceM (Env Value)
resetEnv = do
  env <- getEnv
  setEnv emptyEnv
  return env

-- | Runs a given monadic computation inside an empty environment.
-- See Note [Handling slicing environment inside a monad]
withEmptyEnv :: SliceM a -> SliceM a
withEmptyEnv thing = do
  store <- getStore
  let (result, (env', store')) = runState thing (emptyEnv, store)
  env <- getEnv
  setEnv (env `lub` env')
  setStore store'
  return result

getStore :: SliceM Store
getStore = do
  (_, store) <- get
  return store

setStore :: Store -> SliceM ()
setStore store = do
  env <- getEnv
  put (env, store)

-- | Check if all store labels are store holes (according to `isStoreHole`)
allStoreHolesM :: StoreLabels -> SliceM Bool
allStoreHolesM labels =
    do store <- getStore
       return (allStoreHoles store labels)

existsInStoreM :: StoreLabel -> SliceM Bool
existsInStoreM labels =
    do store <- getStore
       return (existsInStore store labels)

storeUpdateHoleM :: StoreLabel -> SliceM ()
storeUpdateHoleM label =
    do store <- getStore
       setStore (storeUpdateHole store label)

storeUpdateArrHoleM :: StoreLabel -> SliceM ()
storeUpdateArrHoleM label =
    do store <- getStore
       setStore (storeUpdateArrHole store label)

storeUpdateArrIdxHoleM :: StoreLabel -> Int -> SliceM ()
storeUpdateArrIdxHoleM label idx =
    do store <- getStore
       setStore (storeUpdateArrIdxHole store label idx)

storeUpdateM :: StoreLabel -> Value -> SliceM ()
storeUpdateM label value =
    do store <- getStore
       setStore (storeUpdate store label value)

storeUpdateArrIdxM :: StoreLabel -> Int -> Value -> SliceM ()
storeUpdateArrIdxM label idx value =
    do store <- getStore
       setStore (storeUpdateArrIdx store label idx value)

storeDerefM :: StoreLabel -> SliceM Value
storeDerefM label =
    do store <- getStore
       return (storeDeref store label)

storeDerefArrIdxM :: StoreLabel -> Int -> SliceM Value
storeDerefArrIdxM label idx =
    do store <- getStore
       return (storeDerefArrIdx store label idx)

storeDerefArrM :: StoreLabel -> Int -> SliceM Value
storeDerefArrM label dim =
    do store <- getStore
       return (storeDerefArr store label dim)

setSingletonEnv :: Var -> Value -> SliceM ()
setSingletonEnv x v = setEnv (singletonEnv x v)

lookupAndUnbind :: Var -> SliceM Value
lookupAndUnbind x = do
  env <- getEnv
  let p = lookupEnv' env x
  setEnv (unbindEnv env x)
  return p

maybeLookupAndUnbind :: Maybe Var -> SliceM Value
maybeLookupAndUnbind Nothing  = return bot
maybeLookupAndUnbind (Just x) = lookupAndUnbind x
