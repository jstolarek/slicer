module Language.Slicer.Monad.Slice
    ( SliceM, runSliceM
    , allStoreHolesM, existsInStoreM, storeUpdateHoleM, storeDerefM
    , storeUpdateM
    , storeUpdateArrIdxM, storeUpdateArrHoleM, storeUpdateArrIdxHoleM
    , storeDerefArrM
    , storeDerefArrIdxM
    ) where

import           Language.Slicer.Env
import           Language.Slicer.Core

import           Control.Monad.State.Strict

type SliceM = State Store

runSliceM :: Store -> SliceM (Env Value, Exp, Trace)
          -> (Env Value, Store, Exp, Trace)
runSliceM store thing =
    let ((env, e, t), store') = runState thing store
    in (env, store', e, t)

getStore :: SliceM Store
getStore = get

setStore :: Store -> SliceM ()
setStore = put

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
