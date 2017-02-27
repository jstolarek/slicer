module Language.Slicer.Monad.Slice
    ( SliceM, runSliceM
    , allStoreHolesM, existsInStoreM, storeUpdateHoleM, storeDerefM
    , storeUpdateM, storeTraceUpdateM
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

storeUpdateM :: StoreLabel -> Value -> SliceM ()
storeUpdateM label value =
    do store <- getStore
       setStore (storeUpdate store label value)

storeTraceUpdateM :: StoreLabel -> Value -> SliceM ()
storeTraceUpdateM label value =
    do store <- getStore
       setStore (storeTraceUpdate store label value)

storeDerefM :: StoreLabel -> SliceM Value
storeDerefM label =
    do store <- getStore
       return (storeDeref store label)
