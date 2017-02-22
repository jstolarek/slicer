module Language.Slicer.Monad.Slice
    ( SliceM, runSliceM
    ) where

import           Control.Monad.Identity

type SliceM = Identity

runSliceM :: SliceM a -> a
runSliceM = runIdentity
