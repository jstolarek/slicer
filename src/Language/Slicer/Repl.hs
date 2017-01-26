{-# LANGUAGE NamedFieldPuns #-}

module Language.Slicer.Repl
    ( ReplM, runRepl, parseAndEvalLine

    , ParseResult(..)
    ) where

import           Language.Slicer.Absyn
import qualified Language.Slicer.Core as C         ( Value, Type )
import           Language.Slicer.Desugar           ( desugar     )
import           Language.Slicer.Env
import           Language.Slicer.Error
import           Language.Slicer.Eval              ( run         )
import           Language.Slicer.Monad
import           Language.Slicer.Monad.Eval hiding ( addBinding  )
import qualified Language.Slicer.Monad.Eval as E   ( addBinding  )
import           Language.Slicer.PrettyPrinting
import           Language.Slicer.Resugar           () -- PP instances only
import           Language.Slicer.Parser            ( parseRepl   )

import           Control.Exception                 ( assert      )
import           Control.Monad.State.Strict

-- | REPL monad contains a state on top of IO
type ReplM = StateT ReplState IO

-- | Possible results of parsing and evaluating user input
data ParseResult = OK               -- ^ Success without reply
                 | It String        -- ^ Success and reply to user
                 | Error SlicerError -- ^ Parse error
                   deriving ( Eq )

-- | REPL state
data ReplState = ReplState
    { tyCtxS :: TyCtx             -- ^ Data type declarations
    , gammaS :: Env C.Type        -- ^ Context Γ, stores variable types
    , evalS  :: EvalState C.Value -- ^ Evaluation monad state. Contains
                                  --   environment ρ (variable values) and
                                  --   reference store
    }

-- | Empty REPL state.  Used when starting the REPL
emptyState :: ReplState
emptyState = ReplState { tyCtxS = emptyTyCtx
                       , gammaS = emptyEnv
                       , evalS  = emptyEvalState }

-- | Get data type declarations
getTyCtx :: ReplM TyCtx
getTyCtx = do
  ReplState { tyCtxS } <- get
  return tyCtxS

-- | Get context
getGamma :: ReplM (Env C.Type)
getGamma = do
  ReplState { gammaS } <- get
  return gammaS

-- | Get environment
getEvalState :: ReplM (EvalState C.Value)
getEvalState = do
  ReplState { evalS } <- get
  return evalS

setEvalState :: EvalState C.Value -> ReplM ()
setEvalState newEvalSt = do
  replState <- get
  put $ replState { evalS = newEvalSt }

-- | Add new data definition
addDataDefn :: TyCtx -> ReplM ()
addDataDefn newCtx = do
  st@(ReplState { tyCtxS }) <- get
  put $ st { tyCtxS = unionTyCtx tyCtxS newCtx }

-- | Add new binding (name + value + type)
addBinding :: Var -> C.Value -> C.Type -> ReplM ()
addBinding var val ty = do
  replState@(ReplState { evalS, gammaS }) <- get
  let evalS'   = E.addBinding evalS var val
      newGamma = updateEnv gammaS var ty
  put $ replState { evalS = evalS', gammaS = newGamma }

-- | Run REPL monad
runRepl :: ReplM () -> IO ()
runRepl repl = evalStateT repl emptyState

-- | Main REPL logic responsible for parsing a line of input, executing it,
-- updating the REPL state accordingly and returning the result to user
parseAndEvalLine :: String -> ReplM ParseResult
parseAndEvalLine line = do
  tyCtx  <- getTyCtx
  result <- runSlMIO $ liftSlM (parseRepl line tyCtx)
  case result of
    Left err -> return (Error err)
    Right (tyCtx', Nothing  ) -> addDataDefn tyCtx' >> return OK
    Right (tyCtx', Just expr) ->
        -- INVARIANT: if we parsed an expression then we could not have parsed a
        -- data definition, hence the parsed context must be empty.
        assert (nullTyCtx tyCtx') $
        do evalS  <- getEvalState
           gamma  <- getGamma
           dsgres <- runSlMIO $ do
                          (dexpr, ty) <- liftSlM (desugar tyCtx gamma expr)
                          (val, st)   <- run evalS dexpr
                          return (val, ty, st)
           case dsgres of
             Right (val, ty, st) ->
                 do setEvalState st
                     -- See Note [Handling let bindings]
                    when (isLetBinding expr)
                             (val `seq` addBinding (getVar expr) val ty)
                    return (It $ "val it = " ++ show (pp (tyCtx,val)) ++
                                 " : "       ++ show (pp ty))
             Left err -> return (Error err)

-- Note [Handling let bindings]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- If parsed expression is a let-binding then we must add it as a new binding to
-- our environment.  Once the binding is desugared and evaluated we add it to
-- the environment.  Keep in mind that the result of getVar can only be forced
-- safely when the REPL expression is a let binding.

-- | Is this expression a REPL let binding?
isLetBinding :: Exp -> Bool
isLetBinding (LetR _ _) = True
isLetBinding _          = False

-- | Get the variable binder
getVar :: Exp -> Var
getVar (LetR var _) = var
getVar _            = error "REPL error: cannot get var from non-let expression"
