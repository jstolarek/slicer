{-# LANGUAGE NamedFieldPuns #-}

module Repl
    ( ReplM, runRepl, parseAndEvalLine

    , ParseResult(..)
    ) where

import           Absyn
import qualified Core as C      ( Value, Type    )
import           Desugar        ( desugar        )
import           Env
import           Eval           ( eval           )
import           Monad
import           PrettyPrinting
import           Resugar        () -- PP instances only
import           Parser         ( parseRepl      )

import           Control.Exception ( assert )
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
    { tyCtxSt :: TyCtx       -- ^ Data type declarations
    , gammaSt :: Env C.Type  -- ^ Context Γ, stores variable types
    , envSt   :: Env C.Value -- ^ Environment ρ, stores variable values
    }

-- | Empty REPL state.  Used when starting the REPL
emptyState :: ReplState
emptyState = ReplState { tyCtxSt = emptyTyCtx
                       , gammaSt = emptyEnv
                       , envSt   = emptyEnv }

-- | Get data type declarations
getTyCtx :: ReplM TyCtx
getTyCtx = do
  ReplState { tyCtxSt } <- get
  return tyCtxSt

-- | Get context
getGamma :: ReplM (Env C.Type)
getGamma = do
  ReplState { gammaSt } <- get
  return gammaSt

-- | Get environment
getEnv :: ReplM (Env C.Value)
getEnv = do
  ReplState { envSt } <- get
  return envSt

-- | Add new data definition
addDataDefn :: TyCtx -> ReplM ()
addDataDefn newCtx = do
  st@(ReplState { tyCtxSt }) <- get
  put $ st { tyCtxSt = unionTyCtx tyCtxSt newCtx }

-- | Add new binding (name + value + type)
addBinding :: Var -> C.Value -> C.Type -> ReplM ()
addBinding var val ty = do
  replState <- get
  let newEnv   = updateEnv (envSt   replState) var val
      newGamma = updateEnv (gammaSt replState) var ty
  put $ replState { envSt = newEnv, gammaSt = newGamma }

dropBinding :: Var -> ReplM ()
dropBinding var = do
  replState <- get
  let newEnv   = unbindEnv (envSt   replState) var
      newGamma = unbindEnv (gammaSt replState) var
  put $ replState { envSt = newEnv, gammaSt = newGamma }

-- | Run REPL monad
runRepl :: ReplM () -> IO ()
runRepl repl = evalStateT repl emptyState

-- | Main REPL logic responsible for parsing a line of input, executing it,
-- updating the REPL state accordingly and returning the result to user
parseAndEvalLine :: String -> ReplM ParseResult
parseAndEvalLine line = do
  tyCtx  <- getTyCtx
  result <- runSlM $ parseRepl line tyCtx
  case result of
    Left err -> return (Error err)
    Right (tyCtx', Nothing ) -> addDataDefn tyCtx' >> return OK
    Right (tyCtx', Just expr) ->
        -- INVARIANT: if we parsed an expression then we could not have parsed a
        -- data definition, hence the parsed context must be empty.
        assert (nullTyCtx tyCtx') $
        do let isLet = isLetBinding expr -- See Note [Handling let bindings]
               var   = getVar expr -- only safe to force when isLet == True
           when isLet (dropBinding var)
           env    <- getEnv
           gamma  <- getGamma
           dsgres <- runSlM $ do
                          (dexpr, ty) <- desugar tyCtx gamma expr
                          val         <- eval env dexpr
                          return (val, ty)
           case dsgres of
             Right (val, ty) ->
                 do when isLet (val `seq` addBinding var val ty)
                    return (It $ "val it = " ++ show (pp (tyCtx,val)) ++
                                 " : " ++ show (pp ty))
             Left err -> return (Error err)

-- Note [Handling let bindings]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- If parsed expression is a let-binding then we must add it as a new binding to
-- our environment.  To ensure that desugaring does the right thing we have to
-- first drop any existing binding with the same name - otherwise bad things
-- happen.  Once the binding is desugared and evaluated we add it to the
-- environment.  Keep in mind that the result of getVar can only be forced
-- safely when the REPL expression is a let binding.

-- | Is this expression a REPL let binding?
isLetBinding :: Exp -> Bool
isLetBinding (LetR _ _) = True
isLetBinding _          = False

-- | Get the variable binder
getVar :: Exp -> Var
getVar (LetR var _) = var
getVar _            = error "REPL error: cannot get var from non-let expression"
