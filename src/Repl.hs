{-# LANGUAGE NamedFieldPuns #-}

module Repl
    ( ReplM, runRepl, parseAndEvalLine

    , ParseResult(..)
    ) where

import           Absyn
import           Desugar        ( desugar        )
import           Env
import           Eval           ( eval           )
import           PrettyPrinting
import           Resugar        () -- PP instances only
import qualified Trace as T     ( Value, Type    )
import           Parser         ( parseRepl      )

import           Control.Monad.State.Strict
import           Text.ParserCombinators.Parsec ( ParseError )

-- | REPL monad contains a state on top of IO
type ReplM = StateT ReplState IO

-- | Possible results of parsing and evaluating user input
data ParseResult = OK               -- ^ Success without reply
                 | It String        -- ^ Success and reply to user
                 | Error ParseError -- ^ Parse error
                   deriving (Eq)

-- | REPL state
data ReplState = ReplState
    { tyCtxSt :: TyCtx       -- ^ Data type declarations
    , gammaSt :: Env T.Type  -- ^ Context Γ, stores variable types
    , envSt   :: Env T.Value -- ^ Environment ρ, stores variable values
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
getGamma :: ReplM (Env T.Type)
getGamma = do
  ReplState { gammaSt } <- get
  return gammaSt

-- | Get environment
getEnv :: ReplM (Env T.Value)
getEnv = do
  ReplState { envSt } <- get
  return envSt

-- | Add new data definition
addDataDefn :: TyCtx -> ReplM ()
addDataDefn newCtx = do
  replState <- get
  put $ replState { tyCtxSt = newCtx }

-- | Add new binding (name + value + type)
addBinding :: Var -> T.Value -> T.Type -> ReplM ()
addBinding var val ty = do
  replState <- get
  let newEnv   = updateEnv (envSt   replState) var val
      newGamma = updateEnv (gammaSt replState) var ty
  put $ replState { envSt = newEnv, gammaSt = newGamma }

-- | Run REPL monad
runRepl :: ReplM () -> IO ()
runRepl repl = evalStateT repl emptyState

-- | Main REPL logic responsible for parsing a line of input, executing it,
-- updating the REPL state accordingly and returning the result to user
parseAndEvalLine :: String -> ReplM ParseResult
parseAndEvalLine line = do
  tyCtx <- getTyCtx
  case parseRepl line tyCtx of
    Left err -> return (Error err)
    Right (tyCtx', Nothing ) -> addDataDefn tyCtx' >> return OK
    Right (_     , Just (LetR var expr)) ->
        do env   <- getEnv
           gamma <- getGamma
           let (dexpr, ty) = desugar tyCtx gamma expr
           let val         = eval env dexpr
           val `seq` addBinding var val ty
           return (It $ "val it = " ++ show (pp (tyCtx,val)) ++
                        " : " ++ show (pp ty))
    Right (_     , Just expr) ->
        do env   <- getEnv
           gamma <- getGamma
           let (dexpr, ty) = desugar tyCtx gamma expr
           let val         = eval env dexpr
           return (It $ "val it = " ++ show (pp (tyCtx,val)) ++
                        " : " ++ show (pp ty))
