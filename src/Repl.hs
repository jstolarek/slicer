module Repl
    ( ReplM, runRepl, parseAndEvalLine

    , ParseResult(..)
    ) where

import           Absyn
import           Desugar        ( desugar     )
import           Env
import           Eval           ( eval        )
import           PrettyPrinting
import           Resugar
import qualified Trace as T     ( Value, Type )
import           UntypedParser  ( parseRepl   )

import           Control.Monad.State.Strict
import           Text.ParserCombinators.Parsec ( ParseError )

type ReplM = StateT ReplState IO

data ParseResult = OK
                 | It String
                 | Error ParseError deriving (Eq)

data ReplState = ReplState
    { tyCtx :: TyCtx       -- ^ data type declarations
    , gamma :: Env T.Type  -- ^ variable types
    , env   :: Env T.Value -- ^ variable values
    }

emptyState :: ReplState
emptyState = ReplState { tyCtx = emptyTyCtx
                       , gamma = emptyEnv
                       , env   = emptyEnv }

getTyCtx :: ReplM TyCtx
getTyCtx = do
  ReplState { tyCtx = tyCtx } <- get
  return tyCtx

getEnv :: ReplM (Env T.Value)
getEnv = do
  ReplState { env = env } <- get
  return env

getGamma :: ReplM (Env T.Type)
getGamma = do
  ReplState { gamma = gamma } <- get
  return gamma

addDataDefn :: TyCtx -> ReplM ()
addDataDefn newCtx = do
  replState <- get
  put $ replState { tyCtx = newCtx }

addBinding :: Var -> T.Value -> T.Type -> ReplM ()
addBinding var val ty = do
  replState <- get
  let newEnv   = updateEnv (env   replState) var val
      newGamma = updateEnv (gamma replState) var ty
  put $ replState { env = newEnv, gamma = newGamma }

runRepl :: ReplM () -> IO ()
runRepl repl = evalStateT repl emptyState

parseAndEvalLine :: String -> ReplM ParseResult
parseAndEvalLine line = do
  tyCtx <- getTyCtx
  case parseRepl line tyCtx of
    Left err -> return (Error err)
    Right (tyCtx, Nothing ) -> addDataDefn tyCtx >> return OK
    Right (_    , Just (LetR var exp)) ->
        do env   <- getEnv
           gamma <- getGamma
           let (dexp, ty) = desugar tyCtx gamma exp
           let val        = eval env dexp
           val `seq` addBinding var val ty
           return (It $ "val it =  " ++ show (pp (tyCtx,val)) ++ " : " ++ show (pp ty))
    Right (_    , Just exp) ->
        do env   <- getEnv
           gamma <- getGamma
           let (dexp, ty) = desugar tyCtx gamma exp
           let val        = eval env dexp
           return (It $ "val it =  " ++ show (pp (tyCtx,val)) ++ " : " ++ show (pp ty))
