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
import           UntypedParser  ( parseRepl      )

import           Control.Monad.State.Strict
import           Text.ParserCombinators.Parsec ( ParseError )

type ReplM = StateT ReplState IO

data ParseResult = OK
                 | It String
                 | Error ParseError deriving (Eq)

data ReplState = ReplState
    { tyCtxSt :: TyCtx       -- ^ data type declarations
    , gammaSt :: Env T.Type  -- ^ variable types
    , envSt   :: Env T.Value -- ^ variable values
    }

emptyState :: ReplState
emptyState = ReplState { tyCtxSt = emptyTyCtx
                       , gammaSt = emptyEnv
                       , envSt   = emptyEnv }

getTyCtx :: ReplM TyCtx
getTyCtx = do
  ReplState { tyCtxSt = tyCtx } <- get
  return tyCtx

getEnv :: ReplM (Env T.Value)
getEnv = do
  ReplState { envSt = env } <- get
  return env

getGamma :: ReplM (Env T.Type)
getGamma = do
  ReplState { gammaSt = gamma } <- get
  return gamma

addDataDefn :: TyCtx -> ReplM ()
addDataDefn newCtx = do
  replState <- get
  put $ replState { tyCtxSt = newCtx }

addBinding :: Var -> T.Value -> T.Type -> ReplM ()
addBinding var val ty = do
  replState <- get
  let newEnv   = updateEnv (envSt   replState) var val
      newGamma = updateEnv (gammaSt replState) var ty
  put $ replState { envSt = newEnv, gammaSt = newGamma }

runRepl :: ReplM () -> IO ()
runRepl repl = evalStateT repl emptyState

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
           return (It $ "val it = " ++ show (pp (tyCtx,val)) ++ " : " ++ show (pp ty))
    Right (_     , Just expr) ->
        do env   <- getEnv
           gamma <- getGamma
           let (dexpr, ty) = desugar tyCtx gamma expr
           let val         = eval env dexpr
           return (It $ "val it = " ++ show (pp (tyCtx,val)) ++ " : " ++ show (pp ty))
