module Main
    ( -- * Entry point to the program
      main
    ) where

import           Absyn          ( emptyTyCtx  )
import           Desugar
import           Env
import           Eval
import           PrettyPrinting ( pp          )
import           Repl
import           Resugar        () -- dummy import to force module compilation
import           Trace          ( Value, Type )
import           UntypedParser  ( parseIn     )

import           Control.Monad.Trans
import           System.Console.GetOpt
import           System.Console.Haskeline
import           System.Directory
import           System.Environment
import           System.FilePath
import           System.IO

-- | Command line flags
data Flag = Repl deriving Eq

-- | Command line options
options :: [OptDescr Flag]
options =
    [ Option [] ["repl"] (NoArg Repl) "Run interactive interpreter" ]

isReplEnabled :: [Flag] -> Bool
isReplEnabled f = Repl `elem` f

parse_desugar_eval :: String -> (Value, Type)
parse_desugar_eval s =
    let (tyctx, e) = parseIn s emptyTyCtx
        (e', ty)   = desugar tyctx emptyEnv e
        v          = eval emptyEnv e'
    in (v, ty)

main :: IO ()
main = do
  args <- getArgs
  case getOpt Permute options args of
    (flags, [], []) | isReplEnabled flags -> do
                        putStrLn "Welcome to Slicer REPL"
                        settings <- haskelineSettings
                        runRepl (runInputT settings $ noesc replLoop)
    ([], files, []) -> mapM_ run files
    (_, _, errs) -> hPutStrLn stderr (concat errs ++ usageInfo usage options)
        where usage = "Usage: slicer [--repl|<file>.tml ...]"

run :: String -> IO ()
run arg = do
  putStrLn $ "Running " ++ arg
  code <- readFile arg
  let (v,ty) = parse_desugar_eval code
  putStrLn $ "val it =  " ++ show (pp v) ++ " : " ++ show (pp ty)

noesc :: MonadException m => InputT m a -> InputT m a
noesc w = withInterrupt $ let loop = handle (\Interrupt -> loop) w in loop

haskelineSettings :: IO (Settings ReplM)
haskelineSettings = do
  homeDir <- getHomeDirectory
  return Settings { complete       = completeFilename
                  , historyFile    = Just $ joinPath [ homeDir
                                                     , ".slicer.history" ]
                  , autoAddHistory = True
                  }

replLoop :: InputT ReplM ()
replLoop = do
  input <- getInputLine "slicer> "
  case input of
    Nothing     -> return ()
    Just ""     -> replLoop
    Just "quit" -> return ()
    Just line   -> do
           result <- lift $ parseAndEvalLine line
           case result of
             OK        -> replLoop
             It    str -> outputStrLn str        >> replLoop
             Error err -> outputStrLn (show err) >> replLoop
