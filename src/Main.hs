module Main
    ( -- * Entry point to the program
      main
    ) where

import           Absyn          ( emptyTyCtx  )
import           Desugar
import           Env
import           Eval
import           Monad
import           PrettyPrinting ( pp          )
import           Repl
import           Resugar        () -- dummy import to force module compilation
import           Trace          ( Value, Type )
import           Parser         ( parseIn     )

import           Control.Monad.Trans      ( lift              )
import           System.Console.GetOpt
import           System.Console.Haskeline
import           System.Directory         ( getHomeDirectory  )
import           System.Environment       ( getArgs           )
import           System.FilePath          ( joinPath          )
import           System.IO                ( hPutStrLn, stderr )

-- | Command line flags
data Flag = Repl deriving Eq

-- | Command line options
options :: [OptDescr Flag]
options =
    [ Option [] ["repl"] (NoArg Repl) "Run interactive interpreter" ]

-- | Is REPL mode enabled via command line flags?
isReplEnabled :: [Flag] -> Bool
isReplEnabled f = Repl `elem` f

-- | Parse a program and evaluate it.  Return value and its type
parse_desugar_eval :: String -> SlM (Value, Type)
parse_desugar_eval s = do
    (tyctx, e) <- parseIn s emptyTyCtx
    (e', ty)   <- desugar tyctx emptyEnv e
    v          <- eval emptyEnv e'
    return (v, ty)

-- | Catch C^ interrupts when running the REPL
noesc :: MonadException m => InputT m a -> InputT m a
noesc w = withInterrupt $ let loop = handle (\Interrupt -> loop) w in loop

-- | Haskeline settings: store REPL command history in users' home directory
haskelineSettings :: IO (Settings ReplM)
haskelineSettings = do
  homeDir <- getHomeDirectory
  return Settings { complete       = completeFilename
                  , historyFile    = Just $ joinPath [ homeDir
                                                     , ".slicer.history" ]
                  , autoAddHistory = True
                  }

-- | Compile and run a given program
run :: FilePath -> IO ()
run arg = do
  putStrLn $ "Running " ++ arg
  code   <- readFile arg
  result <- runSlM $ parse_desugar_eval code
  case result of
    Right (v, ty) -> putStrLn $ "val it =  " ++ show (pp v) ++
                                " : " ++ show (pp ty)
    Left err -> hPutStrLn stderr (show err)

-- | Start an interactive loop
replLoop :: InputT ReplM ()
replLoop = do
  input <- getInputLine "slicer> "
  case input of
    Nothing     -> return () -- Ctrl + D
    Just ""     -> replLoop  -- Enter
    Just "quit" -> return ()
    Just line   -> do
           result <- lift $ parseAndEvalLine line
           case result of
             OK        -> replLoop
             It    str -> outputStrLn str        >> replLoop
             Error err -> outputStrLn (show err) >> replLoop

-- | Main program loop
main :: IO ()
main = do
  args <- getArgs
  case getOpt Permute options args of
    -- start REPL only when no files are given on the command line
    (flags, [], []) | isReplEnabled flags -> do
                        putStrLn "Welcome to Slicer REPL"
                        settings <- haskelineSettings
                        runRepl (runInputT settings $ noesc replLoop)
    ([], files, []) -> mapM_ run files
    (_, _, errs) -> hPutStrLn stderr (concat errs ++ usageInfo usage options)
        where usage = "Usage: slicer [--repl|<file>.tml ...]"
