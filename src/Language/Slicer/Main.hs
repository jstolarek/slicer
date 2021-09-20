module Main
    ( -- * Entry point to the program
      main
    ) where

import           Language.Slicer.Run
import           Language.Slicer.Repl

import           Control.Monad.Trans            ( MonadIO, lift     )
import           Control.Monad.Catch
import           System.Console.GetOpt
import           System.Console.Haskeline
import           System.Directory               ( getHomeDirectory  )
import           System.Environment             ( getArgs           )
import           System.FilePath                ( joinPath          )
import           System.IO
import           Text.PrettyPrint.HughesPJClass

-- | Command line flags
data Flag = Repl deriving Eq

-- | Command line options
options :: [OptDescr Flag]
options =
    [ Option [] ["repl"] (NoArg Repl) "Run interactive interpreter" ]

-- | Is REPL mode enabled via command line flags?
isReplEnabled :: [Flag] -> Bool
isReplEnabled f = Repl `elem` f

-- | Catch C^ interrupts when running the REPL
noesc :: (MonadMask m, MonadIO m) => InputT m a -> InputT m a
noesc w = withInterrupt $ let loop = handleInterrupt loop w in loop

-- | Haskeline settings: store REPL command history in users' home directory
haskelineSettings :: IO (Settings ReplM)
haskelineSettings = do
  homeDir <- getHomeDirectory
  return Settings
             { complete       = completeFilename
             , historyFile    = Just $ joinPath [ homeDir, ".slicer.history" ]
             , autoAddHistory = True
             }

-- | Compile and run a given program
compileAndRun :: FilePath -> IO ()
compileAndRun arg = do
  putStrLn $ "Running " ++ arg
  hFlush stdout -- otherwise errors get printed before "Running"
  code   <- readFile arg
  result <- runSlM (parseDesugarEval code)
  case result of
    Right (_, res, ty, _) -> putStrLn $ "val it = " ++ show (pPrint res) ++
                                        " : "       ++ show (pPrint ty )
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
    (flags, files, []) | isReplEnabled flags -> do
       putStrLn "Welcome to Slicer REPL"
       settings <- haskelineSettings
       let loadFiles = mapM_ loadFileToRepl files
       runRepl (loadFiles >> (runInputT settings $ noesc replLoop))
    ([], files, []) -> mapM_ compileAndRun files
    (_, _, errs) -> hPutStrLn stderr (concat errs ++ usageInfo usage options)
        where usage = "Usage: slicer [--repl|<file>.tml ...]"
