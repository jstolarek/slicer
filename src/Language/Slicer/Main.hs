module Main
    ( -- * Entry point to the program
      main
    ) where

import           Language.Slicer.Absyn          ( TyCtx, emptyTyCtx         )
import           Language.Slicer.Core           ( Ctx                       )
import           Language.Slicer.Env
import           Language.Slicer.Monad.Eval     ( EvalState, emptyEvalState )
import           Language.Slicer.Monad.Repl     ( runReplWithState          )
import           Language.Slicer.Run
import           Language.Slicer.Repl

import           Control.Monad                  ( foldM                     )
import           Control.Monad.Trans            ( lift                      )
import           System.Console.GetOpt
import           System.Console.Haskeline
import           System.Directory               ( getHomeDirectory          )
import           System.Environment             ( getArgs                   )
import           System.FilePath                ( joinPath                  )
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
noesc :: MonadException m => InputT m a -> InputT m a
noesc w = withInterrupt $ let loop = handle (\Interrupt -> loop) w in loop

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
  result <- runSlMIO (parseDesugarEval code)
  case result of
    Right (_, res, ty, _, _, _) -> putStrLn $ "val it = " ++ show (pPrint res)
                                           ++ " : "       ++ show (pPrint ty )
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

loadFile :: (TyCtx, Ctx, EvalState) -> FilePath -> IO (TyCtx, Ctx, EvalState)
loadFile (tyctx, gamma, evalSt) file = do
  putStrLn $ "Loading " ++ file
  hFlush stdout -- otherwise errors get printed before "Running"
  code   <- readFile file
  result <- runSlMIO (parseDesugarEval code)
  case result of
    Right (_, res, ty, tyctx', evalSt', gamma') ->
        do putStrLn $ "val it = " ++ show (pPrint res)
                   ++ " : "       ++ show (pPrint ty )
           return (tyctx', gamma', evalSt')
    Left err ->
        do hPutStrLn stderr (show err)
           return (tyctx, gamma, evalSt)

-- | Main program loop
main :: IO ()
main = do
  args <- getArgs
  case getOpt Permute options args of
    (flags, files, []) | isReplEnabled flags ->
        do putStrLn "Welcome to Slicer REPL"
           settings <- haskelineSettings
           state <- foldM loadFile (emptyTyCtx, emptyEnv, emptyEvalState) files
           runReplWithState state (runInputT settings $ noesc replLoop)
    ([], files, []) -> mapM_ compileAndRun files
    (_, _, errs) -> hPutStrLn stderr (concat errs ++ usageInfo usage options)
        where usage = "Usage: slicer [--repl|<file>.tml ...]"
