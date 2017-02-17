module Language.Slicer.Repl
    ( ReplM, runRepl, parseAndEvalLine, loadFileToRepl

    , ParseResult(..)
    ) where

import           Language.Slicer.Absyn
import           Language.Slicer.Run               ( desugarEval )
import           Language.Slicer.Env
import           Language.Slicer.Error
import           Language.Slicer.Monad
import           Language.Slicer.Monad.Repl
import           Language.Slicer.Parser            ( parseRepl   )

import           Control.Exception                 ( assert      )
import           Control.Monad                     ( when, liftM )
import           Control.Monad.IO.Class            ( liftIO      )
import           System.IO
import           Text.PrettyPrint.HughesPJClass

-- | Possible results of parsing and evaluating user input
data ParseResult = OK               -- ^ Success without reply
                 | It String        -- ^ Success and reply to user
                 | Error SlicerError -- ^ Parse error
                   deriving ( Eq )

loadFileToRepl :: String -> ReplM ()
loadFileToRepl file = do
  code <- liftIO (do putStr $ "Loading " ++ file ++ "..."
                     hFlush stdout
                     lines `liftM` readFile file)
  loadLinesToRepl (filter (not . null) code)

loadLinesToRepl :: [String] -> ReplM ()
loadLinesToRepl [] = liftIO (putStrLn "done")
loadLinesToRepl (line : ls) = do
  result <- parseAndEvalLine line
  case result of
    Error err -> liftIO (putStrLn "" >> putStrLn (show err))
    _         -> loadLinesToRepl ls

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
           dsgres <- runSlMIO (desugarEval tyCtx gamma evalS expr)
           case dsgres of
             Right (val, res, ty, st) ->
                 do setEvalState st
                     -- See Note [Handling let bindings]
                    when (isLetBinding expr)
                             (val `seq` addBinding (getVar expr) val ty)
                    return (It $ "val it = " ++ show (pPrint res) ++
                                 " : "       ++ show (pPrint ty))
             Left err -> return (Error err)

-- Note [Handling let bindings]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- If parsed expression is a let-binding then we must add it as a new binding to
-- our environment.  Once a binding is desugared and evaluated we add it to
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
