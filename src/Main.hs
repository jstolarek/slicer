module Main where

import System.Environment


import Trace
import TraceGraph
import Eval
import Slice
import Annot
import Compact
import UpperSemiLattice
import Env
import Profile
import UntypedParser
import Desugar
import qualified UntypedParser as P
import qualified Absyn as A
import Util

parse_desugar_eval :: String -> (Value,Type)
parse_desugar_eval s =
    let (tyctx,_,e) = P.parseIn s A.emptyTyCtx
        (e',ty) = desugar tyctx emptyEnv e
        (v) = eval emptyEnv e'
    in (v,ty)



main :: IO ()
main = do
  args <- getArgs
  case args
    of [] -> usage
       args -> do mapM run args
                  return ()

run arg = do putStrLn $ "Running " ++ arg
             code <- readFile arg
             let (v,ty) = parse_desugar_eval code
             putStrLn $ "val it =  " ++ show (pp v) ++ " : " ++ show (pp ty)


usage =
  putStrLn $ "Usage: main <file>.tml ..."
