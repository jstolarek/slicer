module Main where

import           Absyn         ( emptyTyCtx  )
import           Trace         ( Value, Type )
import           Desugar
import           Env
import           Eval
import           UntypedParser ( parseIn     )
import           Util

import           System.Environment


parse_desugar_eval :: String -> (Value, Type)
parse_desugar_eval s =
    let (tyctx, _, e) = parseIn s emptyTyCtx
        (e', ty)      = desugar tyctx emptyEnv e
        v             = eval emptyEnv e'
    in (v, ty)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> usage
    _  -> mapM_ run args

run :: String -> IO ()
run arg = do
  putStrLn $ "Running " ++ arg
  code <- readFile arg
  let (v,ty) = parse_desugar_eval code
  putStrLn $ "val it =  " ++ show (pp v) ++ " : " ++ show (pp ty)

usage :: IO ()
usage = putStrLn $ "Usage: slicer <file>.pml ..."
