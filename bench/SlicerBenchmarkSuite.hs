module Main (
    main
 ) where

import           Language.Slicer.Run

import           Control.DeepSeq
import           Control.Exception.Base
import           Criterion.Main
import           System.FilePath   ( pathSeparator )
import           System.Process    ( callCommand   )

main :: IO ()
main = mkBenchmarks >>= defaultMain >> cleanFiles

mkBenchmarks :: IO [Benchmark]
mkBenchmarks = do
  benchData <- preloadTMLFiles
  return [ bgroup "Slicer" (map mkBenchmark benchData) ]

mkBenchmark :: (FilePath, String) -> Benchmark
mkBenchmark (name, code) =
    bench name $ nfIO (runSlMIO (parseDesugarEval code))

preloadTMLFiles :: IO [(FilePath, String)]
preloadTMLFiles = do
  mapM (\path -> loadFile path >>= (\src -> return (path, src))) benchmarkFiles

loadFile :: FilePath -> IO String
loadFile path = do
  code <- readFile path
  evaluate (rnf code)
  return code

benchmarkFiles :: [FilePath]
benchmarkFiles = map (\file -> "examples" ++ [pathSeparator] ++ file ++ ".tml")
      [ "abs"
      , "array"
      , "array2"
      , "array3"
      , "copy-list"
      , "curried-componentwise-sum"
      , "curried-pointwise-sum"
      , "curried-pointwise-sum-two"
      , "example"
      , "exception_assign"
      , "exceptions"
      , "exceptions2"
      , "exceptions3"
      , "filter"
      , "foo"
      , "gauss"
      , "icfp17-example"
      , "icfp17-example2"
      , "map-increment-closed"
      , "map-increment"
      , "map"
      , "meanSquareDiff"
      , "meanSquare"
      , "mergesort"
      , "merge"
      , "newton"
      , "let-exception"
      , "operators"
      , "proportion"
      , "raise_inside"
      , "refs"
      , "refs-bslice"
      , "reverse-eval"
      , "reverse-slice"
      , "reverse"
      , "reverse-trace"
      , "simple-closure"
      , "sort-bug-2"
      , "sort-bug"
      , "sort-eval"
      , "sort-eval-trace-slice"
      , "sort-eval-trace"
      , "sort"
      , "sum-eval"
      , "sum-eval-trace-slice"
      , "sum-eval-trace"
      , "T2"
      , "T43"
      , "T47"
      , "T52"
      , "T56"
      , "T59"
      , "T62"
      , "uncurried-componentwise-sum"
      , "while"
      , "while2"
      , "while3"
      , "while4"
      ]

cleanFiles :: IO ()
cleanFiles = callCommand "rm -f *.pdf *.svg"
