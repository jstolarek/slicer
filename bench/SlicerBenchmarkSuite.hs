module Main (
    main
 ) where

import           Language.Slicer.API

import           Control.DeepSeq
import           Control.Exception.Base
import           Criterion.Main
import           System.FilePath   ( pathSeparator )
import           System.IO         ( readFile      )
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
    , "copy-list"
    , "curried-componentwise-sum"
    , "curried-pointwise-sum"
    , "curried-pointwise-sum-two"
    , "example"
    , "exceptions"
    , "filter"
    , "foo"
    , "map-increment-closed"
    , "map-increment"
    , "map"
    , "meanSquareDiff"
    , "meanSquare"
    , "mergesort"
    , "merge"
    , "operators"
    , "proportion"
    , "refs"
    , "reverse-eval"
    , "reverse-slice-profile2"
    , "reverse-slice-profile"
    , "reverse-slice-size"
    , "reverse-slice"
    , "reverse"
    , "reverse-trace-profile2"
    , "reverse-trace-profile"
    , "reverse-trace"
    , "simple-closure"
    , "sort-bug-2"
    , "sort-bug"
    , "sort-eval"
    , "sort-eval-trace-profile2"
    , "sort-eval-trace-profile"
    , "sort-eval-trace-slice-profile2"
    , "sort-eval-trace-slice-profile"
    , "sort-eval-trace-slice"
    , "sort-eval-trace"
    , "sort-slice-size"
    , "sort"
    , "sum-eval-profile"
    , "sum-eval"
    , "sum-eval-trace-profile2"
    , "sum-eval-trace-profile"
    , "sum-eval-trace-size"
    , "sum-eval-trace-slice-profile2"
    , "sum-eval-trace-slice-profile"
    , "sum-eval-trace-slice"
    , "sum-eval-trace"
    , "sum-slice-size"
    , "T13"
    , "T2"
    , "T9"
    , "uncurried-componentwise-sum"
    ]

cleanFiles :: IO ()
cleanFiles = callCommand "rm -f *.pdf *.svg"
