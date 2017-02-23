module Main where

import           SlicerTestSuiteUtils ( runTMLTest )

import           Test.Tasty ( TestTree, defaultMain, testGroup )

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
    testGroup "Run TML files"
      [ runTMLTest "abs"
      , runTMLTest "copy-list"
      , runTMLTest "curried-componentwise-sum"
      , runTMLTest "curried-pointwise-sum"
      , runTMLTest "curried-pointwise-sum-two"
      , runTMLTest "example"
      , runTMLTest "exceptions"
      , runTMLTest "exceptions2"
      , runTMLTest "exceptions3"
      , runTMLTest "filter"
      , runTMLTest "foo"
      , runTMLTest "icfp17-example"
      , runTMLTest "icfp17-example2"
      , runTMLTest "map-increment-closed"
      , runTMLTest "map-increment"
      , runTMLTest "map"
      , runTMLTest "meanSquareDiff"
      , runTMLTest "meanSquare"
      , runTMLTest "mergesort"
      , runTMLTest "merge"
      , runTMLTest "operators"
      , runTMLTest "proportion"
      , runTMLTest "raise_inside"
      , runTMLTest "refs"
      , runTMLTest "refs-bslice"
      , runTMLTest "reverse-eval"
      , runTMLTest "reverse-slice-profile2"
      , runTMLTest "reverse-slice-profile"
      , runTMLTest "reverse-slice-size"
      , runTMLTest "reverse-slice"
      , runTMLTest "reverse"
      , runTMLTest "reverse-trace-profile2"
      , runTMLTest "reverse-trace-profile"
      , runTMLTest "reverse-trace"
      , runTMLTest "simple-closure"
      , runTMLTest "sort-bug-2"
      , runTMLTest "sort-bug"
      , runTMLTest "sort-eval"
      , runTMLTest "sort-eval-trace-profile2"
      , runTMLTest "sort-eval-trace-profile"
      , runTMLTest "sort-eval-trace-slice-profile2"
      , runTMLTest "sort-eval-trace-slice-profile"
      , runTMLTest "sort-eval-trace-slice"
      , runTMLTest "sort-eval-trace"
      , runTMLTest "sort-slice-size"
      , runTMLTest "sort"
      , runTMLTest "sum-eval-profile"
      , runTMLTest "sum-eval"
      , runTMLTest "sum-eval-trace-profile2"
      , runTMLTest "sum-eval-trace-profile"
      , runTMLTest "sum-eval-trace-size"
      , runTMLTest "sum-eval-trace-slice-profile2"
      , runTMLTest "sum-eval-trace-slice-profile"
      , runTMLTest "sum-eval-trace-slice"
      , runTMLTest "sum-eval-trace"
      , runTMLTest "sum-slice-size"
      , runTMLTest "T2"
      , runTMLTest "T9"
      , runTMLTest "T13"
      , runTMLTest "T43"
      , runTMLTest "uncurried-componentwise-sum"
      ]
