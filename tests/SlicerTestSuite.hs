module Main where

import           SlicerTestSuiteUtils ( runTMLTest )

import           Test.Tasty ( TestTree, defaultMain, testGroup )

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
    testGroup "Run TML files" (map runTMLTest
      [ "abs"
      , "copy-list"
      , "curried-componentwise-sum"
      , "curried-pointwise-sum"
      , "curried-pointwise-sum-two"
      , "example"
      , "exceptions"
      , "exceptions2"
      , "exceptions3"
      , "filter"
      , "foo"
      , "icfp17-example"
      , "icfp17-example2"
      , "map-increment-closed"
      , "map-increment"
      , "map"
      , "meanSquareDiff"
      , "meanSquare"
      , "mergesort"
      , "merge"
      , "operators"
      , "proportion"
      , "raise_inside"
      , "refs"
      , "refs-bslice"
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
      , "T2"
      , "T9"
      , "T13"
      , "T43"
      , "T47"
      , "T52"
      , "uncurried-componentwise-sum"
      , "while"
      , "while2"
      ] )
