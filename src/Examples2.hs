{-# LANGUAGE ViewPatterns, FlexibleInstances #-}

import Control.Arrow hiding ((<+>))
import Control.Monad
import Control.Exception

import Data.Maybe
import qualified Data.Map as Map
import Text.PrettyPrint

import Util
import LaTeX
import qualified Absyn as A
import UntypedParser
import Desugar
import Env
import Trace
import Eval
import Slice
import PrettyPrinting


data Test = Test {
   testName :: FilePath,
   runTest :: A.TyCtx -> Exp -> IO [Figure]
}

runAll :: IO ()
runAll = mapM_ run [
      test1,
      test2,
      test3,
      test4,
      test5,
      test6,
      test7,
      test10
   ]

-- Helper for parsing values (for populating test environments). Needed in
-- particular to build closures and partial applications, for which we have
-- no concrete syntax.
value :: A.TyCtx -> String -> Value
value tyCtx str = exp2val $ fst . desugar tyCtx emptyEnv $ parse_ tyCtx str

sourceCode :: Test -> IO String
sourceCode test =
   readFile $ testFolder ++ testName test ++ ".pml"

run :: Test -> IO ()
run test = do
   putStrLn $ "Starting test " ++ testName test ++ "."
   code <- sourceCode test
   let (tyCtx, gamma, e0) = parseIn code A.emptyTyCtx
       (e,ty) = desugar tyCtx (fmap desugarTy gamma) e0
   reports <- runTest test tyCtx e
   let reports' = flip (:) reports $ sourceFig code
   mapM_ (report $ testName test) $ zip reports' $ iterate (+1) 1
   putStrLn $ "Test " ++ testName test ++ " done."
   where
      labelPrefix = "example-" ++ testName test

assert_ :: Monad m => String -> Bool -> m ()
assert_ msg b = unless b $ error msg

-- Pair of a trace and a value. Useful for prettyprinting a trace alongside the value
-- it computes/pattern it was sliced with.
data Result =
   TraceResult (Env Value, Exp) Value |
   SliceResult (Env Value, Exp) Value

instance PP (A.TyCtx, Result) where
   pp_partial (tyCtx, TraceResult comp v) (eq tyCtx -> True, TraceResult comp' v') =
      pp_partial (tyCtx, comp) (tyCtx, comp') $$ text ">>" <+>
      (pp_partial (tyCtx, val2exp v) (tyCtx, val2exp v'))
   pp_partial (tyCtx, SliceResult comp v) (eq tyCtx -> True, SliceResult comp' v') =
      pp_partial (tyCtx, comp) (tyCtx, comp') $$ text "<<" <+>
      (pp_partial (tyCtx, val2exp v) (tyCtx, val2exp v'))
   pp x = pp_partial x x

-- Some common figure arrangements.
data TwoFigs = SideBySide | Separate

sourceFig :: String -> Figure
sourceFig code =
   Figure NewFig "Original program" $ SingleFig $ Plain code

traceFig :: A.TyCtx -> Env Value -> Exp -> ((Value, Trace), Figure)
traceFig tyCtx env e =
   let (v, t) = trace env e in
   -- Traces are initially stable.
   assert (snd (trace env t) == t) $
   ((v, t), Figure NewFig "Initial trace" $ SingleFig (Pretty (tyCtx, TraceResult (env, t) v)))

sliceFig :: A.TyCtx -> Trace -> Value -> Figure
sliceFig tyCtx t p =
   let (u, env) = bslice p t
       -- TODO: would really like to be able to re-enable this assertion.
       -- (p', _) = trace env u
   -- assert (p == p') $
   in Figure NewFig "After slicing" $ SingleFig (Pretty (tyCtx, SliceResult (env, u) p))

-- TODO: there's some redundancy with sliceFig to factor out here.
traceVsSliceFig :: TwoFigs -> A.TyCtx -> Env Value -> Exp -> Maybe Value -> ((Trace, Env Value), [Figure])
traceVsSliceFig layout tyCtx env e p_opt =
   let (v, t) = trace env e
       p = if isJust p_opt then fromJust p_opt else v
       (u, env') = bslice p t
       -- TODO: would really like to be able to re-enable this assertion.
       -- (p', _) = trace env' u
   -- assert (p == p') $
   in ((u, env'), case layout of
      SideBySide ->
         [ Figure NewFig "Initial trace (left); after slicing (right)" $
           DoubleFig (Pretty (tyCtx, TraceResult (env, t) v))
                     (Pretty (tyCtx, SliceResult (env', u) p)) ]
      Separate ->
         [ Figure NewFig "Initial trace" $ SingleFig (Pretty (tyCtx, TraceResult (env, t) v)),
           Figure NewFig "After slicing" $ SingleFig (Pretty (tyCtx, SliceResult (env', u) p)) ]
      )

-- Curried function that picks out the first element of a pair.
test1 :: Test
test1 = Test
   "simple-closure" $
   \tyCtx e ->
      return [snd $ traceFig tyCtx emptyEnv e]

-- Copy a list of integers.
-- Picking out only the first element of the result means the nil branch of
-- the function is never used.
test2 :: Test
test2 = Test
   "copy-list" $
   \tyCtx e -> do
      let env = singletonEnv (V "x") $ value tyCtx "3"
      return $ snd $ traceVsSliceFig SideBySide tyCtx env e $ Just $ value tyCtx "Cons (3, _:intlist)"

-- Curried function calculating pointwise sum of two lists.
-- Again this shows that we never use the nil branch of the function because
-- we only look at the head of the result list.
test3 :: Test
test3 = Test
   "curried-pointwise-sum" $
   \tyCtx e -> do
      let env = updateEnv (singletonEnv (V "x") $ value tyCtx "3") (V "y") $ value tyCtx "2"
      return $ snd $ traceVsSliceFig SideBySide tyCtx env e $ Just $ value tyCtx "Cons (5, _:intlist)"

-- As test3, but show replay with a complete trace. Then backslice afterwards to
-- show different recursive uses of function.
test4 :: Test
test4 = Test
   "curried-pointwise-sum-two" $
   \tyCtx e -> do
      let env = updateEnv (singletonEnv (V "x") $ value tyCtx "3") (V "y") $ value tyCtx "2"
          ((_, t), fig2) = traceFig tyCtx env e
          env' = updateEnv env (V "x") $ value tyCtx "5"
          ((v, u), fig3) = traceFig tyCtx env' t
          fig4 = sliceFig tyCtx u v
      assert_ "Result is updated list" (v == value tyCtx "Cons(7, Cons (12, Nil))")
      return $ [fig2, fig3, fig4]

-- Component-wise sum of two pairs (curried).
test5 :: Test
test5 = Test
   "curried-componentwise-sum" $
   \tyCtx e ->
      return $ snd $ traceVsSliceFig SideBySide tyCtx emptyEnv e $ Just $ value tyCtx "(8, _:int)"

-- Component-wise sum of two pairs (uncurried).
test6 :: Test
test6 = Test
   "uncurried-componentwise-sum" $
   \tyCtx e ->
      return $ snd $ traceVsSliceFig SideBySide tyCtx emptyEnv e $ Just $ value tyCtx "(8, _:int)"

-- Pick out second element in a map of a function to a list. Previously this example
-- showed how you could use a slice to update a particular element in a list, but this
-- is no longer possible.
test7 :: Test
test7 = Test
   "map-increment" $
   \tyCtx e -> do
      let (_, t) = trace emptyEnv e
          u0 = value tyCtx "Cons (_:int, Cons (_:int, Cons (_:int, Nil)))"
          u1 = value tyCtx "Cons (_:int, Cons (8, Cons (_:int, Nil)))"
          (s0, _) = bslice u0 t
          (s1, _) = bslice u1 t
          e0 = uneval s0
          e1 = uneval s1
      return [Figure NewFig "Trace slice" $ DoubleFig (Pretty (tyCtx, s0))
                                                      (Pretty (tyCtx, s1)),
              Figure NewFig "Program slice" $ DoubleFig (Pretty (tyCtx, e0))
                                                        (Pretty (tyCtx, e1))]

-- Merge two sorted lists.
test10 :: Test
test10 = Test
   "merge" $
   \tyCtx e -> do
      -- 3 different slicing criteria that show the merge function being sliced in
      -- different ways.
      let v1 = value tyCtx "Cons (_:int, Cons (_:int, Cons (_:int, Cons (13, _:intlist))))"
          v2 = value tyCtx "Cons (_:int, Cons (6, _:intlist))"
          v3 = value tyCtx "Cons (_:int, Cons (_:int, Cons (_:int, Cons (_:int, _:intlist))))"
      do
         let ((_, t), _) = traceFig tyCtx emptyEnv e
             fig1 = sliceFig tyCtx t v1
             fig2 = sliceFig tyCtx t v2
             fig3 = sliceFig tyCtx t v3
         return [fig1, fig2, fig3]

-- Buggy merge sort.
test11 :: Test
test11 = Test
   "mergesort" $
   \tyCtx e -> do
      let (_, t) = trace emptyEnv e
          u0 = value tyCtx "Cons(_:int,Cons(_:int,Cons(_:int,Cons(_:int,Cons(_:int,Cons(_:int,Cons(_:int,Cons(_:int,Nil))))))))"
          u1 = value tyCtx "Cons(12,Cons(12,Cons(12,Cons(12,Cons(18,Cons(23,Cons(23,Cons(23,Nil))))))))"
          (e0, _) = pslice u0 t
          (e1, _) = pslice u1 t
      return [Figure NewFig "Program slice" $ DoubleFig (Pretty (tyCtx, e0))
                                                        (Pretty (tyCtx, e1))]
