module Compact where

import Trace
import TraceTree
import Util

-- idea: represent trace as a string of choices relative to its expression.
-- parse traces to and from streams of choices.



data Choice = CTrue | CFalse | CInL | CInR | CClosure Code | CHole
            deriving (Eq,Show)
type CompactTrace = [Choice]



unparse :: Trace -> CompactTrace
unparse (Var x')  = []
unparse (Let x' t1 t2)
    = unparse t1 ++ unparse t2
unparse Unit = []
unparse (CBool b') = []
unparse (IfThen t _ _ t1) = [CTrue] ++ unparse t ++ unparse t1
unparse (IfElse t _ _ t2) = [CFalse] ++ unparse t ++ unparse t2
unparse (CInt i') = []
unparse (Op f' ts)
    = concat (map unparse ts)
unparse (Pair t1 t2)
    = unparse t1 ++ unparse t2
unparse (Fst t) = unparse t
unparse (Snd t) = unparse t
unparse (InL t) = unparse t
unparse (InR t) = unparse t
unparse (CaseL t m x t1)
    = [CInL] ++ unparse t ++ unparse t1
unparse (CaseR t m y' t2)
    = [CInR] ++ unparse t ++ unparse t2
unparse (Fun k') = []
unparse (Call t1 t2 k t)
    = [CClosure k] ++ unparse t1 ++ unparse t2 ++ unparse (body t)
unparse (Roll _ t) = unparse t
unparse (Unroll _ t) = unparse t
unparse t = error ( show t)


parse :: Exp -> P CompactTrace Trace
parse (Var x) = return (Var x)
parse (Let x e1 e2)  = do t1 <- parse e1
                          t2 <- parse e2
                          return (Let x t1 t2)
parse Unit = return Unit
parse (CBool b) = return (CBool b)
parse (If e e1 e2)
    = do c <- fetch
         case c of CTrue -> do t <- parse e
                               t1 <- parse e1
                               return (IfThen t e1 e2 t1)
                   CFalse -> do t <- parse e
                                t2 <- parse e2
                                return (IfElse t e1 e2 t2)
parse (CInt i) = return (CInt i)
parse (Op f es) = do ts <- mapM parse es
                     return (Op f ts)
parse (Pair e1 e2) = do t1 <- parse e1
                        t2 <- parse e2
                        return (Pair t1 t2)
parse (Fst e) = do t <- parse e
                   return (Fst t)
parse (Snd e) = do t <- parse e
                   return (Snd t)
parse (InL e) = do t <- parse e
                   return (InL t)
parse (InR e) = do t <- parse e
                   return (InR t)
parse (Case e m)
    = let (Match (x,e1) (y,e2)) = m
      in do c <- fetch
            case c of CInL -> do t <- parse e
                                 t1 <- parse e1
                                 return (CaseL t m x t1)
                      CInR -> do t <- parse e
                                 t2 <- parse e2
                                 return (CaseR t m y t2)
parse (Fun k) = return (Fun k)
parse (App e1 e2)
    = do CClosure k <- fetch
         t1 <- parse e1
         t2 <- parse e2
         t <- parse (body k)
         return (Call t1 t2 k (Rec (fn k) (arg k) t Nothing))
parse (Roll tv e) = do t <- parse e
                       return (Roll tv t)
parse (Unroll tv e) = do t <- parse e
                         return (Unroll tv t)

parse' :: Exp -> CompactTrace -> Trace
parse' e cs = let P f = parse e
                  (t,[]) = f cs
              in t
