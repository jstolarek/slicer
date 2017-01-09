module Util where

import Text.PrettyPrint

newtype P s a = P {unP :: s -> (a,s)}

instance Monad (P s) where
    return a = P (\s -> (a,s))
    (P x) >>= f = P (\s -> let (a,s') = x s in unP (f a) s')

fetch :: P [a] a
fetch = P (\(x:xs) -> (x,xs))


class PP a where
    pp :: a -> Doc
    pp a = pp_partial a a
    pp_partial :: a -> a -> Doc

sb x =  brackets (text "|" <> x <> text "|")

-- Assert that y == x. For use as a view pattern.
eq :: (Eq a, Show a) => a -> a -> Bool
eq x y = if x == y then True else error $ "Found " ++ show y ++ ", expected "++ show x
