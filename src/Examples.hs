{-# LANGUAGE FlexibleInstances #-}

import Trace
import TraceGraph
import Eval
import Slice
import Annot
import Compact
import LowerSemiLattice
import Env
import Profile
import UntypedParser
import Desugar
import qualified UntypedParser as P
import qualified Absyn as A



-- examples

vx =  (V "x")
vy =  (V "y")
vf =  (V "f")
vl =  (V "l")
vt =  (V "t")
vfact =  (V "fact")
vlist =  (V "list")
vmap =  (V "map")
vfilter = (V "filter")

fact = Fun (Rec vfact vx
            (If (Op opIntEq [Var vx, (CInt 0)]) 
                (--then
                 (CInt 1)
                 )
                (--else 
                 (Op opTimes [Var vx, App (Var vfact) (Op opMinus [Var vx, (CInt 1)])])
                )
            )
            (Just "fact")
           )

e1 = (Pair (App fact (Var vx)) (CInt 1))

(v1,t1) = trace (Env [(V "x", VInt 5)]) e1

ifthenelse = If (Op opIntEq [Var vx, CInt 42]) 
                (--then
                 (CBool True)
                 )
                (--else 
                 (CBool False)
                )

e2 = ifthenelse

(v2,t2) = trace (Env [(V "x", VInt 5)]) e2

tv_intlist = TV "intlist"

tyCtx = A.addTyDecl A.emptyTyCtx $ 
        A.TyDecl tv_intlist $ [(A.C "Nil", [A.UnitTy]), (A.C "Cons", [A.IntTy, A.TyVar tv_intlist])]

instance Valuable [Int] where
    to_val [] = VRoll (Just tv_intlist) (VInL VUnit)
    to_val (v:vs) = VRoll (Just tv_intlist) (VInR (VPair (to_val v) (to_val vs)))
    from_val (VRoll (Just tv_intlist) (VInL VUnit)) = []
    from_val (VRoll (Just tv_intlist) (VInR (VPair v vs))) = from_val v:from_val vs

nil_list = Roll (Just tv_intlist) (InL Unit)
nil_list_v = VRoll (Just tv_intlist) (VInL VUnit)

cons_list x xs = Roll (Just tv_intlist) (InR (Pair x xs))
cons_list_v x xs = VRoll (Just tv_intlist) (VInR (VPair x xs))

case_list l nil cons = Case (Unroll (Just tv_intlist) l)
                            (Match (bot, nil)
                                   (vlist, cons (Fst (Var vlist)) (Snd (Var vlist))))

apps f es = foldl (\head e -> App head e) f es

map_list = Fun (Rec bot vf
                (Fun (Rec vmap vx 
                      (case_list (Var vx) 
                                nil_list 
                                (\x xs ->  
                                 cons_list (App (Var vf) x)
                                           (apps (Var vmap) [xs]))) 
                     (Just "_map")))
               (Just "map"))

filter_list = Fun (Rec bot vf
                   (Fun (Rec vfilter vx 
                      (case_list (Var vx) 
                                nil_list 
                                (\x xs ->  
                                 If (App (Var vf) x)
                                    (cons_list x (App (Var vfilter) xs))
                                    (App (Var vfilter) xs)))
                     (Just "filter")))
               (Just "_filter"))


ifsquare = (Fun (Rec bot vx (If (Op opIntEq [Var vx,CInt 3]) (Var vx) 
                               (Op opTimes [Var vx,Var vx])) (Just "ifsquare")))
ifthree = (Fun (Rec bot vx (Op opIntEq [Var vx,CInt 3]) (Just "ifthree")))

e3 =  (Let vl (val2exp (to_val [1,2,3,4,5::Int])) (Let vmap map_list (App (App (Var vmap) ifsquare) (Var vl))))

env3 = (Env [(vl, to_val ([1,2,3,4,5]:: [Int]))])

(v3,t3) = trace env3 e3

p3 = cons_list_v VHole (cons_list_v VHole (cons_list_v VStar VHole))
p3' = cons_list_v VHole (cons_list_v VHole (cons_list_v VHole VHole))
p3'' = cons_list_v VHole (cons_list_v VStar VHole)

(t3',rho3) = bslice p3 t3
e3' =  (uneval t3') 
(t3'',_) = bslice_naive p3 t3  
e3'' =  (uneval t3'') 
(e3''',_) = bslice' p3 t3  
(t3'''',_) = bslice_naive p3' t3
(e3'''',_) = bslice' p3' t3

(t3a,_) = bslice_naive p3 t3
(t3b,_) = bslice_naive p3'' t3

e4 =   Let vl (val2exp (to_val [1,2,3,4,5,3::Int])) (Let vfilter filter_list (App (App (Var vfilter) ifthree) (Var vl)))
env4 = (Env [(vl, to_val ([1,2,3,4,5,3]:: [Int]))])
(v4,t4) = trace env4 e4

p4 = cons_list_v VHole (cons_list_v VStar VHole)
p4' =  cons_list_v VStar VHole

(t4',rho4) = bslice p4 t4
e4' =  (uneval t4') 
(t4'',_) = bslice_naive p4 t4  
e4'' =  (uneval t4'') 
(t4''',_) = bslice' p4 t4  
e4''' =  (uneval t4''') 

(t4a,_) = bslice_naive p4 t4
(t4b,_) = bslice_naive p4' t4

e5 = Let vt (Trace e4) (Op opVal  [Op opReplay [TraceUpd (Var vt) vl e3]])


(v5,t5) = trace env4 e5


e6 = Let vt (Trace e4) ( Pair(Op opVal [Var vt])( Op opVal [Op opSlice [Var vt,Op opVal [Var vt]]]))


(v6,t6) = trace env4 e6






parse_desugar_eval :: String -> (Value)
parse_desugar_eval s = 
    let (tyctx,_,e) = P.parseIn s A.emptyTyCtx
        (e',ty) = desugar tyctx emptyEnv e
        (v) = eval emptyEnv e'
    in v


