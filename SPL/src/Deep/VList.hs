module Deep.VList where

import SPL
import Prop -- for testing

data List a =
    NIL 
  | Cons a (List a)

data VList' a =
    VNil'
  | VCons' a (VList a)
  deriving Show
  
type VList a = Var (VList' a)

vNil = mkVarT VNil'

vCons :: Var a -> VList a -> VList a 
vCons x xs = (liftV2 VCons') x (mkVarT xs)

-- test
u :: Universe
u = mkUniverse ["P", "Q", "R", "S"]

p, q, r, s :: Prop
p = Atom u 0
q = Atom u 1
r = Atom u 2
s = Atom u 3

pq = conj[p,q]
p_q = conj[p, neg q]
_pq = conj[neg p, q]
_p_q = conj[neg p, neg q]
_p = neg p

w :: Var Int
w = mkVars [(12, pq), (2, p_q), (3, _p_q)]

x :: Var Int
x = mkVars [(7, pq), (-3, p_q), (-8, _pq), (0, _p_q)]

y :: Var Int
y = mkVars [(-11, _p)]

z :: Var Int
z = mkVars [(6, p)]