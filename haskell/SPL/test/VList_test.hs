{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

import VList
import SPL
import PropBDD
import ShareVis


import Control.Monad.State.Lazy
import Data.Tuple

_p_, _q_, _r_, _s_ :: (String, Prop)
univ@[_p_, _q_, _r_, _s_] = mkUniverse ["P", "Q", "R", "S"]
p = snd _p_
q = snd _q_
r = snd _r_
s = snd _s_

pq = conj[p,q]
p_q = conj[p, neg q]
_pq = conj[neg p, q]
_p_q = conj[neg p, neg q]
_p = neg p

w :: Var Int
w = mkVars [(1, pq), (11, p_q), (111, _pq), (1111, _p_q)]
x = mkVars [(2, pq), (22, p_q), (222, _p)]
y = mkVars [(3, tt)]
z = mkVars [(4, p), (44, _p)]

l0 = vNil 
l1 = vCons w l0
l2 = vCons x l1
l3 = vCons y l2
l4 = vCons z l3

listBegin = mkVList[y, z, x, w]
listEnd = mkVList[w,x,z,y]
listMiddle = mkVList [x, y, z, w]


-- let's figure out these types. we know

-- type VList a = Var [a]
-- newtype Var t = Var [(Val t)]
-- type Val a = (a, PresenceCondition)
--  type PresenceCondition  = Prop

-- so: Var t = [(t, Prop)]
-- and: VList a = Var [a] = [([a], Prop)]

-- which means
-- vmap :: Var (a -> b) -> VList a -> VList b
-- Vmap :: [(a -> b, Prop)] -> [([a], Prop)] -> [([b], Prop)]
-- vmap = liftV2 map


vfoldl :: Var (a -> b -> a) -> Var a -> VList b -> Var a
vfoldl = liftV3 foldl

vfoldr :: Var (a -> b -> b) -> Var b -> VList a -> Var b
vfoldr = liftV3 foldr

varToList :: Var a -> [a]
varToList (Var []) = []
varToList (Var ((t,prop):xs)) = t : (varToList (Var xs)) 


countOps :: VList a -> Var (State Int Int)
countOps vl = vfoldr (mkVarT f) (mkVarT base) vl where
    base = (get >>= return) :: State Int Int
    f :: a -> (State Int Int) -> (State Int Int)
    f x state = do
        count <- get
        put (count+1)
        state


countAcrossVar :: VList a -> Int
countAcrossVar vl = sum(varToList vi)
    where vi = (liftV2 evalState) (countOps vl) (mkVarT 0)


graphVList (Var ls) = showGraph $ fmap (\(a,b)-> (show b,a)) ls


main = do
    graphVList l4
    --print $ vfoldr (mkVarT (+)) (mkVarT 0) l3
    print $ countAcrossVar l4
