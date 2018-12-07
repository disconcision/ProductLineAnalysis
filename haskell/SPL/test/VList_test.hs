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

la = mkVList [y,x,w]
lb = mkVList [z,y,x,w]

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
countOps vl = vfoldr (mkVarT f) base vl where
    base = mkVarT (get >>= return) :: Var (State Int Int)
    f :: a -> (State Int Int) -> (State Int Int)
    f x state = do
        count <- get
        put (count+1)
        state


countAcrossVar :: VList a -> Int
countAcrossVar vl = sum(varToList vi)
    where vi = (liftV2 evalState) (countOps vl) (mkVarT 0)


--instance (Show b) => MemMappable (Var b) where 
--    makeNode (Var []) = ("null", [])
--    makeNode (Var (((a,b)):xs)) = ((show a), [Var xs])


--[([a], Prop)]
instance (Show a) => MemMappable (VList a) where
    makeNode (Var []) = ("null", [])
    makeNode (Var (a:as)) = ((show a), [Var as])
    --    makeNode [] = ("null", [])
--    makeNode ((as, prop):xs) = ((show as), as)



aa = case l3 of Var ((a,b):xs) -> mapMemRaw a
bb = case l3 of Var (x:(a,b):xs) -> mapMemRaw a
cc = case l3 of Var (x:y:(a,b):xs) -> mapMemRaw a
dd = case l3 of Var (x:y:z:(a,b):[]) -> mapMemRaw a


graphVList ls = showGraph $ fmap (\(a,b)-> (show b,a)) $ case ls of Var x -> x


main = do
    graphVList l4
    --showGraph $ case (fmap (\a -> (show a, a)) l3) of Var x -> x
    --showGraphRaw $ case l2 of Var ls -> concatMap (\x -> case x of (a,b) -> mapMemRaw a) ls
    print $ case l3 of Var ((a,b):as) -> a
    print $ aa
    print $ bb
    print $ cc
    print $ dd
    print $ vfoldr (mkVarT (+)) (mkVarT 0) l3
    --showGraph[("l3", l3)]
    --showGraph [("w", w), ("x", x), ("y", y), ("z", z)]
    print $ countAcrossVar la
    print $ case w of
                Var xs -> xs
    print $ (liftV2 evalState) (countOps la) (mkVarT 0)
    print $ (liftV2 evalState) (countOps l3) (mkVarT 0)
    print $ vhead $ vtail l4

    --print $ (liftV2 evalState) (countOps listBegin) (mkVarT 0)
    --print $ (liftV2 evalState) (countOps listEnd) (mkVarT 0)
    --print $ (liftV2 evalState) (countOps listMiddle) (mkVarT 0)
 --   print $ (z :: Var Int)
    --print $ vmap (mkVarT (\ x -> x+1)) l3
    --print $ vhead l3
    --print $ vhead la
    --print $ vnull l3
 --   print $ vlength $ l4
 --   print $ z == (vhead l4)

    --print $ printVar w
    --print $ fmap (\ x -> x + 100) w
 --   print $ vmap (\ x -> x + 1) l0
    --print (l0 :: VList Int)

 --   print $ l2 |!!| 1
    --print $ vlength l2
