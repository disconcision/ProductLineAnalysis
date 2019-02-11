{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE BangPatterns #-}

import VList
import SPL
import PropBDD
import ShareVis


import Control.Monad.State.Lazy
import Data.Tuple
import Data.List

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
z = mkVars [(0, p), (10, _p)]
z1 = mkVars [(1, p), (11, _p)]
y = mkVars [(0, tt)]
y1 = mkVars [(1, tt)]
y2 = mkVars [(2, tt)]
y3 = mkVars [(3, tt)]
y4 = mkVars [(4, tt)]


l0 = vNil 
l1 = vCons w l0
l2 = vCons x l1
l3 = vCons y l2
l4 = vCons z l3

listEnd = mkVList[y,y1,y2,y3] --4 (regardless of compaction)
listEnd2 = mkVList[w,y,y1,y2] --7
listEnd3 = mkVList[w,x,y1,y2] --9
listEnd4 = mkVList[w,x,z,y1]  --10
listEnd5 = mkVList[w,x,z,z1]  --11

listBegin = mkVList[y, y, y, w]  --16

listMiddle = mkVList [x, y, z, w]




-- TYPE FIGURING

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



-- FOLD LIFTING

-- cond' :: Show a => Var Bool -> Var a -> Var a -> Var a
-- vhead :: VList a -> Var a 
-- vtail :: VList a -> VList a 
-- vnull :: VList a -> Var Bool

vfoldrShallow :: Var (a -> b -> b) -> Var b -> Var [a] -> Var b
vfoldrShallow = liftV3 foldr

sFoldr :: (a -> b -> b) -> b -> [a] -> b
sFoldr f init ls = if null ls
    then init
    else f (head ls) (sFoldr f init (tail ls))

vfoldr :: Show b => Var (a -> b -> b) -> Var b -> Var [a] -> Var b
vfoldr f init ls = cond' (vnull ls)
    init
    $ f <*> vhead ls <*> vfoldr f init (vtail ls)

    -- because cond' <= Show
instance Show (State a b) where
    show _ = "" -- (StateT f)

vLength0 :: Var [a] -> Var Int 
vLength0 = liftV length

sLength1 :: [a] -> Int
sLength1 ls = if (null ls) then 0 else ((+) 1 (sLength1 (tail ls)))

vLength1 :: Var [a] -> Var Int    
vLength1 vl = cond' (vnull vl) (mkVarT 0) ((liftV2 (+)) (mkVarT 1) (vLength1 (vtail vl)))
-- vLength0 vl = cond' (vnull vl) (mkVarT 0) (fmap (+) (mkVarT 1) <*> (vLength0 (vtail vl)))


sLength2 :: [a] -> Int
sLength2 ls = foldr (const ((+) 1)) 0 ls
-- sLength1 ls = foldr (\x y -> (+) y 1) 0 ls

vLength2 :: Show a => Var [a] -> Var Int
vLength2 vl = vfoldr (mkVarT (\ x -> (+) 1)) (mkVarT 0) vl




vMap0 :: Show b => Var (a -> b) -> Var [a] -> Var [b]
vMap0 = liftV2 map

sMap0 :: (a -> b) -> [a] -> [b]
sMap0 f ls = if null ls
    then []
    else (:) (f (head ls)) (sMap0 f (tail ls))

vMap1 :: Show b => Var (a -> b) -> Var [a] -> Var [b] -- VList a == Var [a]
vMap1 f vl = cond' (vnull vl)
    (mkVarT [])
    $ (vCons ((<*>) f (vhead vl))) (vMap1 f (vtail vl))


sMap1 :: (a -> b) -> [a] -> [b]
sMap1 f ls = foldr (\x y -> (:) (f x) y) [] ls


-- implemented with (deep) vfoldr
vMap2 :: Show b => Var (a -> b) -> Var [a] -> Var [b]
vMap2 f vl = vfoldr new_f (mkVarT []) vl
        where
            new_f = liftV (\vf -> (\ x y -> (:) (vf x) y)) f

-- do we actually want deep lifting to lift function args?
-- this presents issues like above



-- things which are problematic for rewriting
-- assume no extant lifting?
-- special syntax:
-- ifs
-- guards
-- pattern matching



-- write length

-- OP COUNTING

varToList :: Var a -> [a]
varToList (Var []) = []
varToList (Var ((t,prop):xs)) = t : (varToList (Var xs)) 


vCounter :: Show a => VList a -> Int
vCounter vls = if null (head $ varToList vls)
    then 0 else length (varToList (vhead vls)) + vCounter (vtail vls)
  


{-
vCount2 :: Show a => VList a -> Int
vCount2 vls = vfoldr f init vls
    where init
  -}          


-- MISC

getNames :: VList a -> Var [Int]
getNames vl = vfoldr (mkVarT f) (mkVarT []) vl
        where
            f x names = (getName x) : names


graphVList (Var ls) = showGraph $ fmap (\(a,b)-> (show b,a)) ls



testfn0 x = 5+x
testfn1 x = 5+x
testfn2 x = 5+x
-- note: belows registers 0 entries under main; ??
--testfn = (+) 1 

listN = mkVList[w,w,w,w,w,w,w,w,w,w] -- 40 distinct
listE = mkVList[w,w,w,w,w,y,y,y,y,y] -- 4*5+5=25 distinct 
listB = mkVList[y,y,y,y,y,w,w,w,w,w] -- 25 distinct
listM = mkVList[w,w,w,y,y,y,y,w,w,w] -- 6*4+4=28 distinct

-- vMap0 - shallow lift
-- vMap1 - deep lifted recursive
-- vMap2 - deep lifted vfoldr (itself deep lifted)


-- results (num calls to testfnX)
--       vMap0 vMap1 vMap2
-- listN    40    40    40
-- listE    40    25    25
-- listB    40    25    40
-- listM    40    28    40

-- above: note that resulting lists are correct


-- results (num variations in length)
--       vLength0 vLength1 vLength2
-- listN        4        1        4
-- listE        4        1        4
-- listB        4        1        2
-- listM        3        1        3

main = do

    print $ vLength0 listM
    print $ vLength1 listM 
    print $ vLength2 listM

    print $ vMap0 (mkVarT testfn0) listE
    print $ vMap1 (mkVarT testfn1) listE
    print $ vMap2 (mkVarT testfn2) listE

    --graphVList $ listEnd2

    --print $ vLength1 listEnd

    --print listEnd
    --print $ (vMap0 (mkVarT ((+)10)) listBegin)

    --print $ vCounter listEnd
    --print $ vCounter listEnd2
    --print $ vCounter listEnd3
    --print $ vCounter listEnd4
    --print $ vCounter listEnd5
    --print $ vCounter listBegin

    --print $ getNames listEnd
    --print $ case listEnd of Var ls -> fmap (\(a,b)-> (show b,a)) ls
    
    
    
    --print $ vfoldr (mkVarT (+)) (mkVarT 0) l3
  
