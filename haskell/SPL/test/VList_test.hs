import VList
import SPL
import PropBDD


import Control.Monad.State.Lazy


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
w = mkVars [(12, pq), (2, p_q), (0, _pq), (3, _p_q)]

x :: Var Int
x = mkVars [(7, pq), (-3, p_q), (-8, _pq), (0, _p_q)]

y :: Var Int
y = mkVars [(-11, _p), (3, p)]

z :: Var Int
z = mkVars [(6, p), (2, _p)]

l0 = vNil 
l1 = vCons w l0
l2 = vCons x l1
l3 = vCons y l2
l4 = vCons z l3

la = mkVList [y,x,w]
lb = mkVList [z,y,x,w]

printVar :: Show a => Var a -> String
printVar (Var xs) = foldl (\ acc x -> case x of (v, pc) -> " v: " ++ (show v) ++ " pc: " ++ (show pc)) "" xs


prettyPrint :: Show a => VList a -> String
prettyPrint (Var x) = show x
prettyPrint _ = "?"

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

{-
mnMap :: (a -> a) -> VList a -> VList a
mnMap f vl = let temp = vnull vl
                 g = (\x ->
                        if x
                          then vl
                          else vCons (fmap f $ vhead vl) (mnMap f (vtail vl)))
                in fmap g temp 
-}


--apply (Var fn) x = --compact $
--     unions [apply_ f x | f <- fn] 

-- expected type ‘Var (a0 -> b0)’ : [(a0 -> b0, Prop)]



--instance (Show a) => MemMappable (Btree a) where
--    makeNode (Leaf x) = ((show x), [])
--    makeNode (Node x y z) = ((show x), [y, z])
--t0 = Node "woo" (Node "bzz" (Leaf "yaa") (Leaf "boi")) (Leaf "yum")
--main = do showGraph [("t0", t0)]

--instance (Show a) => MemMappable (VList a) where
--    makeNode [] = ("null", [])
--    makeNode (x:xs) = ((show x), [xs]) 
--t0 = Node "woo" (Node "bzz" (Leaf "yaa") (Leaf "boi")) (Leaf "yum")
--main = do showGraph [("t0", t0)]


vfoldl :: Var (a -> b -> a) -> Var a -> VList b -> Var a
vfoldl = liftV3 foldl

vfoldr :: Var (a -> b -> b) -> Var b -> VList a -> Var b
vfoldr = liftV3 foldr


base :: Var (State Int Int)
base = mkVarT (get >>= return)

countOps :: VList a -> Var (State Int Int)
countOps vl = vfoldr (mkVarT f) base vl where
    f :: a -> (State Int Int) -> (State Int Int)
    f x y = do
        count <- get
        put (count+1)
        y


varToList :: Var a -> [a]
varToList (Var []) = []
varToList (Var ((t,prop):xs)) = t : (varToList (Var xs)) 

countAcrossVar :: VList a -> Int
countAcrossVar vl = sum(varToList vi)
    where vi = (liftV2 evalState) (countOps vl) (mkVarT 0)


main = do
    print $ countAcrossVar l3
    print $ (liftV2 evalState) (countOps l3) (mkVarT 0)
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
