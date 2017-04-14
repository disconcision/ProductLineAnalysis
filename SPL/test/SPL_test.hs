-- SPL unit tests
{-# LANGUAGE TemplateHaskell #-}

--import Test.QuickCheck
--import Test.QuickCheck.All
import SPL
import Prop
import Control.Applicative

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
x0 = mkVars [(-8, _pq), (0, _p_q), (-3, p_q), (7, pq)]

y :: Var Int
y = mkVars [(-11, _p)]
y0 = mkVars [(-11, _pq)]

z :: Var Int
z = mkVars [(6, p)]

-- exists
prop_exists1 = exists (Just 2, p_q) w 
prop_exists2 = exists (Just (-11), _pq) y
prop_exists3 = not (exists (Just 4,p_q) w)
prop_exists4 = not (exists (Just (-8), q) x)

-- ORD
prop_lt1 = y0 < y
prop_lt2 = not (y < y0)
prop_lt3 = not (x < x0)

abs' = pure abs

xAbs = abs' <*> x
yAbs = abs' <*> y


--(|+|) = liftV2 (+)

x_plus_y0 = apply (apply (pure (+)) x) y
x_plus_y1 = (pure (+)) <*> x <*> y
x_plus_y2 = x |+| y

safeDiv :: Int -> Int -> Int
safeDiv a b = if b == 0 then 0 else (div a b)
div' = liftV2 div

zero = (mkVarT 0)
one = (mkVarT 1)
 
safeDiv' :: Var Int -> Var Int -> Var Int
safeDiv' a b = cond' (b |==| zero) zero (div' a b)

--return []
--runTests = $verboseQuickCheckAll
--main = do runTests