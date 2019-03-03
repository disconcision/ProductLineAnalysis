{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE BangPatterns #-}

import SPL
import PropBDD

-- note: top level app in rules cant have parens
-- rule3 : warning: Forall'd type variable ‘b’ is not bound in RULE lhs ?
-- rule2: it's a fallthrough - might be a showstopper
-- wait, how does this rule "know" if x occurs free in _A?
    -- is this going to compile-time error?

{-# RULES
"r1" forall vx. apply (mkVarT (\x -> x)) vx = vx
"r3" forall vx _A _B . apply (mkVarT (\ x -> (_A _B))) vx = (apply (apply (mkVarT (\ x -> _A)) vx) (apply (mkVarT (\ x -> _B)) vx))
"r3_2" forall vx _A _B . apply (mkVarT (\ x y -> (_A _B))) vx = (apply (apply (mkVarT (\ x y -> _A)) vx) (apply (mkVarT (\ x y -> _B)) vx))
"r2" forall vx _A . apply (mkVarT (\x -> _A)) vx = (mkVarT _A)

#-}

{-# NOINLINE foo #-}
{-# NOINLINE bar #-}

_p_, _q_ :: (String, Prop)
univ@[_p_, _q_] = mkUniverse ["P", "Q"]
p = snd _p_
q = snd _q_

pq = conj[p,q]
p_q = conj[p, neg q]
_pq = conj[neg p, q]
_p_q = conj[neg p, neg q]
_p = neg p


foo a = 1
bar b = 1
vbaz = mkVarT (\a b -> ((+) (foo a) (foo b)))
va = mkVars [(1, pq), (2, p_q), (3, _pq), (4, _p_q)]
vb = mkVars [(1, tt)]


main = do
    print $ apply (apply (mkVarT (\a b -> ((+) (foo a) (foo b)))) va) vb