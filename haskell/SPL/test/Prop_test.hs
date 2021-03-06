-- Propositional Logic and SAT solving Tests
-- Ramy Shahin
-- Jan 3rd 2017
import Prop

import GHC.Arr

u :: Universe
u = mkUniverse ["P", "Q", "R", "S"]

p, q, r, s :: Prop
p = Atom u 0
q = Atom u 1
r = Atom u 2
s = Atom u 3

prop1 = conj [p, (neg q)]   -- sat
prop2 = disj [(neg r), s]   -- sat
prop3 = conj [p, (neg p)]   -- unsat
prop4 = disj [r]            -- sat
prop5 = conj [F, p, q]      -- unsat
prop6 = disj [T, prop1, prop3] -- sat
prop7 = impl p (neg p)      -- sat
prop8 = iff  p (neg p)      -- unsat
prop9 = impl p q            -- sat
prop10 = iff p q            -- sat

props = [prop1, prop2, prop3, prop4, prop5, prop6, prop7, prop8, prop9, prop10]

run :: IO ()
run = mapM_ (\p -> do
                    let r = checkSAT p
                    putStrLn ((show p) ++ "------>" ++ (show r))
            ) props

