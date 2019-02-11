{-# LANGUAGE TemplateHaskell #-}
import Control.Monad
import Language.Haskell.TH
--import Language.Haskell.TH.Utils


a0 :: Q Exp
-- ListE [LitE (IntegerL 0)]
a0 = [| [0] |]

a1 :: Q Exp
a1 =  [| length [] |]

a2 :: Q Exp
a2 =  [|foldr (const ((+) 1)) 0 ls|]

a3 :: Q [Dec]
a3 =  [d|sLength1 ls = foldr (const ((+) 1)) 0 ls|]



f :: Exp -> Exp
f (ListE [LitE (IntegerL a)]) = (ListE [LitE (IntegerL (a + 10))])

b :: IO Exp
b = runQ a0
--x = length

main = do x <- runQ a0 ; return (f x)