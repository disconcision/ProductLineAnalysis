import System.IO
import System.Environment
import Control.Monad
import Data.List (nub)
import Data.Maybe (fromJust)
import Data.List.Split 
import Text.Parsec
import Text.Parsec.String (Parser)

import SPL
import PropBDD
import Shallow.VList

-- 1. token preprocessor
-- I use typechef to dump token info to a file
-- which is sanitized via the code below:

stringToLists :: String -> [[String]]
stringToLists = filter ((/=) [""]). map (splitOn "\t") . splitOn "\n"

listToTuple :: [String] -> (Bool, String, String, String, (Int, Int), PC)
listToTuple [_, type', lang, text, val, line, col, feat] =
    (lang', type', text, val, loc, feat')
    where
        loc = (read line, read col)
        lang' = if lang == "true" then True else False        
        Right feat' = (regularParse _pc feat)
        
stripRedundantFields :: (Bool, String, String, String, (Int, Int), PC) -> (String, String, (Int, Int), PC) 
stripRedundantFields (_, type', text, val, loc, feat)  = (type', text, loc, feat) 

preprocessor :: String -> [(String, String, (Int, Int), PC)]
preprocessor x = map stripRedundantFields . (filter (\(b,_,_,_,_,_) -> b)) . map listToTuple . stringToLists $ x


-- 2. features parsing
-- ref: http://jakewheat.github.io/intro_to_parsing/
-- todo: this is super wordy; refactor to applicative-style

data PC = TT | FF | Feature String | Not PC | And [PC] | Or [PC]
    deriving Show

_pc :: Parser PC
_pc = choice [ (try _and <|> _or), _def, _true, _false, _not]


_true :: Parser PC
_true = do
    void $ string "True"
    return $ TT

_false :: Parser PC
_false = do
    void $ string "False"
    return $ FF    

_def :: Parser PC
_def = do
    void $ string "def"
    void $ char '('
    e <- many1 letter
    void $ char ')'
    return $ Feature $  e

_not :: Parser PC
_not = do
    void $ char '!'
    a <- _pc
    return $ Not a

_and :: Parser PC
_and = do
    void $ char '('
    a <- _pc
    b <- many1 (do
        void $ char '&'
        c <- _pc
        return c)
    void $ char ')'
    return $ And $ a : b

_or :: Parser PC
_or = do
    void $ char '('
    a <- _pc
    b <- many1 (do
        void $ char '|'
        c <- _pc
        return c)
    void $ char ')'
    return $ Or $ a : b


regularParse :: Parser a -> String -> Either ParseError a
regularParse p = parse p ""


{- TODO: make these into tests:

    print $ regularParse _def "def(AB)"
    print $ regularParse _and "(True&def(A))"
    print $ regularParse _pc "(def(C)&!def(B))"
    print $ regularParse _pc "(def(C)&def(B)&def(C))"
    print $ regularParse _pc "(def(C)&!def(B)&def(B)&def(C))"
    print $ regularParse _pc "(def(C)&(def(B)&def(C)))"
    print $ regularParse _pc "(def(C)|def(D))"
    print $ regularParse _pc "(def(C)&!def(B)&(def(B)|def(C)))"
    print $ regularParse _pc "(!def(B)&!def(C)&(!def(C)|def(B)|(!def(B)&!def(C))))"
-}


-- 3. feature extraction

collectFromTokens :: [(String, String, (Int, Int), PC)] -> [String]
collectFromTokens tokens =
    nub $ concatMap (\(_,_,_,pc) -> collectFromPC pc) tokens
    where
        collectFromPC :: PC -> [String]
        collectFromPC pc = case pc of
            TT -> []
            FF -> []
            Feature f -> [f]
            Not pc0 -> collectFromPC pc0
            And pcs -> concatMap collectFromPC pcs
            Or pcs -> concatMap collectFromPC pcs


-- 4. make universe, process PCs to BDD PCs
 
convertPCsToBDD :: Universe -> [(String, String, (Int, Int), PC)] -> [(String, String, (Int, Int), Prop)]
convertPCsToBDD universe toks = map (\(a,b,c,pc) -> (a,b,c,convertPCtoBDD pc)) toks
    where
        --universe = mkUniverse $ collectFromTokens toks
        convertPCtoBDD :: PC -> Prop
        convertPCtoBDD pc = case pc of
            TT -> tt
            FF -> ff
            Feature f -> fromJust $ lookup f universe
            Not pc -> neg $ convertPCtoBDD pc
            And pcs -> conj $ map convertPCtoBDD pcs
            Or pcs -> disj $ map convertPCtoBDD pcs  


-- 5. make VList from token list

makeVList :: [(String, String, (Int, Int), Prop)] -> VList (String, String, (Int, Int))
makeVList = foldr f vNil
    where
        skipToken = ("SKIP", "SKIP", (0,0)) -- a 'blank' token
        f t@(a, b, c, pc) acc =
            vCons newToken acc where
                newToken = if tautology pc
                    then mkVarT (a, b, c)
                    else mkVars [((a, b, c), pc), (skipToken, neg pc)]


-- 6. testing                    

projectVList :: Prop -> VList (String, String, (Int, Int)) -> [[(String, String, (Int, Int))]]
projectVList pc vl =
    if (case vnull vl of Var ((x,pc):xs) -> x)
        -- above is hack which works only in all-same-length case
        then []
        else x : (projectVList pc (vtail vl))
            where
                Var xls = vhead vl
                x = concatMap f xls
                f y = case y of
                    (t, myPC) -> if implies myPC pc 
                        then [t]
                        else []


-- Usage instructions:
-- java -jar TypeChef-0.4.2.jar ifdef1.c 2>&1 >/dev/null | stack runghc testparse.hs  

main = do
    -- 0. recieve raw text from typechef
    contents <- getContents
    -- 1. preprocess that text into tokens
    let toks = preprocessor $ contents
    print "TOKENS:"
    mapM_ print $ toks
    -- 2. set up a universe from the features in those tokens' PCs
    let universe = mkUniverse $ collectFromTokens toks
    print "FEATURES:"
    print $ collectFromTokens toks
    -- 3. convert tokens to a VList
    let vl = makeVList $ convertPCsToBDD universe toks
    -- print $ makeVList $ convertPCsToBDD universe toks
    -- 4. to test, extract regular lists satisfying a couple different PCs
    let [pc_b,pc_c,pc_a] = map snd universe
    let myPC1 = conj [neg pc_a, neg pc_b, pc_c]
    let myPC2 = pc_a
    print "PROJECTION TEST 1:"
    mapM_ print $ projectVList myPC1 vl
    print "PROJECTION TEST 2:"
    mapM_ print $ projectVList myPC2 vl

{- OUTPUT OF ABOVE:

"TOKENS:"
("IDENTIFIER","int",(15,0),TT)
("IDENTIFIER","main",(15,4),TT)
("(","(",(15,8),TT)
(")",")",(15,9),TT)
("{","{",(15,11),TT)
("IDENTIFIER","return",(15,12),TT)
("INTEGER","3",(7,10),Feature "B")
("INTEGER","4",(10,10),And [Feature "C",Not (Feature "B"),Or [Feature "B",Feature "C"]])
("INTEGER","5",(12,10),And [Not (Feature "B"),Not (Feature "C"),Or [Not (Feature "C"),Feature "B",And [Not (Feature "B"),Not (Feature "C")]]])
("+","+",(15,21),TT)
("INTEGER","1",(2,10),Feature "A")
("INTEGER","2",(4,10),Not (Feature "A"))
(";",";",(15,24),TT)
("}","}",(15,25),TT)

"FEATURES:"
["B","C","A"]

"PROJECTION TEST 1:"
[("IDENTIFIER","int",(15,0))]
[("IDENTIFIER","main",(15,4))]
[("(","(",(15,8))]
[(")",")",(15,9))]
[("{","{",(15,11))]
[("IDENTIFIER","return",(15,12))]
[("SKIP","SKIP",(0,0))]
[("INTEGER","4",(10,10))]
[("SKIP","SKIP",(0,0))]
[("+","+",(15,21))]
[("SKIP","SKIP",(0,0))]
[("INTEGER","2",(4,10))]
[(";",";",(15,24))]
[("}","}",(15,25))]

"PROJECTION TEST 2:"
[("IDENTIFIER","int",(15,0)),("IDENTIFIER","int",(15,0)),("IDENTIFIER","int",(15,0))]
[("IDENTIFIER","main",(15,4)),("IDENTIFIER","main",(15,4)),("IDENTIFIER","main",(15,4))]
[("(","(",(15,8)),("(","(",(15,8)),("(","(",(15,8))]
[(")",")",(15,9)),(")",")",(15,9)),(")",")",(15,9))]
[("{","{",(15,11)),("{","{",(15,11)),("{","{",(15,11))]
[("IDENTIFIER","return",(15,12)),("IDENTIFIER","return",(15,12)),("IDENTIFIER","return",(15,12))]
[("INTEGER","3",(7,10)),("SKIP","SKIP",(0,0)),("SKIP","SKIP",(0,0))]
[("SKIP","SKIP",(0,0)),("INTEGER","4",(10,10)),("SKIP","SKIP",(0,0))]
[("SKIP","SKIP",(0,0)),("SKIP","SKIP",(0,0)),("INTEGER","5",(12,10))]
[("+","+",(15,21)),("+","+",(15,21)),("+","+",(15,21))]
[("INTEGER","1",(2,10)),("INTEGER","1",(2,10)),("INTEGER","1",(2,10))]
[("SKIP","SKIP",(0,0)),("SKIP","SKIP",(0,0)),("SKIP","SKIP",(0,0))]
[(";",";",(15,24)),(";",";",(15,24)),(";",";",(15,24))]
[("}","}",(15,25)),("}","}",(15,25)),("}","}",(15,25))]


-}





        
