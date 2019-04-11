import System.IO
import System.Environment
import Control.Monad
import Data.List.Split 

import Text.Parsec
import Text.Parsec.String (Parser)

-- token preprocessor
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


-- features parsing
-- ref: http://jakewheat.github.io/intro_to_parsing/

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

-- java -jar TypeChef-0.4.2.jar ifdef1.c 2>&1 >/dev/null | runghc testparse.hs 

main = do
    contents <- getContents
    --args <- getArgs
    --putStrLn $ head args
    --contents <- readFile $ head args -- "test_token_input.txt"
    --print contents
    --print $ breakStr $ contents
    mapM_ print $ preprocessor $ contents
    {-
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

        
