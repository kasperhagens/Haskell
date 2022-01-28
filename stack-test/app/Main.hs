module Main where
import Lib
import Z3.Monad
import Data.Terms
import Data.Rules
import Data.Equations
import Data.Constraints
import Data.Zz
import Data.Char
import Data.Maybe
import Data.Deductionsystem (
    Proofstate,
    Side (..),
    Rules,
    showsimps,
    simplification,
    equationSide)

getInteger :: String -> IO Int
getInteger message =
    do  putStrLn message -- show a message like "Enter an integer"
        x <- getLine
        if all isDigit x && (read x >= 0)
            then
                return (read x :: Int)
            else
                getInteger "Enter a valid integer"

getLeftRight :: String -> IO Side
getLeftRight message =
    do  putStrLn message -- show a message like "Wchich side?"
        x <- getLine
        if x == "Left" || x == "left"
            then
                return Data.Deductionsystem.Left
            else
                if x == "Right" || x == "right"
                    then
                        return Data.Deductionsystem.Right
                    else
                        getLeftRight "Left or Right?"

getRuleSet :: String -> IO String
getRuleSet message =
    do  putStrLn message --
        x <- getLine
        if x == "R" || x == "r"
            then
                return "rs"
            else
                if x == "H" || x == "h"
                    then
                        return "hs"
                    else
                        getRuleSet "R or H?"

getRule :: String -> [Rule] -> IO Int
getRule message rules = do
    putStrLn message
    l <- getLine
    let lth = length rules
        eval = (fmap (\n x -> (n,x == ("r" ++ show n) || x == show n)) [0..(lth -1)])<*> [l]
        evaltrue = filter (\x -> snd x == True) eval
    if null evaltrue
        then
            getRule "This rule does not exist. Enter a valid rule." rules
        else do
            let n = fst (head evaltrue)
            if (n > lth || n<0)
                then
                    getRule "This rule does not exist. Enter a valid rule." rules
                else
                    return n

getEq :: String -> [Equation] -> IO Int
getEq message eqs = do
    putStrLn message
    l <- getLine
    let lth = length eqs
        eval = (fmap (\n x -> (n,x == ("r" ++ show n) || x == show n)) [0..(lth -1)])<*> [l]
        evaltrue = filter (\x -> snd x == True) eval
    if null evaltrue
        then
            getEq "This equation does not exist. Enter a valid equation." eqs
        else do
            let n = fst (head evaltrue)
            if (n > lth || n<0)
                then
                    getEq "This equation does not exist. Enter a valid equation." eqs
                else
                    return n

-- !!WARNING!! The function getPosition will not do a safety check to deterine whether p is really a position (we could implement this later). If we enter an invalid position then it will crash.
getPosition :: String -> IO Position
getPosition message =
    do  putStrLn message
        p <- getLine
        return (read p :: Position)

printEqs :: String -> [Equation] -> IO ()
printEqs message eqs = do
    let l = length eqs
        eqsindex = zipWith (++) (replicate l "e") (fmap show [0..l])
        numberedeqs = zipWith (\x y->x ++ ": " ++ y) eqsindex (fmap show eqs)
    putStrLn message
    mapM_ putStrLn numberedeqs
    putStrLn " "

printRules :: String -> [Rule] -> String -> IO ()
printRules message rs symb = do
    let l = length rs
        rsindex = zipWith (++) (replicate l symb) (fmap show [0..l])
        numberedrs = zipWith (\x y->x ++ ": " ++ y) rsindex (fmap show rs)
    putStrLn message
    mapM_ putStrLn numberedrs
    putStrLn " "

printPfst :: Proofstate -> IO ()
printPfst (eqs, hs) = do
    printEqs "Equations" eqs
    printRules "Hypothisis" hs "h"
--    let l = length eqs
--        eqsindex = zipWith (++) (replicate l "e") (fmap show [0..l])
--        numberedeqs = zipWith (\x y->x ++ ": " ++ y) eqsindex (fmap show eqs)
--
--        m = length hs
--        hsindex = zipWith (++) (replicate m "h") (fmap show [0..m])
--        numberedhs = zipWith (\x y->x ++ ": " ++ y) hsindex (fmap show hs)
--    putStrLn "Equations"
--    mapM_ putStrLn numberedeqs
--    putStrLn " "
--    putStrLn "Hypothesis"
--    mapM_ putStrLn numberedhs
--    putStrLn " "

-- printEqs :: Equat

interactiveSimplification :: Rules -> Proofstate -> IO Proofstate
interactiveSimplification rs (eqs, hs) = do
    putStrLn "Current proofstate:"
    printPfst (eqs,hs)
    n <- getEq "Which equation to simplify?" eqs
    s <- getLeftRight "On which side of this equation to simplify: Left or Right?"
    p <- getPosition (
        "Enter the position of the subterm of "
        ++
        show (equationSide (eqs !! n) s)
        ++
        " to simplify"
        )
    let u = postoterm (equationSide (eqs !! n) s) p
    if (u == Nothing)
        then do
            putStrLn "Invalid position, try again."
            interactiveSimplification rs (eqs, hs)
        else do
            let t = fromJust u
            if null hs
                then do
                    putStrLn "These are the rules"
                    print rs
                    m <- getRule ("Which rule to use to simplify "
                        ++
                        show t ++"?") rs
                    y <- simplification n s p (rs!!m) (eqs, hs)
                    interactiveSimplification rs y
                else do
                    putStrLn "These are the rules"
                    putStrLn ("R = " ++ show rs)
                    putStrLn ("H = " ++ show hs)
                    l <- getRuleSet ("Using R or H to simplify " ++ (show t) ++ "?")
                    if l == "rs"
                        then do
                            m <- getInteger "Which rule from R to use in the simplification?"
                            y <- simplification n s p (rs!!m) (eqs, hs)
                            interactiveSimplification rs y
                        else do
                            m <- getInteger "Which rule from H to use in the simplification?"
                            y <- simplification n s p (hs!!m) (eqs, hs)
                            interactiveSimplification rs y

r0=R (F "f" [V 0]) (F "f" [F "f" [V 0]]) (B TT)
rs = [r0, r0]

e = E (F "f" [V 0]) (F "g" [V 0]) (B TT)
eqs = [e, e]
pfst = (eqs, rs)
hs = [R (V 0) (V 1) (B (TT))]

main :: IO ()
main = do
    printPfst (eqs, hs)
