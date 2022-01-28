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

getrule :: String -> IO String
getrule message =
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
                        getrule "R or H?"

-- !!WARNING!! The function getPosition will not do a safety check to deterine whether p is really a position (we could implement this later). If we enter an invalid position then it will crash.
getPosition :: String -> IO Position
getPosition message =
    do  putStrLn message
        p <- getLine
        return (read p :: Position)

--printNthEq :: Equation ->

printPfst :: Proofstate -> IO ()
printPfst (eqs, hs) = do
    let l = length eqs
        eqsindex = zipWith (++) (replicate l "e") (fmap show [0..l])
        numberedeqs = zipWith (\x y->x ++ ": " ++ y) eqsindex (fmap show eqs)

        m = length hs
        hsindex = zipWith (++) (replicate m "h") (fmap show [0..m])
        numberedhs = zipWith (\x y->x ++ ": " ++ y) hsindex (fmap show hs)
    putStrLn "Equations"
    mapM_ putStrLn numberedeqs
    putStrLn " "
    putStrLn "Hypothesis"
    mapM_ putStrLn numberedhs
    putStrLn " "

-- printEqs :: Equat

repeatSimplification :: Rules -> Proofstate -> IO Proofstate
repeatSimplification rs (eqs, hs) = do
    putStrLn "Current proofstate:"
    printPfst (eqs,hs)
    n <- getInteger "Which equation to simplify?"
    putStrLn ("You have chosen equation " ++ show (eqs !! n))
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
            putStrLn "Invalid position, start again."
            repeatSimplification rs (eqs, hs)
        else do
            let t = fromJust u
            if null hs
                then do
                    putStrLn "These are the rules"
                    print rs
                    m <- getInteger ("Which rule to use to simplify "
                        ++
                        show t ++"?")
                    y <- simplification n s p (rs!!m) (eqs, hs)
                    repeatSimplification rs y
                else do
                    putStrLn "These are the rules"
                    putStrLn ("R = " ++ show rs)
                    putStrLn ("H = " ++ show hs)
                    l <- getrule ("Using R or H to simplify " ++ (show t) ++ "?")
                    if l == "rs"
                        then do
                            m <- getInteger "Which rule from R to use in the simplification?"
                            y <- simplification n s p (rs!!m) (eqs, hs)
                            repeatSimplification rs y
                        else do
                            m <- getInteger "Which rule from H to use in the simplification?"
                            y <- simplification n s p (hs!!m) (eqs, hs)
                            repeatSimplification rs y

rs = [R (F "f" [V 0]) (F "f" [F "f" [V 0]]) (B TT)]

e = E (F "f" [V 0]) (F "g" [V 0]) (B TT)
eqs = [e, e]
pfst = (eqs, rs)

main :: IO ()
main = do
    x <- repeatSimplification rs pfst
    print x
