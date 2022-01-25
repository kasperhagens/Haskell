module Main where
import Lib
import Z3.Monad
import Data.Terms
import Data.Rules
import Data.Equations
import Data.Constraints
import Data.Zz
import Data.Char
import Data.Deductionsystem (
    Proofstate,
    Side (..),
    Rules,
    showsimps,
    simplification)

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

-- !!WARNING!! The function getPosition will not do a safety check to deterine whether p is really a position (we could implement this later). If we enter an invalid position then it will crash.
getPosition :: String -> IO Position
getPosition message =
    do  putStrLn message
        p <- getLine
        return (read p :: Position)

repeatSimplification :: Rules -> Proofstate -> IO Proofstate
repeatSimplification rs (eqs, hs) = do
    putStrLn "Current proofstate:"
    putStrLn ("E = " ++ show eqs)
    putStrLn ("H = " ++ show hs)
    n <- getInteger "Which equation to simplify? Counting starts at 0."
    s <- getLeftRight "On which side of this equation to simplify: Left or Right?"
    p <- getPosition "Enter the position of the subterm to simplify"
    putStrLn "These are the rules"
    print rs
    m <- getInteger "Which rule to use in the simplification? Counting starts at 0."
    y <- simplification n s p (rs!!m) (eqs, hs)
    repeatSimplification rs y

rs = [R (F "f" [V 0]) (F "f" [F "f" [V 0]]) (B TT)]
eqs = [E (F "f" [V 0]) (F "g" [V 0]) (B TT)]
pfst = (eqs, [])

main :: IO ()
main = do
    x <- repeatSimplification rs pfst
    print x
