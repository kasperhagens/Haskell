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
    Side,
    showsimps,
    simplification)

getInteger :: String -> IO Int
getInteger message =
    do  putStrLn message -- show a message like "Enter an integer"
        x <- getLine
        if all isDigit x
            then
                return (read x :: Int)
            else
                 do
                    getInteger "Enter a valid integer"


doSimplification :: Int -> Side -> Position -> Rule -> Proofstate -> IO Proofstate
doSimplification n s p r pfst = do
    putStrLn "Current proofstate:"
    print pfst
    putStrLn "Which equation to simplify? Counting starts at 0."
    n <- getLine
    putStrLn "On which side of the equation to simplify: Left or Right?"
    s <- getLine
    putStrLn "Enter the position of the subterm to simplify"
    p <- getLine
    putStrLn "Which rule to use? Counting starts at 0."
    r <- getLine
    return ([],[])

main :: IO ()
main = do
    print 4
