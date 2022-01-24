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

pfst = (eqs, [])

getDigit :: String -> IO Int
getDigit message =
    do  putStr message -- like "Enter a number"
        x <- getChar
        putStrLn ""
        if isDigit x
            then
                return (digitToInt x)
            else
                do
                    putStrLn ""



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

main :: IO ()
main = do

--    putStrLn "Test suite not yet implemented"
--    Z.printResult
--    printTest
