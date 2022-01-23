import Z3.Monad
import Data.Terms
import Data.Rules
import Data.Equations
import Data.Constraints
import Data.Zz
import qualified Data.Deductionsystem as Ded
pfst = (eqs, [])
main :: IO ()
main = do
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
--    putStrLn "Test suite not yet implemented"
--    Z.printResult
--    printTest
