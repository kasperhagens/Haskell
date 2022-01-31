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
    Hypothesis,
    Rules,
    equationSide,
    showsimps,
    simplification,
    expansionSingleRule,
    expansion,
    deletion,
    eqdeletion)
import qualified Data.Map as Map
import Data.Maybe

printEqs :: String -> [Equation] -> IO ()
printEqs message eqs = do
    let l = length eqs
    if l==0
        then do
            putStrLn ("No " ++ (map toLower message))
            putStrLn " "
        else do
        let eqsindex = zipWith (++) (replicate l "e") (fmap show [0..l])
            numberedeqs = zipWith (\x y->x ++ ": " ++ y) eqsindex (fmap show eqs)
        putStrLn message
        mapM_ putStrLn numberedeqs
        putStrLn " "

printRules :: String -> [Rule] -> String -> IO ()
printRules message rs symb = do
    let l = length rs
    if l==0
        then do
            putStrLn ("No " ++ (map toLower message))
            putStrLn " "
        else do
        let rsindex = zipWith (++) (replicate l symb) (fmap show [0..l])
            numberedrs = zipWith (\x y->x ++ ": " ++ y) rsindex (fmap show rs)
        putStrLn message
        mapM_ putStrLn numberedrs
        putStrLn " "

printPfst :: Proofstate -> IO ()
printPfst (eqs, hs) = do
    printEqs "Equations" eqs
    printRules "Hypothesis" hs "h"

n=0
eqs = [E (F "/" [F "*" [F "2" [], V 0], F "2" []]) (V 0) (B TT)]
pfst = (eqs, [])

main :: IO ()
main = do
    printPfst pfst
    x <- eqdeletion 0 1 [[]] [[]] pfst
    putStrLn "Equation Deletion gives"
    printPfst x
    y <- deletion 0 x
    putStrLn "Deletion gives"
    printPfst y
-- putStrLn (show x )
--    putStrLn "Test suite not yet implemented"
--    Z.printResult
--    printTest
