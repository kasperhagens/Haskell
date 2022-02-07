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
    eqdeletion,
    getinstanceleft
    )
import qualified Data.Map as Map
import Data.Maybe
import Data.Constraints (constrToList)

constraintEqImpRule :: Equation -> Rule -> IO Bool
constraintEqImpRule (E e1 e2 ce) (R r1 r2 cr) =
    if null tau
        then
            return False
        else
            uConstraintCheck (Or (N ce) (appsubC tau cr))
    where tau = getinstanceleft (R r1 r2 cr) (E e1 e2 ce)

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

r0 = R (F "sum" [V 0]) (F "error" []) (B (V 0 `Lt` F "0" []))
r1 = R (F "sum" [V 0]) (F "v" [V 0, F "sum" [F "-" [V 0, F "1" []]]]) (B (V 0 `Gt` F "0" []))
r2 = R (F "sum" [V 0]) (F "return" [F "0" []]) (B (V 0 `Eq` F "0" []))
r3 = R (F "v" [V 0, F "return" [V 1]]) (F "return" [F "+" [V 0, V 1]]) (B TT)
r4 = R (F "return" [V 0]) (F "error" []) (B (V 0 `Lt` F "0" []))
rs = [r0, r1, r2, r3, r4]

e = E (F "v" [V 0, F "sum" [F "-" [V 0, F "1" []]]]) (F "return" [F "/" [F "*" [V 0, F "+" [V 0, F "1" []]], F "2" []]]) (And (B TT) (B (V 0 `Gt` F "0" [])))
eqs = [e]
h0 = R (F "sum" [V 0]) (F "return" [F "/" [F "*" [V 0, F "+" [V 0, F "1" []]], F "2" []]]) (B TT)
hs = [h0]
r=h0
pfst = (eqs, hs)
n = 0
s = Data.Deductionsystem.Left
p = [1]

subsequentCommas :: String -> Bool
subsequentCommas l =
    not (null l || null (tail l)) && (
        let (x:y:ys) = l in
        (x == ',' && y == ',') ||
                subsequentCommas (y:ys))

isIntList :: String -> Bool
isIntList l =
--    null l
--    ||
    (not (head l /= '[' || last l /= ']') && (
        let k = tail (init l)
            y = filter (\x -> isDigit x || x == ',') k
        in
        k == y &&
                not (head y == ',' || last y == ',') &&
                not (subsequentCommas k)))

l = []

c1 = B (V 0 `Gt` F "0" []) `And` (B (V 1 `Gt` F "0" []) `And` B (V 2 `Gt` F "0" []))
c2 = B (V 0 `Gt` F "0" []) `And` B (V 1 `Gt` F "0" [])

main :: IO ()
main = do
    print (constrToList c1)
    print (constrToList c2)
-- putStrLn (show x )
--    putStrLn "Test suite not yet implemented"
--    Z.printResult
--    printTest
