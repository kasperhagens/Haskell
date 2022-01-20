import Z3.Monad
import Data.Terms
import Data.Constraints
import Data.Zz
-- v0 > 2 -> v0 > 0 is universally true
c0 = Or (N (B ( V 0 `Gt` F "2" []))) (B (V 0 `Gt` F "0" []))
-- v0 >0 -> v0 > 2 is not universally true
c1 = Or (N (B ( V 0 `Gt` F "0" []))) (B (V 0 `Gt` F "2" []))

main :: IO ()
main = do
    a <- uConstraintCheck c0
    b <- uConstraintCheck c1
    print a
    print b
--    putStrLn "Test suite not yet implemented"
--    Z.printResult
--    printTest
