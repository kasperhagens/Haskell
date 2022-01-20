import qualified Z3 as Z
import UnitTest.Terms
import Data.Zz

cstr = Or (N (B ( V 0 `Gt` F "2" []))) (B (V 0 `Gt` F "0" []))
main :: IO ()
main = do
    c <- uConstraintCheck cstr
    putStrl (show c)
--    putStrLn "Test suite not yet implemented"
--    Z.printResult
--    printTest
