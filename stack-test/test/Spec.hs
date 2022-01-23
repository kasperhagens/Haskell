import Z3.Monad
import Data.Terms
import Data.Rules
import Data.Equations
import Data.Constraints
import Data.Zz
import qualified Data.Deductionsystem as Ded
-- v0 > 2 -> v0 > 0 is universally true
-- c0 = Or (N (B ( V 0 `Gt` F "2" []))) (B (V 0 `Gt` F "0" []))
-- v0 >0 -> v0 > 2 is not universally true
-- c1 = Or (N (B ( V 0 `Gt` F "0" []))) (B (V 0 `Gt` F "2" []))
-- a <- uConstraintCheck c0
--     b <- uConstraintCheck c1
--     print a
--     print b



-- eqs : {sum1(v1)≈sum2(v1) [True], sum1(v1)≈sum3(v1) [True]}
-- rs : {sum1(v2) -> return(0) [v2 <= 0],  sum2(v2) -> u(v2,0,0) [TT]}
e0 = E (F "sum1" [V 1]) (F "sum2" [V 1]) (B TT)
e1 = E (F "sum1" [V 1]) (F "sum3" [V 1]) (B TT)
eqs = [e0, e1]
r0 = R (F "sum1" [V 2]) (F "return" [F "0" []]) (B (V 2 `Le` F "0" []))
r1 = R (F "sum2"[V 2]) (F "u" [V 2, F "0" [], F "0" []]) (B TT)
rs = [r0, r1]
-- showsimp rs eqs =
-- [
-- (sum1(v1)~sum2(v1) [True],sum1(v2)->return(0) [v2<=0],Left) ,
-- (sum1(v1)~sum3(v1) [True],sum1(v2)->return(0) [v2<=0],Left) ,
-- (sum1(v1)~sum2(v1) [True],sum2(v2)->u(v2,0,0) [True],Right)
-- ]
-- Note that the first two options in this list are non-valid SIMPLIFICATION posibilities. As said: we really have to filter out the valid ones by comparing the constraints with a SAT-solver.

main :: IO ()
main = do
    a <- Ded.showsimps rs eqs
--   b <- Ded.showsimpleft r1 eqs
    print a
--    putStrLn "Test suite not yet implemented"
--    Z.printResult
--    printTest
