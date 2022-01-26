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
    showsimps,
    simplification,
    expansionSingleRule)
n=0
s = Data.Deductionsystem.Left
p = [] :: Position
r = R (F "f" [V 2, V 3]) (V 2) (B (V 2 `Ge` V 3))
eqs = [E (F "f" [F "g" [V 0], V 1]) (F "g" [V 0]) (B TT)]
hs = []
pfst = (eqs, hs) :: Proofstate

main :: IO ()
main = do
    exp <- expansionSingleRule n s p r pfst
    putStrLn " "
    putStrLn " "
    putStrLn ("Expansion on the "
                ++
                show s
                ++
                "-side of equation ")
    putStrLn (show (eqs !! n))
    putStrLn ("on position "
                ++
                show p
                ++
                " with proofstate "
                )
    putStrLn (show pfst)
    putStrLn " yields "
    putStrLn (show exp)
-- putStrLn (show x )
--    putStrLn "Test suite not yet implemented"
--    Z.printResult
--    printTest
