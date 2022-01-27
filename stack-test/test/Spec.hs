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
    expansion)
import qualified Data.Map as Map
import Data.Maybe

n=0
s = Data.Deductionsystem.Left :: Side
p = [] :: Position
r = R (F "f" [V 2, V 3]) (V 2) (B (V 2 `Ge` V 3)) :: Rule
rs = [r] :: Rules
psi = constraintR r :: Constraint
l = leftsideR r :: Term
eqs = [E (F "f" [F "g" [V 0], V 1]) (F "g" [V 0]) (B TT)]
hs = [] :: Hypothesis
pfst :: Proofstate
pfst = (eqs, hs) :: Proofstate
E a b phi = eqs !! n
u = postoterm (Data.Deductionsystem.equationSide (E a b phi) s) p
tau = Map.fromList (equalize l (fromJust u))

main :: IO ()
main = do
--    checkconstraint <- uConstraintCheck (Or (N phi) (appsubC tau psi))
--    putStrLn (show phi
--        ++
--        " -> "
--        ++
--        show (appsubC tau psi)
--        ++
--        " is "
--        ++
--        show checkconstraint)
    exp <- expansion n s p rs pfst
    putStrLn " "
    putStrLn " "
    putStrLn ("EXPANSION on the "
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
    putStrLn "yields the proofstate"
    putStrLn (show exp)


-- putStrLn (show x )
--    putStrLn "Test suite not yet implemented"
--    Z.printResult
--    printTest
