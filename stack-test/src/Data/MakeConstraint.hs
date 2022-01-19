module Data.MakeConstraint where
import Z3.Monad
import Data.Constraints
import Data.Terms

makeTerm :: Term -> Z3 AST
makeTerm (V x) = mkFreshIntVar (show (V x))
makeTerm (F "+" [t1,t2]) = do
                                a <- makeTerm t1
                                b <- makeTerm t2
                                mkAdd [a,b]

makeTerm (F "*" [t1,t2]) = do
                                a <- makeTerm t1
                                b <- makeTerm t2
                                mkMul [a,b]

makeTerm (F "-" [t1,t2]) = do
                                a <- makeTerm t1
                                b <- makeTerm t2
                                mkSub [a,b]

-- We only allow terms with functionsymbols +, - and *
makeTerm t = mkFalse

makeBasicformula :: Basicformula -> Z3 AST

makeBasicformula TT =
