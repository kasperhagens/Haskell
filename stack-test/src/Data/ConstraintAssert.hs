module Data.ConstraintAssert where
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

constraintassertB :: Basicformula -> Z3()
constraintassertB TT = do
                    tt <- mkTrue
                    assert tt

constraintassertB FF = do
                    ff <- mkFalse
                    assert ff

constraintassertB (Eq t1 t2) = do
                    a <- makeTerm t1
                    b <- makeTerm t2
                    assert =<< (mkEq a b)

constraintassertB (Lt t1 t2) = do
                    a <- makeTerm t1
                    b <- makeTerm t2
                    assert =<< (mkLt a b)

constraintassertB (Le t1 t2) = do
                    a <- makeTerm t1
                    b <- makeTerm t2
                    assert =<< (mkLe a b)

constraintassertB (Gt t1 t2) = do
                    a <- makeTerm t1
                    b <- makeTerm t2
                    assert =<< (mkGt a b)

constraintassertB (Ge t1 t2) = do
                    a <- makeTerm t1
                    b <- makeTerm t2
                    assert =<< (mkGe a b)

constraintassert :: Constraint -> Z3()
constraintassert (B f) = constraintassertB f
