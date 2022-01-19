module Data.AssertConstraint where
import Z3.Monad
import Data.Constraints
import Data.Terms
import PrelNames (c1TyConKey)

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

