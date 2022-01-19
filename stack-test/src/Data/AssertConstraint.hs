module Data.AssertConstraint where
import Z3.Monad
import Data.Constraints
import Data.Terms
import Data.MakeConstraint
import PrelNames (c1TyConKey)

assertBasicformula :: Basicformula -> Z3()
assertBasicformula x = do
                        a <- makeBasicformula x
                        assert a

assertConstraint :: Constraint -> Z3()
assertConstraint x = do
                        a <- makeConstraint x
                        assert a
