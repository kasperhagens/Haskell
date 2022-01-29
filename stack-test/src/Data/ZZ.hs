module Data.Zz where
import Z3.Monad
import Data.Terms
import Data.Equations
import Data.Constraints
import Data.Make
import Data.Assert
import Data.Maybe

checkConstraint :: Constraint -> Z3 Result
checkConstraint cstr = do
    assertConstraint cstr
    check

-- uConstraintCheck c checks whether constraint c holds universally, i.e. whether not c has no model
uConstraintCheck :: Constraint -> IO Bool
uConstraintCheck cstr = do
    res <- evalZ3 (checkConstraint (N cstr))
    if res == Unsat then return True else return False
