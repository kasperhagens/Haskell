module Data.MakeConstraint where
import Z3.Monad
import Data.Constraints
import Data.Terms
import PrelNames (c1TyConKey)

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
makeBasicformula TT = mkTrue
makeBasicformula FF = mkFalse

makeBasicformula (Eq t1 t2) = do
                                a <- makeTerm t1
                                b <- makeTerm t2
                                mkEq a b

makeBasicformula (Lt t1 t2) = do
                                a <- makeTerm t1
                                b <- makeTerm t2
                                mkLt a b

makeBasicformula (Le t1 t2) = do
                                a <- makeTerm t1
                                b <- makeTerm t2
                                mkLe a b

makeBasicformula (Gt t1 t2) = do
                                a <- makeTerm t1
                                b <- makeTerm t2
                                mkGt a b

makeBasicformula (Ge t1 t2) = do
                                a <- makeTerm t1
                                b <- makeTerm t2
                                mkGe a b

makeConstraint :: Constraint -> Z3 AST
makeConstraint (B f) = makeBasicformula f

makeConstraint (Or c1 c2) = do
                                a <- makeConstraint c1
                                b <- makeConstraint c2
                                mkOr [a,b]

makeConstraint (And c1 c2) = do
                                a <- makeConstraint c1
                                b <- makeConstraint c2
                                mkAnd [a,b]

makeConstraint (N c) = do
                                a <- makeConstraint c
                                mkNot a
