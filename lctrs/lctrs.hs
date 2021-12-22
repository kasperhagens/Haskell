import qualified Data.Map as Map
data Term t = Var t | Func t [Term t] | Const t deriving (Eq, Show)

instance Functor Term where
    fmap f (Var x) = Var (f x)
    fmap f (Const x) = Const (f x)
    fmap f (Func x ls) = Func (f x) [fmap f l | l<-ls]

-- Note: we introduce a separate type constructor for constants instead of considering a constant as a 0-ary functionsymbol.
data Constraint t = Eq (Term t) (Term t)
                    |
                    Lt (Term t) (Term t) |
                    Le (Term t) (Term t)
data Rule t = Rule (Term t) (Term t) (Constraint t)

-- Write a function
-- sat :: Constraint t -> Bool
-- such that
--

-- GOAL: write a function
-- instanceof :: Rule t -> Rule t -> Bool
-- such that
-- instanceof r1 r2 == True <=> r1 is an instance of r2
