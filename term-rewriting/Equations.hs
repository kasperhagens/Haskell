module Equations where
import qualified Data.Map as Map
import Terms (Term(..), Varname )
import Rules (Basicformula(..), Constraint(..), Rule (..), leftsideR)

--Example of equation
--E (F "f" [V 1]) (F "g" [V 2]) (B (V 1 `Le` V 2))
data Equation = E Term Term Constraint
instance Show Equation where
    show (E t1 t2 c) = (show t1) ++ "~" ++ (show t2) ++ " [" ++ (show c)++"]"

leftsideEQ :: Equation -> Term
leftsideEQ (E t1 t2 c) = t1

reverseEQ :: Equation -> Equation
reverseEQ (E t1 t2 c) = E t2 t1 c

-- If we have an equation
-- e: f(x1,...,xn) ≈ f'(a1,...,am) [C1]
-- and a rule
-- r: g(y1,...,yi) -> g'(b1,...,bj)  [C2]
-- then getinstance r e will give the 'substitution' tau such that
-- g(y1,...,yi)*tau = f(x1,...,xn), if it exists. If such a tau does not exist it gives the empty list [].
-- Note, however, that this substitution is not necessarily a mapping (and therefore not of the type Substitution)
-- For example consider
-- r : f(v1,v1) -> g(v1)  [true]
-- e : f(v4,v5) ≈ g(v4)  [v4=v5]
--
-- r = R (F "f" [V 1, V 1]) (F "g" [V 1]) (B TT)
-- e = E (F "f" [V 4, V 5]) (F "g" [V 4]) (B (V 4 `Eq` V 5))
--
-- then getinstance r e = [(1, v4), (1, v5)]
equalize :: Term -> Term -> [(Varname, Term)]
equalize s t = case s of
    (V x) -> case t of
        (V y) -> [(x, V y)]
        (F f l) -> [(x, F f l)]
    (F f l) -> case t of
        (V y) ->[]
        (F g m) -> if (f/=g || length(l)/=length(m)) then [] else (concat [ equalize a b | (a,b) <- (zip l m)])

getinstance :: Rule -> Equation -> [(Varname, Term)]
getinstance r e = equalize (leftsideR r) (leftsideEQ e)
