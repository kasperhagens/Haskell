module Equations where
import qualified Data.Map as Map
import Terms (Term(..), Varname, Substitution )
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
-- then getinstance r e may give the substitution tau such that
-- g(y1,...,yi)*tau ~ f(x1,...,xn), if such a tau (possibly) exists. If such a tau does not exist then getinstance r e = [].
--
-- Example
-- r : f(v1,v1) -> g(v1)  [true]
-- e : f(v4,v5) ≈ g(v4)  [v4=v5]
--
-- r = R (F "f" [V 1, V 1]) (F "g" [V 1]) (B TT)
-- e = E (F "f" [V 4, V 5]) (F "g" [V 5]) (B (V 4 `Eq` V 5))
-- then
-- getinstance r e = Map.fromList [(1, v4), (1, v5)] = fromList [(1,v5)]
equalize :: Term -> Term -> [(Varname, Term)]
equalize t1 t2 = case t1 of
    (V x) -> case t2 of
        (V y) -> [(x, V y)]
        (F f ts) -> [(x, F f ts)]
    (F f ts) -> case t2 of
        (V y) ->[]
        (F g qs) -> if (f/=g || length(ts)/=length(qs)) then [] else (concat [ equalize a b | (a,b) <- (zip ts qs)])

getinstance :: Rule -> Equation -> Substitution
getinstance r e = Map.fromList (equalize (leftsideR r) (leftsideEQ e))
