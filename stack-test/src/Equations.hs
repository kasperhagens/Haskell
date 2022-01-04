-- In this module we model the constrainted programm equations as described in the following paper
-- Verifying Procedural Programs via Constrained Rewriting Induction - Carsten Fuhs, Cynthia Kop, Naoki Nishida, page A:15, section 4.2, definition 4.3
-- source: https://arxiv.org/abs/1409.0166
module Equations where
import qualified Data.Map as Map
import Terms (Term(..), Varname, Substitution, appsub)
import Rules (Basicformula(..), Constraint(..), Rule (..), leftsideR, rightsideR, appsubC, appsubR)

--Example of equation
--E (F "f" [V 1]) (F "g" [V 2]) (B (V 1 `Le` V 2))
data Equation = E Term Term Constraint
instance Show Equation where
    show (E t1 t2 c) = (show t1) ++ "~" ++ (show t2) ++ " [" ++ (show c)++"]"

leftsideEQ :: Equation -> Term
leftsideEQ (E t1 t2 c) = t1

rightsideEQ :: Equation -> Term
rightsideEQ (E t1 t2 c) = t2

reverseEQ :: Equation -> Equation
reverseEQ (E t1 t2 c) = E t2 t1 c

-- If we have an equation
-- e: f(x1,...,xn) ≈ f'(a1,...,am) [C1]
-- and a rule
-- r: g(y1,...,yi) -> g'(b1,...,bj)  [C2]
-- then getinstanceleft r e may give the substitution tau such that
-- g(y1,...,yi)*tau ~ f(x1,...,xn), if such a tau (possibly) exists. If such a tau does not exist then getinstance r e = [].
--
-- Example 1
-- r : f(v1,v1) -> g(v1)  [true]
-- e : f(v4,v5) ≈ g(v4)  [v4=v5]
--
-- r = R (F "f" [V 1, V 1]) (F "g" [V 1]) (B TT)
-- e = E (F "f" [V 4, V 5]) (F "g" [V 5]) (B (V 4 `Eq` V 5))
-- then
-- getinstanceleft r e = Map.fromList [(1, v4), (1, v5)] = fromList [(1,v5)]
--
--
-- Example 2
-- r : u(v1,v2,v3) -> v1 + u(v4,v5,v6) [v5<=v1 /\ v1=v4+1 /\ v2=v5+1 /\ v3=v6+v5]
-- e : u(v1,v7,v8) ≈  v1 + u(v4,v2,v3) [v5<=v1 /\ v1=v4+1 /\ v2=v5+1 /\ v3=v6+v5 /\ v2<=v1 /\ v7=v2+1 /\ v8=v3+v2]
--
-- r = R (F "u" [V 1, V 2, V 3]) (F "+" [V 1, F "u" [V 4, V 5, V 6]]) (B (V 5 `Le` V 1) `And` B (V 1 `Eq` F "+" [V 4, F "1" []]) `And` B (V 2 `Eq` F "+" [V 5, F "1" [] ]) `And` B (V 3 `Eq` F "+" [V 6, V 5]))
-- e = E (F "u" [V 1, V 7, V 8]) (F "+" [V 1, F "u" [V 4, V 2, V 3]]) (B (V 5 `Le` V 1) `And` B (V 1 `Eq` F "+" [V 4, F "1" []]) `And` B (V 2 `Eq` F "+" [V 5, F "1" [] ]) `And` B (V 3 `Eq` F "+" [V 6, V 5]) `And` B (V 2 `Le` V 1) `And` B (V 7 `Eq` F "+" [V 2, F "1" [] ]) `And` B (V 8 `Eq` F "+" [V 3, V 2]))
--
-- s = getinstanceleftright r e = fromList [(1,v1),(2,v7),(3,v8),(4,v4),(5,v2),(6,v3)]
--
-- appsubR s r
-- =
-- u(v1,v7,v8)->v1+u(v4,v2,v3) [(((v2<=v1) and (v1=v4+1())) and (v7=v2+1())) and (v8=v3+v2)]
equalize :: Term -> Term -> [(Varname, Term)]
equalize t1 t2 = case t1 of
    (V x) -> case t2 of
        (V y) -> [(x, V y)]
        (F f ts) -> [(x, F f ts)]
    (F f ts) -> case t2 of
        (V y) ->[]
        (F g qs) -> if (f/=g || length(ts)/=length(qs)) then [] else (concat [ equalize a b | (a,b) <- (zip ts qs)])

getinstanceleft :: Rule -> Equation -> Substitution
getinstanceleft r e = Map.fromList (equalize (leftsideR r) (leftsideEQ e))

getinstanceleftright :: Rule -> Equation -> Substitution
getinstanceleftright r e = Map.fromList ((equalize (leftsideR r) (leftsideEQ e)) ++ (equalize (rightsideR r) (rightsideEQ e)))

appsubE :: Substitution -> Equation -> Equation
appsubE s (E t1 t2 c) = E (appsub s t1) (appsub s t2) (appsubC s c)
