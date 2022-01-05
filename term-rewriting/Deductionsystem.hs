-- In this module we model the deduction system for constrainted program equations as described in the following paper
-- Verifying Procedural Programs via Constrained Rewriting Induction - Carsten Fuhs, Cynthia Kop, Naoki Nishida, page A:16 - A:20.
-- source: https://arxiv.org/abs/1409.0166

-- For the moment we slightly simplify the notion of a proofstate by ignoring the complete/incomplete flag. So we consider a proofstate as a tuple (E,H) where E is a set of equations and H is a set of rules called induction hypothesis.
-- The goal is to start with a set of equations E and, by using the interference rules, finding a deduction sequence (E,Ø) ⊢ ... ⊢ (Ø,H)
module Deductionsystem where
import qualified Data.Map as Map
import Terms (Term(..), Varname, Substitution, appsub, subterms)
import Rules (Basicformula(..), Constraint(..), Rule (..), leftsideR, rightsideR, appsubC, appsubR)
import Equations
-- equalize is a helper function used to define getinstanceleft and getinstanceleftright
equalize :: Term -> Term -> [(Varname, Term)]
equalize t1 t2 = case t1 of
    (V x) -> case t2 of
        (V y) -> [(x, V y)]
        (F f ts) -> [(x, F f ts)]
    (F f ts) -> case t2 of
        (V y) ->[]
        (F g qs) -> if (f/=g || length(ts)/=length(qs)) then [] else (concat [ equalize a b | (a,b) <- (zip ts qs)])

-- If we have an equation
-- e: f(x1,...,xn) ≈  f'(a1,...,am)  [C1]
-- and a rule
-- r: g(y1,...,yi) -> g'(b1,...,bj)  [C2]
-- then getinstanceleft r e may give the substitution tau such that
-- g(y1,...,yi)*tau ~ f(x1,...,xn), if such a tau (possibly) exists. If such a tau does not exist then getinstance r e = [].
--
-- Example 1
-- r : f(v1,v1) -> g(v1)  [true]
-- e : f(v4,v5) ≈  g(v4)  [v4=v5]
--
-- r = R (F "f" [V 1, V 1]) (F "g" [V 1]) (B TT)
-- e = E (F "f" [V 4, V 5]) (F "g" [V 5]) (B (V 4 `Eq` V 5))
-- then
-- getinstanceleft r e = Map.fromList [(1, v4), (1, v5)] = fromList [(1,v5)]
--
-- In getinstanceleftriht we also equalize the right-hand sides of the rule with the equation.
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
getinstanceleft :: Rule -> Equation -> Substitution
getinstanceleft r e = Map.fromList (equalize (leftsideR r) (leftsideEQ e))

getinstanceleftright :: Rule -> Equation -> Substitution
getinstanceleftright r e = Map.fromList ((equalize (leftsideR r) (leftsideEQ e)) ++ (equalize (rightsideR r) (rightsideEQ e)))

-- If r is a rule then
-- getinstancesleft r e = [(s, t) | t is a subterm of the lefthand side of equation e such that the rule r*s is applicable to t]
-- Example
-- r : f(v1) -> v1      [TT]
-- e : f(f(v1)) ≈ g(v1) [TT]
--
-- r = R (F "f" [V 1]) (V 1) (B (TT))
-- e = E (F "f" [F "f" [V 1]]) (F "g" [V 1]) (B (TT))
-- getinstancesleft r e = [(fromList [(1,f(v1))],f(f(v1))),(fromList [(1,v1)],f(v1))]
getinstancesleft :: Rule -> Equation -> [(Substitution,Term)]
getinstancesleft r e = [(Map.fromList (equalize (leftsideR r) t), t) | t <- subterms (leftsideEQ e), equalize (leftsideR r) t /= []]

-- Example (from the seminar-document, page 102, slide 30)
-- sum1 = [R (F "sum1" [V 1]) (F "0" []) (B (V 1 `Le` F "0" [])), R (F "sum1" [V 1]) (F "+" [V 1, F "sum1" [F "-" [V 1, F "1" []]]]) (B (V 1 `Ge` F "0" [])), R (F "+" [V 1, F "return" [V 2]]) (F "return"[F "+" [V 1, V 2]]) (B TT)]
--
-- sum2 = [R (F "sum2"[V 1]) (F "u" [V 1, F "0" [], F "0" []]) (B TT), R (F "u" [V 1, V 2, V 3]) (F "u" [V 1, F "+" [V 2, F "1" [] ], F "+" [V 3, V 2]]) (B (V 2 `Le` V 1)), R (F "u" [V 1, V 2, V 3]) (F "return" [V 3]) (N (B (V 2 `Le` V 1))) ]
type Rules = [Rule]
type Hypothesis = [Rule]
type Equations = [Equation]
type Proofstate = (Equations, Rules)
