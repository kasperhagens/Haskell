-- In this module we model the deduction system for constrainted program equations as described in the following paper
-- Verifying Procedural Programs via Constrained Rewriting Induction - Carsten Fuhs, Cynthia Kop, Naoki Nishida, page A:16 - A:20.
-- source: https://arxiv.org/abs/1409.0166

-- For the moment we slightly simplify the notion of a proofstate by ignoring the complete/incomplete flag. So we consider a proofstate as a tuple (E,H) where E is a set of equations and H is a set of rules called induction hypothesis.
-- The goal is to start with a set of equations E and, by using the interference rules, finding a deduction sequence (E,Ø) ⊢ ... ⊢ (Ø,H)
module Deductionsystem where
import qualified Data.Map as Map
import Terms (Term(..), Varname, Substitution, appsub, subterms, mgu)
import Rules (Basicformula(..), Constraint(..), Rule (..), leftsideR, rightsideR, appsubC, appsubR, equalize, concatnoempties)
import Equations
import qualified Data.List as List
import Prelude hiding (Left, Right)

-- If we have an equation
-- e: f(x1,...,xn) ≈  f'(a1,...,am)  [Ce]
-- and a rule
-- r: g(y1,...,yi) -> g'(b1,...,bj)  [Cr]
-- then getinstanceleft r e may (possibily) give the substitution tau such that
-- g(y1,...,yi)*tau ~ f(x1,...,xn).
-- Note that we do not consider the righthand side of the equation e (we have to do that separately).
-- If such a tau does not exist then getinstance r e = []. See Example 1 for the meaning of ~.
--
-- Example 1
-- r : f(v1,v1) -> g(v1)  [true]
-- e : f(v4,v5) ≈  g(v4)  [v4=v5]
--
-- r = R (F "f" [V 1, V 1]) (F "g" [V 1]) (B TT)
-- e = E (F "f" [V 4, V 5]) (F "g" [V 5]) (B (V 4 `Eq` V 5))
-- then
-- s = getinstanceleft r e
-- = Map.fromList [(1, v4), (1, v5)] = fromList [(1,v5)]
--
-- REMARK
-- The lefthand side of r*s equals f(v5,v5), which (as a term) is not equal to f(v4,v5).
-- However, the equality of these terms follows from the constraint.
-- We denote f(v5,v5)~f(v4,v5).
--
-- In getinstanceleftright we also equalize the right-hand sides of the rule with the equation.
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
getinstanceleftright r e = Map.fromList (concatnoempties [equalize (leftsideR r) (leftsideEQ e), equalize (rightsideR r) (rightsideEQ e)])

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

type Rules = [Rule]
type Hypothesis = [Rule]
type Equations = [Equation]

-- Example (from the seminar-document, page 102, slide 30)
-- r1 : sum1(x) -> return(0)             [x<=0]
-- r2 : sum1(x) -> x + sum(x-1))         [x>=0]
-- r3 : x + return(y) -> return (x+y)    [True]
--
-- r4 : sum2(x) -> u(x,0,0)              [True]
-- r5 : u(x,i,z) -> u(x,i+1,z+i)         [i<=x]
-- r6 : u(x,i,z) -> return(z)            [not (i<=x)]
--
-- r1 = R (F "sum1" [V 1]) (F "return" [F "0" []]) (B (V 1 `Le` F "0" []))
-- r2 = R (F "sum1" [V 1]) (F "+" [V 1, F "sum1" [F "-" [V 1, F "1" []]]]) (B (V 1 `Ge` F "0" []))
-- r3 = R (F "+" [V 1, F "return" [V 2]]) (F "return"[F "+" [V 1, V 2]]) (B TT)
-- sum1 = [r1, r2, r3]
--
-- r4 = R (F "sum2"[V 1]) (F "u" [V 1, F "0" [], F "0" []]) (B TT)
-- r5 = R (F "u" [V 1, V 2, V 3]) (F "u" [V 1, F "+" [V 2, F "1" [] ], F "+" [V 3, V 2]]) (B (V 2 `Le` V 1))
-- r6 = R (F "u" [V 1, V 2, V 3]) (F "return" [V 3]) (N (B (V 2 `Le` V 1)))
-- sum2 = [r4, r5, r6]

-- !!CAUTION!! If we want to implement a SIMPLIFICATION-step on an equation
-- e : f(x1,...,xn) ≈  f'(a1,...,am)  [Ce]
-- with a rule
-- r : g(y1,...,yi) -> g'(b1,...,bj)  [Cr]
-- and a substitution tau such that
-- g(y1,...,yi)*tau ~ f(x1,...,xn)
-- Then before we can really do the SIMPLIFICATION we have to make sure that
-- Ce -> Cr*tau holds for all assignments of the variables x1,...,xn,a1,...,am
-- We need to check this with a SAT-solver
-- For the moment we are ignoring this condition (since it requires the connection between haskell and a SAT-solver) but eventually we have to fix this.

-- showsimp rs es = [(e,r,s) | e <- es, r <- rs such that we can (possibly) do SIMPLIFICATION with r on side s of equation e]
-- Example
-- eqs : {sum1(v1)≈sum2(v1) [True], sum1(v1)≈sum3(v1) [True]}
-- rs : {sum1(v2) -> return(0) [v2 <= 0],  sum2(v2) -> u(v2,0,0) [TT]}
--
-- e1 = E (F "sum1" [V 1]) (F "sum2" [V 1]) (B TT)
-- e2 = E (F "sum1" [V 1]) (F "sum3" [V 1]) (B TT)
-- eqs = [e1, e2]
-- r1 = R (F "sum1" [V 2]) (F "return" [F "0" []]) (B (V 2 `Le` F "0" []))
-- r2 = R (F "sum2"[V 2]) (F "u" [V 2, F "0" [], F "0" []]) (B TT)
-- rs = [r1, r2]
-- showsimp rs eqs =
-- [
-- (sum1(v1)~sum2(v1) [True],sum1(v2)->return(0) [v2<=0],Left) ,
-- (sum1(v1)~sum3(v1) [True],sum1(v2)->return(0) [v2<=0],Left) ,
-- (sum1(v1)~sum2(v1) [True],sum2(v2)->u(v2,0,0) [True],Right)
-- ]
-- Note that the first two options in this list are non-valid SIMPLIFICATION posibilities. As said: we really have to filter out the valid ones by comparing the constraints with a SAT-solver.
data Side = Left | Right deriving (Eq, Show)
showsimp :: Rules -> Equations -> [(Equation, Rule, Side)]
showsimp rs es = List.nub [(e,r, Left) | e <- es, r <- rs, getinstancesleft r e /= [] ] ++ [(e,r, Right) | e <- es, r <- rs, getinstancesleft r (reverseEQ e) /= []]

-- A proofstate as a tuple (E,H) where E is a set of equations and H is a set of induction hypothesis.
type Proofstate = (Equations, Hypothesis)

-- simplification :: Int -> Side -> Position -> Rule -> Proofstate -> Proofstate
-- simplification n s p r (eqs, hs) = the proofstate obtained by applying SIMPLIFICATION on position p on side s of the nth equation (counting starts at 0) in eqs with rule r.
-- simplification n s p r (eqs, hs)
-- s==Left = (,hs)
-- otherwise =
