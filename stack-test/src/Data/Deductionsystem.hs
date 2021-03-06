-- In this module we model the deduction system for constrainted program equations as described in the following paper
-- Verifying Procedural Programs via Constrained Rewriting Induction - Carsten Fuhs, Cynthia Kop, Naoki Nishida, page A:16 - A:20.
-- source: https://arxiv.org/abs/1409.0166

-- For the moment we slightly simplify the notion of a proofstate by ignoring the complete/incomplete flag. So we consider a proofstate as a tuple (E,H) where E is a set of equations and H is a set of rules called induction hypothesis.
-- The goal is to start with a set of equations E and, by using the interference rules, finding a deduction sequence (E,Ø) ⊢ ... ⊢ (Ø,H)
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
module Data.Deductionsystem (
    Proofstate,
    Side (..),
    Rules,
    Hypothesis,
    getinstanceleft,
    simplification,
    equationSide,
    expansionSingleRule,
    expansion,
    deletion,
    eqdeletion,
    generalization,
    moveToConstraint
    ) where
import qualified Data.Map as Map
import Data.Terms (
    Term(..),
    Varname,
    Substitution,
    Position,
    postoterm,
    appsub,
    equalize,
    subterms,
    concatnoempties,
    vars,
    mgu)
import Data.Constraints
import Data.Rules (
    Rule (..),
    leftsideR,
    rightsideR,
    appsubR,
    applyrule,
    constraintR,
    replace,
    replaceNthElt)
import Data.Side
import Data.List (delete, nub)
import Data.Maybe (fromJust, isNothing)
import Data.Equations
import Data.Zz
import Z3.Monad
import qualified Data.List as List
import Prelude hiding (Left, Right)
-- If we have an equation
-- e: f(x1,...,xn) ≈  f'(a1,...,am)  [Ce]
-- and a rule
-- r: g(y1,...,yi) -> g'(b1,...,bj)  [Cr]
-- then getinstanceleft r e may (possibily) give the substitution tau such that
-- g(y1,...,yi)*tau ~ f(x1,...,xn).
-- Note that we do not consider the righthand side of the equation e (we have to do that separately).
-- If such a tau does not exist then getinstance r e = [].
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
-- getinstancesleft r e = [(tau, t) | t is a subterm of the lefthand side of equation e such that the rule r*tau may be applicable to t]
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
-- sum1:
-- r1 : sum1(x) -> return(0)             [x<=0]
-- r2 : sum1(x) -> x + sum(x-1))         [x>=0]
-- r3 : x + return(y) -> return (x+y)    [True]
--
-- sum2:
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

-- constraintEqImpRule e r = True <=> The constraint of equation e implies the constraint of (an instance of) constraint of rule r
constraintEqImpRule :: Equation -> Rule -> IO Bool
constraintEqImpRule (E e1 e2 ce) (R r1 r2 cr) =
    if null tau
        then
            return False
        else
            uConstraintCheck (Or (N ce) (appsubC tau cr))
    where tau = getinstanceleft (R r1 r2 cr) (E e1 e2 ce)

-- A proofstate as a tuple (E,H) where E is a set of equations and H is a set of induction hypothesis.
type Proofstate = (Equations, Hypothesis)

-- SIMPLIFICATION
-- simplification n s p r (eqs, hs) = the proofstate obtained by applying SIMPLIFICATION on position p on side s of the nth equation (counting starts at 0) in eqs with rule r.
-- In case of invalid n, s, p or r implification n s p r (eqs, hs) = (eqs, hs)
--Example
-- eqs : {sum1(v1)≈sum2(v1) [True], sum1(v1)≈sum3(v1) [True]}
-- rs : {sum1(v2) -> return(0) [v2 <= 0],  sum2(v2) -> u(v2,0,0) [TT]}
-- ps = (eqs, [])
--
-- e0 = E (F "sum1" [V 1]) (F "sum2" [V 1]) (B TT)
-- e1 = E (F "sum1" [V 1]) (F "sum3" [V 1]) (B TT)
-- eqs = [e0, e1]
-- r0 = R (F "sum1" [V 2]) (F "return" [F "0" []]) (B (V 2 `Le` F "0" []))
-- r1 = R (F "sum2"[V 2]) (F "u" [V 2, F "0" [], F "0" []]) (B TT)
-- rs = [r0, r1]
-- ps = (eqs, [])
--
-- simplification 0 Left [] (rs!!0) ps
-- =
-- ([return(0)~sum2(v1) [True],sum1(v1)~sum3(v1) [True]],[])
--
--
-- simplification 1 Left [] (rs!!0) ps
-- =
-- ([sum1(v1)~sum2(v1) [True],return(0)~sum3(v1) [True]],[])
--
--
-- simplification 0 Right [] (rs!!1) ps
-- =
-- ([sum1(v1)~u(v1,0,0) [True],sum1(v1)~sum3(v1) [True]],[])
simplification :: Int -> Side -> Position -> Rule -> Proofstate -> IO Proofstate
simplification n s p r (eqs, hs) =
    if n<0 || n >= length eqs
        then
            return (eqs, hs)
        else do
            let u = postoterm (equationSide (eqs !! n) s) p
            if isNothing u
                then do
                    putStrLn (show (equationSide (eqs !! n) s) ++ " has no subterm on position " ++ show p ++ ". Proofstate has not been changed.")
                    return (eqs, hs)
                else do
                    let t = fromJust u
                        ce = constraintEQ (eqs !! n)
                        cr = constraintR r
                        tau = Map.fromList (equalize (rightsideR r) (equationSide (eqs!!n) (oppositeSide s)) ++ (equalize (leftsideR r) t))
                    checkconstraint <- uConstraintCheck (Or (N ce) (appsubC tau cr))
                    putStrLn ("Simplification-substitution: " ++ show tau)
                    if checkconstraint
                        then
                            case s of
                                Left -> return (replaceNthElt eqs n (E e1 e2 c), hs)
                                    where e1 = applyrule (appsubR tau r) (leftsideEQ (eqs!!n)) p
                                          e2 = rightsideEQ (eqs!!n)
                                          c = constraintEQ (eqs !! n)
                                Right -> return (replaceNthElt eqs n (E e1 e2 c), hs)
                                    where e1 = leftsideEQ (eqs!!n)
                                          e2 = applyrule (appsubR tau r) (rightsideEQ (eqs!!n)) p
                                          c = constraintEQ (eqs !! n)
                        else do
                            putStrLn ("Cannot do simplification: the substitution " ++ (show tau) ++ " applied to " ++ show r ++ " does not yield an applicable rule. Proofstate has not been changed. \n")
                            return (eqs, hs)

-- EXPANSION
-- expansion
-- expansion n s p rs (eqs, hs) = the proofstate obtained by applying EXPANSION on position p on side s of the nth equation (counting starts at 0) in eqs with respect to the rules in rs.

expansionSingleRule :: Int -> Side -> Position -> Rule -> Proofstate -> IO Proofstate
expansionSingleRule n s p (R l r psi) (eqs, hs) = do
    let E a b phi = eqs !! n
        u = postoterm (equationSide (E a b phi) s) p
    if isNothing u -- If u equals Nothing then side s of equation (E a b phi) has no subterm on position p.
        then do
            putStrLn (
                    show (equationSide (E a b phi) s)
                    ++
                    " has no subterm on position "
                    ++
                    show p
                    ++
                    ". Proofstate has not been changed."
                )
            return (eqs, hs)
        else do
            let tau = Map.fromList (equalize l (fromJust u))
            -- If tau is empty then we cannot apply the rule to the subterm on position p.
            if null tau
                then do
                    putStrLn ("You cannot use "
                        ++
                        show (R l r psi)
                        ++
                        " to expand "
                        ++
                        show (fromJust u)
                        ++
                        ". Proofstate has not been changed."
                        )
                    putStrLn " "
                    return (eqs, hs)
                else do
                    -- checkconstraint is true <=> phi implies psi*tau
                    -- if checkconstraint holds then we do not need to expand on this rule (since we can do a simplification step).
                    checkconstraint <- uConstraintCheck (Or (N phi) (appsubC tau psi))
                    if checkconstraint
                        then do
                            putStrLn (
                                "Proofstate has not been changed. "
                                ++
                                "You can do simplification with rule "
                                ++
                                show (R l r psi)
                                ++
                                " on "
                                ++
                                show (fromJust u)
                                )
                            putStrLn " "
                            return (eqs, hs)
                        else do
                            let adjustconstraint = if phi == B TT
                                                    then
                                                        appsubC tau psi
                                                    else
                                                        And (appsubC tau psi) phi
                                adjustequation = E a b adjustconstraint
                            checkadjustconstraint <- uConstraintCheck (Or (N adjustconstraint) (appsubC tau psi))
                        -- This check is really necessary: it can happen that the constraint phi is contradictory to tau*psi.
                            if checkadjustconstraint
                                then do
                                    let newequationleft = E (applyrule (R l r psi) a p) b adjustconstraint
                                        newequationright = E a (applyrule (R l r psi) b p) adjustconstraint
                                    if s==Left
                                        then do
                                            let neweqs = newequationleft:delete (E a b phi) eqs
                                                newhs = R a b phi:hs
                                            return (neweqs, newhs)
                                        else do
                                            let neweqs = newequationright:delete (E a b phi) eqs
                                                newhs = R b a phi:hs
                                            return (neweqs, newhs)
                                else
                                    return (eqs,hs)

expansion :: Int -> Side -> Position -> Rules -> Proofstate -> IO Proofstate
expansion n s p rs (eqs, hs) =
    if null rs
        then
            return (eqs, hs)
        else do
            (x,y) <- expansionSingleRule n s p (head rs) (eqs, hs)
            if (x,y) == (eqs, hs)
                then -- in this case we cannot do expansion with rule head rs, so we move on to the next rule in rs.
                    expansion n s p (tail rs) (eqs, hs)
                else
                    if (null (tail rs)) --If rs contains only one rule then we return the same as expansionSingleRule
                        then
                             return (x,y)
                        else do
                            (remeqs, remhyps) <- expansion n s p (tail rs) (eqs, hs)
                            let neweq = head x
                                newhyp = head y
                                neweqs = neweq : remeqs
                                newhs = nub (newhyp : remhyps)
                                -- If we don't use nub we may get multiple occurrences of a single hypothesis (one for each applicable rule).
                                newpfst = (delete (eqs !! n) neweqs, newhs)
                            return newpfst

deletion :: Int -> Proofstate -> IO Proofstate
deletion n (eqs,hs) = do
    let e = eqs !! n
        cstr = constraintEQ e
    res <- evalZ3 (checkConstraint cstr)
    if leftsideEQ e == rightsideEQ e || res == Unsat
        then do
            let neweqs = filter (/= e) eqs
            return (neweqs, hs)
        else do
            putStrLn ("You cannot delete " ++ show e ++ ". Proofstate has not been changed.")
            putStrLn " "
            return (eqs, hs)

eqdeletion :: Int -> Int -> [Position] -> [Position] -> Proofstate -> IO Proofstate
-- n: the equation on which eqdeletion is applied
-- h: the number of holes in the context C
-- pl: the list of positions of holes on the left-side of the nth equation
-- pr: the list of positions of holes on the right-side of the nth equation
eqdeletion n h pl pr (eqs,hs) = do
    let E a b phi = eqs !! n
        tsleft = map fromJust (filter (/= Nothing ) (map (postoterm a) pl))
        tsright = map fromJust (filter (/= Nothing) (map (postoterm b) pr))
    if (length tsleft /= h || length tsright /= h)
        then do
            putStrLn "Input contained invalid positions. Proofstate has not been changed."
            putStrLn " "
            return (eqs, hs)
        else do
            let uneqs = zipWith ( \x y -> N(B(x `Eq` y)) ) tsleft tsright
                addconstraint = foldr And (B(TT)) uneqs --conjunct all the constraints in uneqs
                neweq = E a b (And phi addconstraint)
                neweqs = replaceNthElt eqs n neweq
            return (neweqs, hs)

-- Generalization n p (eqs, hs) will remove the subconstraint occuring on position p of the constraint of the nth equation in eqs.
generalization :: Int -> [Side] -> Proofstate -> IO Proofstate
generalization n p (eqs, hs) = do
    let E a b c = eqs !! n
        newc = removeCstrAtPos c p
        neweq = E a b newc
    return (replaceNthElt eqs n neweq, hs)


moveToConstraint :: Int -> Side -> Position -> Proofstate -> IO Proofstate
moveToConstraint n s p (eqs, hs) = do
    let E a b phi = eqs !! n
        u = postoterm (equationSide (E a b phi) s) p
    if isNothing u -- If u equals Nothing then side s of equation (E a b phi) has no subterm on position p.
        then do
            putStrLn (
                    show (equationSide (E a b phi) s)
                    ++
                    " has no subterm on position "
                    ++
                    show p
                    ++
                    ". Proofstate has not been changed."
                )
            return (eqs, hs)
        else do
            let t = fromJust u
                newvarname = maximum (vars a ++ vars b) + 1
                newvar = V newvarname
                addconstraint = B (newvar `Eq` t)
                neweq =
                    if (s == Left)
                        then
                            E (replace a p newvar) b (addconstraint `And` phi)
                        else
                            E a (replace b p newvar) (addconstraint `And` phi)
            return (replaceNthElt eqs n neweq, hs)
