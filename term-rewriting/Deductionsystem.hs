-- In this module we model the deduction system for constrainted program equations as described in the following paper
-- Verifying Procedural Programs via Constrained Rewriting Induction - Carsten Fuhs, Cynthia Kop, Naoki Nishida, page A:16 - A:20.
-- source: https://arxiv.org/abs/1409.0166

-- For the moment we slightly simplify the notion of a proofstate by ignoring the complete/incomplete flag. So we consider a proofstate as a tuple (E,H) where E is a set of equations and H is a set of rules called induction hypothesis.
-- The goal is to start with a set of equations E and, by using the interference rules, finding a deduction sequence (E,Ø) ⊢ ... ⊢ (Ø,H)
module Deductionsystem where
import qualified Data.Map as Map
import Terms (Term(..), Varname, Substitution, appsub)
import Rules (Basicformula(..), Constraint(..), Rule (..), leftsideR, rightsideR, appsubC, appsubR)
import Equations
type Hypothesis = [Rule]
-- Example (from the seminar-document, page 102, slide 30)
-- sum1 = [R (F "sum1" [V 1]) (F "0" []) (B (V 1 `Le` F "0" [])), R (F "sum1" [V 1]) (F "+" [V 1, F "sum1" [F "-" [V 1, F "1" []]]]) (B (V 1 `Ge` F "0" [])), R (F "+" [V 1, F "return" [V 2]]) (F "return"[F "+" [V 1, V 2]]) (B TT)]
--
-- sum2 = [R (F "sum2"[V 1]) (F "u" [V 1, F "0" [], F "0" []]) (B TT), R (F "u" [V 1, V 2, V 3]) (F "u" [V 1, F "+" [V 2, F "1" [] ], F "+" [V 3, V 2]]) (B (V 2 `Le` V 1)) ]
type Rules = [Rule]
type Equations = [Equation]
type Proofstate = (Equations, Rules)
