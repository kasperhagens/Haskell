-- In this module we model the deduction system for constrainted program equations as described in the following paper
-- Verifying Procedural Programs via Constrained Rewriting Induction - Carsten Fuhs, Cynthia Kop, Naoki Nishida, page A:16 - A:20.
-- source: https://arxiv.org/abs/1409.0166

-- For the moment we slightly simplify the notion of a proofstate by ignoring the complete/incomplete flag. So we consider a proofstate as a tuple (E,H) where E is a set of equations and H is a set of rules.
-- The goal is to start with a set of equations E and, by using the interference rules, finding a deduction sequence (E,Ø) ⊢ ... ⊢ (Ø,H)
module Deductionsystem where
import qualified Data.Map as Map
import Terms (Term(..), Varname, Substitution, appsub)
import Rules (Basicformula(..), Constraint(..), Rule (..), leftsideR, rightsideR, appsubC, appsubR)
import Equations
type Rules = [Rule]
type Equations = [Equation]
type Proofstate = (Equations, Rules)
