-- In this module we model the constrainted programm equations as described in the following paper
-- Verifying Procedural Programs via Constrained Rewriting Induction - Carsten Fuhs, Cynthia Kop, Naoki Nishida, page A:15, section 4.2, definition 4.3
-- source: https://arxiv.org/abs/1409.0166
module Data.Equations where
import qualified Data.Map as Map
import Data.Terms (Term(..), Varname, Substitution, appsub)
import Data.Rules (Rule (..), leftsideR, rightsideR, appsubR)
import Data.Constraints

--Example of equation
--E (F "f" [V 1]) (F "g" [V 2]) (B (V 1 `Le` V 2))
data Equation = E Term Term Constraint deriving Eq
instance Show Equation where
    show (E t1 t2 c) = (show t1) ++ "~" ++ (show t2) ++ " [" ++ (show c)++"]"

leftsideEQ :: Equation -> Term
leftsideEQ (E t1 t2 c) = t1

rightsideEQ :: Equation -> Term
rightsideEQ (E t1 t2 c) = t2

constraintEQ :: Equation -> Constraint
constraintEQ (E t1 t2 c) = c

reverseEQ :: Equation -> Equation
reverseEQ (E t1 t2 c) = E t2 t1 c

appsubE :: Substitution -> Equation -> Equation
appsubE s (E t1 t2 c) = E (appsub s t1) (appsub s t2) (appsubC s c)
