module Rules where
import qualified Data.Map as Map
import Terms
data Basicformula = Eq Term Term | Lt Term Term | Le Term Term deriving Eq
data Constraint = B Basicformula | Or Constraint Constraint | And Constraint Constraint deriving Eq
data Rule = R Term Term Constraint deriving Eq
