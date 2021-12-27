module Rules where
import qualified Data.Map as Map
import Terms
-- Note: we introduce a separate type constructor for constants instead of considering a constant as a 0-ary functionsymbol.
data Basicformula = Eq Term Term | Lt Term Term | Le Term Term deriving Eq
data Constraint = B Basicformula | Or Constraint Constraint | And Constraint Constraint deriving Eq
data Rule = Rule Term Term Constraint deriving Eq
