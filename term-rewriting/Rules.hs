module Rules where
import qualified Data.Map as Map
import Terms ( Term(..), Varname, Substitution, appsub)
data Basicformula = TT | FF | Eq Term Term | Lt Term Term | Le Term Term deriving Eq
instance Show Basicformula where
    show (Eq t1 t2) = (show t1) ++ "=" ++ (show t2)
    show (Lt t1 t2) = (show t1) ++ "<" ++ (show t2)
    show (Le t1 t2) = (show t1) ++ "<="++ (show t2)
    show TT = "True"
    show FF = "False"
appsubB :: Substitution -> Basicformula -> Basicformula
appsubB s (TT) = TT
appsubB s (FF) = FF
appsubB s (Eq t1 t2) = Eq (appsub s t1) (appsub s t2)
appsubB s (Lt t1 t2) = Lt (appsub s t1) (appsub s t2)
appsubB s (Le t1 t2) = Le (appsub s t1) (appsub s t2)

--Example: the constraint v1<=3 /\ v2=f(v1) is written as
--B ((V 1) `Le` (F "3" [])) `And` B((V 2) `Eq` (F "f" [V 1]))
--Example: the constraint v1<=3 /\ (v2=f(v1) \/ v2=f(f(v1)) is written as
-- B ((V 1) `Le` (F "3" [])) `And` (B((V 2) `Eq` (F "f" [V 1])) `Or` B((V 2) `Eq` (F "f"[F "f" [V 1]])))
data Constraint = B Basicformula | Or Constraint Constraint | And Constraint Constraint deriving Eq
instance Show Constraint where
    show (B f) = show f
    show (Or f1 f2) = "(" ++ (show f1) ++ ")" ++ " or " ++ "(" ++ (show f2) ++ ")"
    --Note that the brackets around s and t are really necessary for visualizing expressions like s \/ (t /\ u)
    show (And f1 f2) = "("++(show f1) ++ ")"++ " and "++ "("++(show f2) ++")"

appsubC :: Substitution -> Constraint -> Constraint
appsubC s (B f) = B (appsubB s f)
appsubC s (Or c1 c2) = Or (appsubC s c1) (appsubC s c2)
appsubC s (And c1 c2) = And (appsubC s c1) (appsubC s c2)

-- Example: the rule f(v1) -> g(v2) [v1 <= v2] is written as
-- R (F "f" [V 1]) (F "g" [V 2]) (B (V 1 `Le` V 2))
data Rule = R Term Term Constraint deriving Eq
instance Show Rule where
    show (R t1 t2 c) = (show t1) ++ "->" ++ (show t2) ++ " [" ++ (show c) ++ "]"

appsubR :: Substitution -> Rule -> Rule
appsubR s (R t1 t2 c) = R (appsub s t1) (appsub s t2) (appsubC s c)

leftsideR :: Rule -> Term
leftsideR (R t1 t2 c) = t1
