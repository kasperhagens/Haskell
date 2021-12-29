module Rules where
import qualified Data.Map as Map
import Terms ( Term(..), Varname )
data Basicformula = TT | FF | Eq Term Term | Lt Term Term | Le Term Term deriving Eq
instance Show Basicformula where
    show (Eq s t) = (show s) ++ "=" ++ (show t)
    show (Lt s t) = (show s) ++ "<" ++ (show t)
    show (Le s t) = (show s) ++ "<="++ (show t)
    show TT = "True"
    show FF = "False"

data Constraint = B Basicformula | Or Constraint Constraint | And Constraint Constraint deriving Eq
instance Show Constraint where
    show (B s) = show s
    show (Or s t) = "(" ++ (show s) ++ ")" ++ " or " ++ "(" ++ (show t) ++ ")"
    -- Note that the brackets around s and t are really necessary for visualizing expressions like s \/ (t /\ u)
    show (And s t) = "("++(show s) ++ ")"++ " and "++ "("++(show t) ++")"
--Example: x<=3 /\ y=f(x) is written as
--B ((V 1) `Le` (F "3" [])) `And` B((V 2) `Eq` (F "f" [V 1]))
--Example: x<=3 /\ (y=f(x) \/ y=f(f(x)) is written as
-- B ((V 1) `Le` (F "3" [])) `And` (B((V 2) `Eq` (F "f" [V 1])) `Or` B((V 2) `Eq` (F "f"[F "f" [V 1]])))

-- Example: the rule f(x) -> g(y) [x <= y] is written as
-- R (F "f" [V 1]) (F "g" [V 2]) (B (V 1 `Le` V 2))
data Rule = R Term Term Constraint deriving Eq
instance Show Rule where
    show (R t1 t2 c) = (show t1) ++ "->" ++ (show t2) ++ " [" ++ (show c) ++ "]"

leftsideR :: Rule -> Term
leftsideR (R s t c) = s
