module Rules where
import qualified Data.Map as Map
import Terms ( Term(..), Varname )
data Basicformula = Eq Term Term | Lt Term Term | Le Term Term deriving Eq
instance Show Basicformula where
    show (Eq s t) = (show s) ++ "=" ++ (show t)
    show (Lt s t) = (show s) ++ "<" ++ (show t)
    show (Le s t) = (show s) ++ "<="++ (show t)
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

data Rule = R Term Term Constraint deriving Eq
leftside :: Rule -> Term
leftside (R s t c) = s

-- If we have two terms s = f(x1,...,xn) and t = g(y1,...,ym) then inst r1 r2 will give the substitution such that
inst :: Term -> Term -> [(Varname, Term)]
inst s t = case s of
    (V x) -> case t of
        (V y) -> [(x, V y)]
        (F f l) -> [(x, F f l)]
    (F f l) -> case t of
        (V y) ->[]
        (F g m) -> if (f/=g || length(l)/=length(m)) then [] else (concat [ inst a b | (a,b) <- (zip l m)])

