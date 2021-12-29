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

data Rule = R Term Term Constraint deriving Eq
leftside :: Rule -> Term
leftside (R s t c) = s

-- If we have two rules
-- r1 : f(x1,...,xn) -> f'(a1,...,am)  [c1]
-- and
-- r2 : g(y1,...,yi) -> g'(b1,...,bj)  [c2]
-- then identify r1 r2 will give the 'substitution' tau such that f(x1,...,xn)*tau = g(y1,...,yi)
-- Note, however, that this substitution is not necessarily a mapping
-- For example consider
-- r1 : f(x,x) -> g(y)  [true]
-- r2 : f(a,b) -> g(y)  [a=b]
-- then identify r1 r2 = [(x, V a), (x, V b)]
--
-- r1 = (F "f" [V 1, V 1]) (F "g" [V 2]) (B TT)
-- r2 = (F "f" [V 4, V 5]) (F "g" [V 2]) (B (V4 `Eq` V5))
equalize :: Term -> Term -> [(Varname, Term)]
equalize s t = case s of
    (V x) -> case t of
        (V y) -> [(x, V y)]
        (F f l) -> [(x, F f l)]
    (F f l) -> case t of
        (V y) ->[]
        (F g m) -> if (f/=g || length(l)/=length(m)) then [] else (concat [ equalize a b | (a,b) <- (zip l m)])

getinstance :: Rule -> Rule -> [(Varname, Term)]
getinstance r1 r2 = equalize (leftside r1) (leftside r2)
