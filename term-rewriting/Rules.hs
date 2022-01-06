module Rules where
import qualified Data.Map as Map
import Terms ( Term(..), Varname, Substitution, appsub)
data Basicformula =   TT
                    | FF
                    | Eq Term Term
                    | Lt Term Term
                    | Le Term Term
                    | Gt Term Term
                    | Ge Term Term
                    deriving Eq
instance Show Basicformula where
    show TT = "True"
    show FF = "False"
    show (Eq t1 t2) = (show t1) ++ "=" ++ (show t2)
    show (Lt t1 t2) = (show t1) ++ "<" ++ (show t2)
    show (Le t1 t2) = (show t1) ++ "<="++ (show t2)
    show (Gt t1 t2) = (show t1) ++ ">" ++ (show t2)
    show (Ge t1 t2) = (show t1) ++ ">=" ++ (show t2)
appsubB :: Substitution -> Basicformula -> Basicformula
appsubB s (TT) = TT
appsubB s (FF) = FF
appsubB s (Eq t1 t2) = Eq (appsub s t1) (appsub s t2)
appsubB s (Lt t1 t2) = Lt (appsub s t1) (appsub s t2)
appsubB s (Le t1 t2) = Le (appsub s t1) (appsub s t2)
appsubB s (Gt t1 t2) = Gt (appsub s t1) (appsub s t2)
appsubB s (Ge t1 t2) = Ge (appsub s t1) (appsub s t2)

--Example: the constraint v1<=3 /\ v2=f(v1) is written as
--B ((V 1) `Le` (F "3" [])) `And` B((V 2) `Eq` (F "f" [V 1]))
--Example: the constraint v1<=3 /\ (v2=f(v1) \/ v2=f(f(v1)) is written as
-- B ((V 1) `Le` (F "3" [])) `And` (B((V 2) `Eq` (F "f" [V 1])) `Or` B((V 2) `Eq` (F "f"[F "f" [V 1]])))
data Constraint = B Basicformula
                | Or Constraint Constraint
                | And Constraint Constraint
                | N Constraint
                deriving Eq
instance Show Constraint where
    show (B f) = show f
    show (Or f1 f2) = "(" ++ (show f1) ++ ")" ++ " or " ++ "(" ++ (show f2) ++ ")"
    --The brackets around s and t are really necessary for expressions like s \/ (t /\ u)
    show (And f1 f2) = "("++(show f1) ++ ")"++ " and "++ "("++(show f2) ++")"
    show (N f) = "not("++(show f)++")"

appsubC :: Substitution -> Constraint -> Constraint
appsubC s (B f) = B (appsubB s f)
appsubC s (Or c1 c2) = Or (appsubC s c1) (appsubC s c2)
appsubC s (And c1 c2) = And (appsubC s c1) (appsubC s c2)
appsubC s (N c) = N (appsubC s c)

-- Example: the rule f(v1) -> g(v2) [v1 <= v2] is written as
-- R (F "f" [V 1]) (F "g" [V 2]) (B (V 1 `Le` V 2))
data Rule = R Term Term Constraint deriving Eq
instance Show Rule where
    show (R t1 t2 c) = (show t1) ++ "->" ++ (show t2) ++ " [" ++ (show c) ++ "]"

appsubR :: Substitution -> Rule -> Rule
appsubR s (R t1 t2 c) = R (appsub s t1) (appsub s t2) (appsubC s c)

leftsideR :: Rule -> Term
leftsideR (R t1 t2 c) = t1

rightsideR :: Rule -> Term
rightsideR (R t1 t2 c) = t2

-- concatnoempties y = concat y <=> all lists in y are non-empty
-- otherwise concatnoempties y = []
-- we use this function to define equalize
concatnoempties :: [[a]] -> [a]
concatnoempties y = if all (\ls->length(ls)>0) y then concat y else []

-- equalize is a helper function used to define getinstanceleft and getinstanceleftright (in the module Deductionsystem).
-- equalize t1 t2 = the 'substitution' s such that t1*s is possibly an instance of t2 (depending on the constraints in the rule where t1 occurs and the constraints in the equation where t2 occurs).
--
-- Example
-- t1 = F "f" [V 1, V 1]
-- t2 = F "f" [V 4, V 5]
-- equalize t1 t2 = [(1,v4),(1,v5)]
equalize :: Term -> Term -> [(Varname, Term)]
equalize t1 t2 = case t1 of
    (V x) -> case t2 of
        (V y) -> [(x, V y)]
        (F f ts) -> [(x, F f ts)]
    (F f ts) -> case t2 of
        (V y) ->[]
        (F g qs) -> if (f/=g || length(ts)/=length(qs)) then [] else (concatnoempties [ equalize a b | (a,b) <- (zip ts qs)])

-- replace t1 p t2 = the term obtained by replacing the subterm of t1 ocurring at position p by the term t2.
-- replace :: Term -> Position -> Term -> Term

-- applyrule r t p = the term obtained by applying rule r on the subterm of t occuring on  position p.
-- If rule r is not applicable on any subterm of t then we define applyrule t p r = t.
-- WARNING!! WE DO NOT CONSIDER THE CONSTRAINTS IN DETERMINING WHETHER RULE r IS APPLICABLE ON A SUBTERM OF t. HOWEVER, THE IDEA IS THAT WE CHECK THE POSSIBILITY OF APPLYING RULE r BEFORE WE AVOKE THIS FUNCTION.

-- applyrule :: Rule -> Term -> Position -> Term
-- applyrule r t p
-- | postoterm t p /= Nothing =
--    if (equalize (leftsideR r) (fromJust (postoterm t p))) /= [] then A else t
-- | otherwise = t
