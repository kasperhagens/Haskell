module Rules where
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import Terms ( Term(..), Varname, Substitution, appsub, Position, postoterm)
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
concatnoempties y = if all (\ls->not (null ls)) y then concat y else []

-- equalize is a helper function used to define getinstanceleft and getinstanceleftright (in the module Deductionsystem).
-- equalize t1 t2 = the 'substitution' s such that t1*s is possibly an instance of t2. The idea is to take for t1 the lefthand side of some rule r and for t2 the lefthand side of some equation on which we want to apply r. Whether t1*s is really an instance of t2 depends on the constraints in the rule where t1 occurs and the constraints in the equation where t2 occurs.
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

-- replaceNthElt xs i y = the list obtained obtained from xs by replacing the element occuring at position i by y. In case i<0 or or i>"last index of xs" then we return xs itself.
-- Example
-- replaceNthElt [0,0,0,0] 2 1 = [0,0,1,0]
replaceNthElt :: [a] -> Int -> a -> [a]
replaceNthElt [] i y = []
replaceNthElt (x:xs) i y
    | (i<0 || i> length(xs)) = x:xs
    | otherwise = if i==0 then y:xs else x:replaceNthElt xs (i-1) y

-- replace t1 p t2 = the term obtained by replacing the subterm of t1 ocurring at position p by the term t2. If p is a nonvalid position in t1 then t1 is returned.
-- Example
-- t1 = f(f(v1, v2), g(v1))
-- t2 = h(v1)
--
-- t1 = F "f" [F "f" [V 1, V 2], F "g" [V 1]]
-- t2 = F "h" [V 1]
-- then
-- replace t1 [0] t2 = f(h(v1),g(v1))
-- replace t1 [0,0] t2 = f(f(h(v1),v2),g(v1))
-- replace t1 [1,1] t2 = f(f(v1,v2),g(v1))
replace :: Term -> Position -> Term -> Term
replace t1 [] t2 = t2
replace (V x) p t = V x
replace (F f ts) (i:p) t
    | (i<0 || i>= length(ts)) = F f ts
    | otherwise = F f (replaceNthElt ts i (replace (ts!!i) p t))

-- applyrule r t p = the term obtained by applying rule r on the subterm of t occuring on  position p. If rule r is not applicable on the subterm of t occuring on position p then applyrule t p r = t.
-- WARNING!!
-- WE DO NOT CONSIDER THE CONSTRAINTS IN DETERMINING WHETHER RULE r IS REALLY APPLICABLE ON A SUBTERM OF t. IT COULD THEREFORE HAPPEN THAT applyrule WILL APPLY A RULE WHERE THIS IS NOT ALLOWED. THE IDEA IS THAT WE CHECK THE POSSIBILITY OF APPLYING RULE r BEFORE AVOKING THIS FUNCTION (WITH A SAT-SOLVER).
-- Example
-- t = F "f" [F "g" [F "h" [V 1]]]
-- r1 = R (F "g" [V 2]) (F "f" [V 2]) (B TT)
-- r2 = R (F "h" [V 2]) (F "f" [V 2]) (B TT)
-- r3 = R (F "f" [V 1]) (V 1) (B TT)
-- then
-- applyrule r1 t [0] = f(f(h(v1)))
-- applyrule r2 t [0,0] = f(g(f(v1)))
-- applyrule r3 t [] = g(h(v1))
applyrule :: Rule -> Term -> Position -> Term
applyrule r t p
    | postoterm t p /= Nothing =
    if (equalize (leftsideR r) (Maybe.fromJust (postoterm t p))) /= [] then (replace t p a) else t
    | otherwise = t
        where a = appsub (Map.fromList (equalize (leftsideR r) (Maybe.fromJust (postoterm t p)))) (rightsideR r)
