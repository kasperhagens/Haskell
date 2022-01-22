module Data.Rules where
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import Data.Terms ( Term(..),
                    Varname,
                    Substitution,
                    Position,
                    appsub,
                    postoterm,
                    equalize)
import Data.Constraints

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

-- replaceNthElt is a helper function used to define replace.
-- replaceNthElt xs i y = the list obtained obtained from xs by replacing the element occuring at position i by y. In case i<0 or or i>"last index of xs" we output xs itself.
-- Example
-- replaceNthElt [0,0,0,0] 2 1 = [0,0,1,0]
replaceNthElt :: [a] -> Int -> a -> [a]
replaceNthElt [] i y = []
replaceNthElt (x:xs) i y
    | (i<0 || i> length(xs)) = x:xs
    | otherwise = if i==0 then y:xs else x:replaceNthElt xs (i-1) y

-- replace t1 p t2 = the term obtained by replacing the subterm of t1 ocurring at position p by the term t2. If p is a nonvalid position in t1 then we act as identity on t1.
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
-- !!WARNING!!
-- WE DO NOT CONSIDER THE CONSTRAINTS TO DETERMINE WHETHER RULE r IS REALLY APPLICABLE ON A SUBTERM OF t. IT COULD THEREFORE HAPPEN THAT applyrule WILL APPLY A RULE WHERE THIS IS NOT ALLOWED. THE IDEA IS THAT WE CHECK THE POSSIBILITY OF APPLYING RULE r BEFORE AVOKING THIS FUNCTION.
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
    if equalize (leftsideR r) (Maybe.fromJust (postoterm t p)) /= []
        then
            replace t p a
        else t
    | otherwise = t
        where a = appsub (Map.fromList (equalize (leftsideR r) (Maybe.fromJust (postoterm t p)))) (rightsideR r)
