{-# LANGUAGE TypeApplications #-}
module Terms where
import qualified Data.Map as Map
type Funcname = String
type Varname = Int
data Term = V Varname| F Funcname [Term] deriving (Eq)

instance Show Term where
    show = remsuperflcommas.convtoStr

-- convtoStr takes a string and concerts it to a string. Note that convtoStr t contains additional superfluous commas for any non-variable term t. For example convtoStr (F "f" [V "x"]) = f(x,). We write a function remsuperflcommas to remove the superfluous commas
convtoStr :: Term -> String
convtoStr (V x) = show x
convtoStr (F f xs) = f++"(" ++ (concat [convtoStr x ++ "," | x<- xs]) ++ ")"

remsuperflcommas::String ->String
remsuperflcommas l = case l of
    (x:y:ys) -> if x==',' && y==')' then y:remsuperflcommas ys else x:remsuperflcommas (y:ys)
    (x:xs) -> x:xs
    [] -> []

--Map a b is the type of mappings from type a to type b
--You can make a mapping from a list with the function fromList.
--For example, Map.fromList [((1,2),(3,4),(5,6))] creates a mapping
--{1|->2, 3|->4, 5|->6}
--Conversely you can turn a mapping into a list of tuples by using the function toList. For example
-- Map.toList (Map.fromList [((1,2),(3,4),(5,6))])=[((1,2),(3,4),(5,6))]
type Substitution = Map.Map Varname Term

-- varin x t checks whether the variablename x occurs in term t
-- Example
-- varin 1 (F "f" [F "g" [V 1], F "h" [V 2, V 3]]) = True
varin :: Varname -> Term -> Bool
varin x (V y)
   | x==y = True
   | otherwise = False
varin x (F f l) = or [varin x t | t <- l]

-- showvars t shows a list of variable names occuring in t
-- Example
-- showvars(F "f" [F "g" [V 1], F "h" [V 2, V 3]]) = [1,2,3]
showvars :: Term -> [Varname]
showvars (V x) = [x]
showvars (F f l) = concat [showvars t | t<- l]


-- substitute x s t equals t[x:=s]
-- Example
-- substitute 3 (F "f" [V 1]) (F "f" [F "g" [V 1], F "h" [V 2, V 3]])
-- =
-- F "f" [F "g" [V 1],F "h" [V 2,F "f" [V 1]]]
substitute :: Varname -> Term -> Term -> Term
substitute x s (V y)
    | x==y = s -- y[x:=s]=s if x=y
    | otherwise = V y --y[x:=s]=y if x/=y
substitute x s (F f l) = F f [substitute x s t | t <- l]

-- appsub s t = the term obtained by applying substitution s on term t
-- Example
-- s = Map.fromList [(1, V 2), (2, F "k" [V 4])]
-- t = F "f" [F "g" [V 1], F "h" [V 2, V 3]]
-- appsub s t = f(g(2),h(k(4),3))
appsub :: Substitution -> Term -> Term
appsub s (V x) = case (Map.lookup x s) of
    Nothing  -> V x
    Just y -> y
appsub s (F f l) = F f [appsub s t | t <- l]

--transition takes a pair (P,S) where P is a problem-set of equalities, 'solution-set' S (S is a substitution) and returns a pair (P',S') of a new problem-set and solution-set.
type EQ = [(Term, Term)]
transition :: (EQ, EQ) -> (EQ, EQ)
transition ([], s) = ([],s)
transition (((V x), V y) : ls, s)
    | x == y = (ls, s)
    | otherwise = ([(appsub sub u, appsub sub v) | (u,v) <- ls], (V x,V y):[(appsub sub q, appsub sub r) | (q,r) <- s])
    where sub = Map.fromList [(x,V y)]
transition ((V x, y@(F _ _)) : ls, s)
    | varin x y = ([], [])
    | otherwise = ([(appsub sub u, appsub sub v) | (u,v) <- ls], (V x,y):[(appsub sub q, appsub sub r) | (q,r) <- s])
    where sub = Map.fromList [(x, y)]
transition ((y@(F _ _), V x) : ls, s)
    | varin x y = ([], [])
    | otherwise = ([(appsub sub u, appsub sub v) | (u,v) <- ls], (V x,y):[(appsub sub q, appsub sub r) | (q,r) <- s])
    where sub = Map.fromList [(x, y)]
transition ((x@(F f xs), y@(F g ys)) : ls, s)
    | f/=g = ([],[])
    | otherwise = (zip xs ys ++ ls, s)

--proceed takes a pair (P,S) where P is a problem-set and S is a Solution-set and applies a transition-step as long as possible (i.e. as long as P is non-empty)
proceed :: (EQ, EQ) -> EQ
proceed (p,s)
    | null p = s
    | otherwise = proceed (transition (p, s))

processpair :: (Term, Term) -> (Varname, Term)
processpair (V x, V y) = (x, V y)
processpair (V x, y@(F _ _)) = (x, y)
processpair (x, y) = (-1, V (-1)) -- set some default value when applied to nonsense

-- eqtosub takes an equation and turns it into a substitution, for example
-- eqtosub [(V 1, V 2), (V 3, F "f" [V 2])] = [(1,2),(3,f(2))]
eqtosub :: EQ -> Substitution
eqtosub x = Map.fromList [processpair (a,b) | (a,b) <- x]

--mgu u v calculates the most general unifier of u and v
mgu :: Term -> Term -> Substitution
mgu u v = (eqtosub . reverse . proceed) ([(u,v)],[])

-- Example 1 (from syllabus automated reasoning)
-- s= F "P" [F "f" [V 1], V 2]
-- t= F "P" [V 3, F "g" [V 4]]
-- mgu st
-- =
--
