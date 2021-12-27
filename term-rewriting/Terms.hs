
module Terms (Term(..), postoterm, positions, subterms, issubterm, varin, vars, funcs, substitute, appsub, mgu) where
import qualified Data.Map as Map
import qualified Data.List as List
import Distribution.Simple.Utils (xargs)
type Funcname = String
type Varname = Int
data Term = V Varname| F Funcname [Term] deriving (Eq)

instance Show Term where
    show = remsuperflcommas.convtoStr

-- convtoStr takes a string and concerts it to a string. Note that convtoStr t contains additional superfluous commas for any non-variable term t. For example convtoStr (F "f" [V "x"]) = f(x,). Therefore, we wrote a function remsuperflcommas to remove the superfluous commas.
convtoStr :: Term -> String
convtoStr (V x) = show x
convtoStr (F f xs) = f++"(" ++ (concat [convtoStr x ++ "," | x<- xs]) ++ ")"

remsuperflcommas::String ->String
remsuperflcommas l = case l of
    (x:y:ys) -> if x==',' && y==')' then y:remsuperflcommas ys else x:remsuperflcommas (y:ys)
    (x:xs) -> x:xs
    [] -> []

type Position = [Int]
postoterm :: Position -> Term -> Maybe Term
postoterm [] (V x) = Just (V x)
postoterm (y:ys) (V x) = Nothing
postoterm [] (F f l) = Just (F f l)
postoterm (x:xs) (F c [])= Just (F c [])
postoterm (x:xs) (F f l)= postoterm xs (l!!x)

--pos is a helper function used for defining the function positions
pos :: Term -> [Position]
pos (V x) = [[]]
pos (F c []) = [[]]
pos (F f l) = [i:p | i <- [0..length l-1], p<-pos(l!!i)]

positions :: Term -> [Position]
positions t = List.nub [p | v<-pos t, p <- List.inits v]

--maysubterms is a helper function used to define the function subterms
maysubterms :: Term -> [Maybe Term]
maysubterms t = List.nub [postoterm p t | p <- positions t ]

subterms :: Term -> [Term]
subterms t = [s | Just s <- maysubterms t]

issubterm :: Term -> Term -> Bool
issubterm s t = s `elem` (subterms t)
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

-- getvars t shows a list of variable names occuring in t. Similarly, showfuncs t shows the list of functionsymbols occuring in t.
-- Example
-- showvars(F "f" [F "g" [V 1], F "h" [V 2, V 3]]) = [1,2,3]
-- showfuncs(F "f" [F "g" [V 1], F "h" [V 2, V 3]]) = [1,2,3]
vars :: Term -> [Varname]
vars (V x) = [x]
vars (F f l) = concat [vars t | t<- l]

funcs :: Term -> [Funcname]
funcs (V x) = []
funcs (F f l) = f : concat [funcs t | t<- l]

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
appsub s (V x) = case Map.lookup x s of
    Nothing  -> V x
    Just y -> y
appsub s (F f l) = F f [appsub s t | t <- l]

--transition takes a pair (P,S) where P is a problem-set of equalities, 'solution-set' S (S is a substitution) and returns a pair (P',S') of a new problem-set and solution-set.
type EQ = [(Term, Term)]
transition :: (EQ, EQ) -> (EQ, EQ)
transition ([], s) = ([],s)
transition ((V x, V y) : ls, s)
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

-- eqtosub takes an equation and turns it into a substitution. It only makes sense in case the equation really represents a substitution but for our application this will always be true (we don't export this function anyway). For example
-- eqtosub [(V 1, V 2), (V 3, F "f" [V 2])] = [(1,2),(3,f(2))]
eqtosub :: EQ -> Substitution
eqtosub x = Map.fromList [processpair (a,b) | (a,b) <- x]

--mgu u v calculates the most general unifier of u and v
mgu :: Term -> Term -> Substitution
mgu u v = (eqtosub . proceed) ([(u,v)],[])

-- Example 1 (from syllabus automated reasoning)
-- s = F "P" [F "f" [V 1], V 2]
-- t = F "P" [V 3, F "g" [V 4]]
-- mgu st = fromList [(2,g(4)),(3,f(1))]

-- Example 2 (from syllabus automated reasoning)
-- s = F "P" [F "f" [V 1], V 1]
-- t = F "P" [V 2, F "g" [V 2]]
-- mgu s t = fromList []

-- Example 3: Problem 4 of the Exam Automated Reasoning 2016
-- s = F "f" [F "f" [F "g" [V 3], V 3], F "f" [V 1, V 3]]
-- t = F "f" [V 2, F "f" [F "f" [V 2, F "g" [V 2]], F "g" [V 4]]]
-- mgu s t = fromList [(1,f(f(g(g(4)),g(4)),g(f(g(g(4)),g(4))))),(2,f(g(g(4)),g(4))),(3,g(4))]

--Example 4: from https://www.cs.toronto.edu/~sheila/384/w11/Lectures/csc384w11-KR-tutorial.pdf
-- !!! CAUTION: THE SOLUTION ON THE SLIDES IS WRONG. THE ALGORITHM WILL CALCULATE THE CORRECT MGU!!!
-- s = F "p" [F "a" [], V 1, F "h" [F "g" [V 3]]]
-- t = F "p" [V 3, F "h" [V 2], F "h" [V 2]]
-- mgu s t = fromList [(1,h(g(a()))),(2,g(a())),(3,a())]
