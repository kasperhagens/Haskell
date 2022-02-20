
module Data.Terms (
    Term(..),
    Substitution,
    Varname,
    Position,
    postoterm,
    positions,
    subterms,
    issubterm,
    varin,
    vars,
    funcs,
    substitute,
    appsub,
    mgu,
    equalize,
    concatnoempties
) where

import qualified Data.Map as Map
import qualified Data.List as List
type Funcname = String
type Varname = Int
data Term = V Varname| F Funcname [Term] deriving (Eq)

isVar :: Term -> Bool
isVar (V x) = True
isVar (F f l) = False

-- convtoStr is used for defining instance Show of Term. Note that convtoStr t contains additional superfluous commas for any non-variable term t. For example convtoStr (F "f" [V "V 1"]) = f(v1,). Therefore, we wrote a function remsuperflcommas to remove the superfluous commas.
convtoStr :: Term -> String
convtoStr (V x) = "x" ++ show x
convtoStr (F "+" [t1, t2]) = convtoStr t1 ++ "+" ++ convtoStr t2

convtoStr (F "-" [t1, t2]) =
    let o1 = convtoStr t1 ++ "-" ++ convtoStr t2
        o2 = convtoStr t1 ++ "-" ++ "(" ++ convtoStr t2 ++ ")"
    in
    if isVar t2
        then
            o1
        else
            let F f l = t2 in
            if f == "+" || f == "-"
                then
                    o2
                else
                    o1

convtoStr (F "*" [t1, t2]) =
    let o1 = convtoStr t1 ++ "*" ++ convtoStr t2
        o2 = convtoStr t1 ++ "*" ++ "(" ++ convtoStr t2 ++ ")"
        o3 = "(" ++ convtoStr t1 ++ ")"++ "*" ++ convtoStr t2
        o4 = "(" ++ convtoStr t1 ++ ")"++ "*" ++ "(" ++ convtoStr t2 ++ ")"
    in
    if isVar t1
        then
            if isVar t2
                then
                    o1
                else
                    let F f l = t2 in
                    if f == "+" || f == "-"
                        then
                            o2
                        else
                            o1
        else
            let F f l = t1 in
            if f == "+" || f == "-"
                then
                    if isVar t2
                        then
                            o3
                        else
                            let F g k = t2 in
                            if f == "+" || f == "-"
                                then
                                    o4
                                else
                                    o3
                else
                    if isVar t2
                        then
                            o1
                        else
                            let F g k = t2 in
                            if f == "+" || f == "-"
                                then
                                    o2
                                else
                                    o1

convtoStr (F "/" [t1, t2]) =

    let o1 = convtoStr t1 ++ "/" ++ convtoStr t2
        o2 = convtoStr t1 ++ "/" ++ "(" ++ convtoStr t2 ++ ")"
        o3 = "(" ++ convtoStr t1 ++ ")"++ "/" ++ convtoStr t2
        o4 = "(" ++ convtoStr t1 ++ ")"++ "/" ++ "(" ++ convtoStr t2 ++ ")"
    in
    if isVar t1
        then
            if isVar t2
                then
                    o1
                else
                    let F f l = t2 in
                    if f == "+" || f == "-"
                        then
                            o2
                        else
                            o1
        else
            let F f l = t1 in
            if f == "+" || f == "-"
                then
                    if isVar t2
                        then
                            o3
                        else
                            let F g k = t2 in
                            if f == "+" || f == "-"
                                then
                                    o4
                                else
                                    o3
                else
                    if isVar t2
                        then
                            o1
                        else
                            let F g k = t2 in
                            if f == "+" || f == "-"
                                then
                                    o2
                                else
                                    o1
convtoStr (F f []) = f
convtoStr (F f ts) = f ++ "(" ++ (concat [convtoStr t ++ "," | t <- ts]) ++ ")"

remsuperflcommas :: String -> String
remsuperflcommas l = case l of
    (x:y:ys) -> if x==',' && y==')' then y:remsuperflcommas ys else x:remsuperflcommas (y:ys)
    (x:xs) -> x:xs
    [] -> []

instance Show Term where
    show = remsuperflcommas.convtoStr

type Position = [Int]
-- postoterm t p = maybe the subterm of t occuring on position p (depending on whether p represents a valid position in t).
postoterm :: Term -> Position -> Maybe Term
postoterm (V x) [] = Just (V x)
postoterm (V x) (y:ys) = Nothing
postoterm (F f ts) [] = Just (F f ts)
postoterm (F c []) (x:xs) = Just (F c [])
postoterm (F f ts) (x:xs) = postoterm (ts!!x) xs

-- pos is a helper function used for defining positions
pos :: Term -> [Position]
pos (V x) = [[]]
pos (F c []) = [[]]
pos (F f ts) = [i:p | i <- [0..length ts-1], p <- pos(ts!!i)]

-- positions t = [positions of all subterms in t]
--
-- Example
-- positions (F "f" [F "g" [V 1], F "h" [V 2, V 3]])
-- =
-- [[],[0],[0,0],[1],[1,0],[1,1]]
positions :: Term -> [Position]
positions t = List.nub [p | x <- pos t, p <- List.inits x]

-- maysubterms is a helper function used to define the function subterms
-- The function nub from Data.List removes duplicates elements from a list
maysubterms :: Term -> [Maybe Term]
maysubterms t = List.nub [postoterm t p | p <- positions t ]

-- subterms t = [subterms of t]
subterms :: Term -> [Term]
subterms t = [s | Just s <- maysubterms t]

-- issubterm t1 t2 equals True <=> t1 is a subterm of t2
issubterm :: Term -> Term -> Bool
issubterm t1 t2 = t1 `elem` (subterms t2)
--Map a b is the type of mappings from type a to type b
--You can make a mapping from a list with the function fromList.
--For example, Map.fromList [((1,2),(3,4),(5,6))] creates a mapping
--{1|->2, 3|->4, 5|->6}
--Conversely you can turn a mapping into a list of tuples by using the function toList. For example
-- Map.toList (Map.fromList [((1,2),(3,4),(5,6))])=[((1,2),(3,4),(5,6))]
type Substitution = Map.Map Varname Term

-- varin x t checks whether variablename x occurs in term t
--
-- Example
-- varin 1 (F "f" [F "g" [V 1], F "h" [V 2, V 3]]) = True
varin :: Varname -> Term -> Bool
varin x (V y)
   | x==y = True
   | otherwise = False
varin x (F f ts) = or [varin x t | t <- ts]

-- vars t = [variable names occuring in t]
-- funcs t = [functionsymbols occuring in t]
--
-- Example
-- vars(F "f" [F "g" [V 1], F "h" [V 2, V 3]]) = [1,2,3]
-- funcs(F "f" [F "g" [V 1], F "h" [V 2, V 3]]) = [1,2,3]
vars :: Term -> [Varname]
vars (V x) = [x]
vars (F f ts) = concat [vars t | t <- ts]

funcs :: Term -> [Funcname]
funcs (V x) = []
funcs (F f ts) = f : concat [funcs t | t <- ts]

-- substitute x t1 t2 equals t[x:=s]
-- Example
-- substitute 3 (F "f" [V 1]) (F "f" [F "g" [V 1], F "h" [V 2, V 3]])
-- =
-- f(g(v1),h(v2,f(v1)))
substitute :: Varname -> Term -> Term -> Term
substitute x s (V y)
    | x==y = s
    | otherwise = V y
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
appsub s (F f ts) = F f [appsub s t | t <- ts]

-- concatnoempties y = concat y <=> all lists in y are non-empty
-- otherwise concatnoempties y = []
-- we use this function to define equalize
concatnoempties :: [[a]] -> [a]
concatnoempties y = if all (\ls->not (null ls)) y then concat y else []

-- equalize is a helper function used to define getinstanceleft and getinstanceleftright (in the module Deductionsystem).
-- equalize t1 t2 = the 'substitution' s such that t1*s is possibly an instance of t2. The idea is to take for t1 the lefthand side of some rule r and for t2 the lefthand side of some equation on which we want to apply r.
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

-- We now define a type EQ and a bunch of functions, all used to eventually obtain the unification algorithm mgu which calculates the most general unifier of two terms.

type EQ = [(Term, Term)]
--transition takes a pair (P,S) where P is a problem-set of equalities, solution-set S and returns a pair (P',S') of a new problem-set and solution-set. It describes how a single transition step in the mgu-algorithm is done.
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

-- proceed takes a pair (P,S) where P is a problem-set and S is a Solution-set and applies a transition-step as long as possible (i.e. as long as P is non-empty).
proceed :: (EQ, EQ) -> EQ
proceed (e1, e2)
    | null e1 = e2
    | otherwise = proceed (transition (e1, e2))

-- processpair is a helper function used in the definition of eqtosub
processpair :: (Term, Term) -> (Varname, Term)
processpair (V x, V y) = (x, V y)
processpair (V x, y@(F _ _)) = (x, y)
processpair (x, y) = (-1, V (-1)) -- set some default value when applied to nonsense
-- eqtosub takes an equation and turns it into a substitution. It only makes sense in case the equation really represents a substitution but in our application this will always be true.
--
-- Example
-- eqtosub [(V 1, V 2), (V 3, F "f" [V 2])] = fromList [(1,2),(3,f(2))]
eqtosub :: EQ -> Substitution
eqtosub e = Map.fromList [processpair (a,b) | (a,b) <- e]

--mgu u v calculates the most general unifier of u and v
mgu :: Term -> Term -> Substitution
mgu t1 t2 = (eqtosub . proceed) ([(t1, t2)],[])

-- Example 1 (from syllabus automated reasoning)
-- s = F "P" [F "f" [V 1], V 2]
-- t = F "P" [V 3, F "g" [V 4]]
-- mgu s t = fromList [(2,g(v4)),(3,f(v1))]

-- Example 2 (from syllabus automated reasoning)
-- s = F "P" [F "f" [V 1], V 1]
-- t = F "P" [V 2, F "g" [V 2]]
-- mgu s t = fromList []

-- Example 3: Problem 4 of the Exam Automated Reasoning 2016
-- s = F "f" [F "f" [F "g" [V 3], V 3], F "f" [V 1, V 3]]
-- t = F "f" [V 2, F "f" [F "f" [V 2, F "g" [V 2]], F "g" [V 4]]]
-- mgu s t
-- =
-- fromList [(1,f(f(g(g(v4)),g(v4)),g(f(g(g(v4)),g(v4))))),(2,f(g(g(v4)),g(v4))),(3,g(v4))]

--Example 4: from https://www.cs.toronto.edu/~sheila/384/w11/Lectures/csc384w11-KR-tutorial.pdf
-- !!! CAUTION: THE SOLUTION ON THE SLIDES IS WRONG. THE ALGORITHM WILL CALCULATE THE CORRECT MGU!!!
-- s = F "p" [F "a" [], V 1, F "h" [F "g" [V 3]]]
-- t = F "p" [V 3, F "h" [V 2], F "h" [V 2]]
-- mgu s t = fromList [(1,h(g(a()))),(2,g(a())),(3,a())]
