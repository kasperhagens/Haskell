{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
data Term t = Var t | Func t [Term t] deriving (Show, Eq)
-- A term is either a variable or a function applied to a list of Terms.
-- Example:
-- f(g(x), h(y,z)) is a term. Its corresponding tree is drawn as
--              f
--             /  \
--            g    h
--            |   / \
--            x  y   z
-- This term is encoded by
-- Func 'f' [Func 'g' [Var 'x'], Func 'h' [Var 'y', Var 'z']]

-- Suggestions Deivid
-- data Term = Var Int | Funct String Int [Term]
-- let t = Func "f" [(Func "g" [Var 1]), (Func "h" [Var 2, Var 3])]

type Substitution t = [(Term t, Term t)]
-- Note that working with sets instead of lists is would actually be better.
-- For example
-- [(Var 'x', Var 'y'), (Var 'y', Var 'z')]
-- and
-- [(Var 'y', Var 'z'), (Var 'x', Var 'y')]
-- are not considered to be equal, even though they respresent the same substution.
-- Furthermore we can construct invalid substutions like
-- [(Var 'x', Var 'y'), (Var 'x', Var 'z')]
-- or
-- [(Func 'f' [Var 'x'], Var 'x')]

varin :: Eq t => Term t -> Term t -> Bool
varin (Var x) (Var y)
   | x==y = True
   | otherwise = False
varin (Var x) (Func f l) = or [varin (Var x) t | t <- l]
varin u v = False --This last case is needed for avoiding non-exhaustive patterns (in case u is not a variable)
--
--Example
-- varin (Var 'x') (Func 'f' [Func 'g' [Var 'x'], Func 'h' [Var 'y', Var 'z']])
-- yields True
-- and
-- varin (Func 'f' [Var 'x']) (Var 'x')
-- yields False

substitute :: Eq t => Term t -> Term t -> Term t -> Term t
-- substitute x s t substitutes x|->s in t.
-- So substitute x s t = t[x:=s]
substitute (Var x) s (Var y)
    | x==y = s -- y[x:=s]=s if x=y
    | otherwise = Var y --y[x:=s]=y if x/=y
substitute (Var x) s (Func f l) = Func f [substitute (Var x) s t | t <- l]
substitute u v t = t -- needed for non-exhaustive patterns (when u is not a variable)
-- Example
-- substitute (Var'z') (Func 'f' [Var 'x']) (Func 'f' [Func 'g' [Var 'x'], Func 'h' [Var 'y', Var 'z']])

appsub :: Eq t => Substitution t -> Term t -> Term t
-- appsub s t = the term obtained by applying s on t
appsub [] (Var x) = Var x
appsub ((Var y, t) : l) (Var x)
    | x==y = t
    | otherwise = appsub l (Var x)
appsub s (Func f l) = Func f [appsub s t | t <- l]
-- NOTE: the function appsub is not total. For example
-- appsub [(Func 'f' [Var 'x'], Var 't')] (Var 'y')
-- is not defined. Make sure you only invoke it with well-defined substitutions.
--
-- Example
-- appsub [(Var 'x', Var 'y'), (Var 'y', Func 'k' [Var 'p'])] (Func 'f' [Func 'g' [Var 'x'], Func 'h' [Var 'y', Var 'z']])


-- transition will take a problem-set P of equalities (first argument) a solution-set S (second argument) and returns a pair (P',S') of a new problem-set and solution-set.
transition :: Eq t => ([(Term t, Term t)], Substitution t) -> ([(Term t, Term t)], Substitution t)
transition ([], s) = ([],s)
transition (((x@(Var _), y@(Var _)) : ls), s)
    | x == y = (ls, s)
    | otherwise = ([(appsub [(x,y)] u, appsub [(x,y)] v) | (u,v) <- ls], (x,y):[(appsub [(x,y)] q, appsub [(x,y)] r) | (q,r) <- s])
transition (((x@(Var _), y@(Func _ _)) : ls), s)
    | varin x y = ([], [])
    | otherwise = ([(appsub [(x,y)] u, appsub [(x,y)] v) | (u,v) <- ls], (x,y):[(appsub [(x,y)] q, appsub [(x,y)] r) | (q,r) <- s])
transition (((y@(Func _ _), x@(Var _)) : ls), s)
    | varin x y = ([], [])
    | otherwise = ([(appsub [(x,y)] u, appsub [(x,y)] v) | (u,v) <- ls], (x,y):[(appsub [(x,y)] q, appsub [(x,y)] r) | (q,r) <- s])
transition (((x@(Func f xs), y@(Func g ys)) : ls), s)
    | f/=g = ([],[])
    | otherwise = (zip xs ys ++ ls, s)

-- proceed takes a pair (P,S) where P is a problem-set and S is a Solution-set and applies a transition-step as long as possible (i.e. as long as P is non-empty)
proceed :: Eq t => ([(Term t, Term t)], Substitution t) -> Substitution t
proceed (p,s)
    | p==[] = s
    | otherwise = proceed (transition (p, s))
-- proceed ([(Func 'a' [], Var 'z'), (Var 'x', Func 'h' [Var 'y']), (Func 'h' [Func 'g' [Var 'z']], Func 'h' [Var 'y'])], [])

-- mgu u v calculates the most general unifier of u and v
mgu :: Eq t => Term t -> Term t -> Substitution t
mgu u v = reverse (proceed ([(u,v)],[]))

-- Examples (from syllabus automated reasoning)
--
-- Example 1
-- s= Func 'P' [Func 'f' [Var 'x'], Var 'y']
-- t= Func 'P' [Var 'z', Func 'g' [Var 'w']]
-- mgu st
-- =
-- mgu (Func 'P' [Func 'f' [Var 'x'], Var 'y']) (Func 'P' [Var 'z', Func 'g' [Var 'w']])
-- =
--
-- Example 2
-- s= Func 'P' [Func 'f' [Var 'x'], Var 'x']
-- t = Func 'P' [Var 'y', Func 'g' [Var 'y']]
-- mgu s t
-- =
-- mgu (Func 'P' [Func 'f' [Var 'x'], Var 'x']) (Func 'P' [Var 'y', Func 'g' [Var 'y']])

-- Example 3: Problem 4 of the Exam Automated Reasoning 2016
-- s = Func 'f' [Func 'f' [Func 'g' [Var 'z'], Var 'z'], Func 'f' [Var 'x', Var 'z']]
-- t= Func 'f' [Var 'y', Func 'f' [Func 'f' [Var 'y', Func 'g' [Var 'y']], Func 'g' [Var 'w']]]
-- mgu s t
-- =
-- mgu (Func 'f' [Func 'f' [Func 'g' [Var 'z'], Var 'z'], Func 'f' [Var 'x', Var 'z']]) (Func 'f'[Var 'y',Func 'f' [Func 'f' [Var 'y', Func 'g' [Var 'y']], Func 'g' [Var 'w']]])

--Example 4: from https://www.cs.toronto.edu/~sheila/384/w11/Lectures/csc384w11-KR-tutorial.pdf
-- !!! THIS EXAMPLE GIVES ALSO WRONG ANSWER !!!
-- s = Func 'p' [Func 'a' [], Var 'x', Func 'h' [Func 'g' [Var 'z']]]
-- t= Func 'p' [Var 'z', Func 'h' [Var 'y'], Func 'h' [Var 'y']]
-- mgu s t =
-- mgu (Func 'p' [Func 'a' [], Var 'x', Func 'h' [Func 'g' [Var 'z']]]) (Func 'p' [Var 'z', Func 'h' [Var 'y'], Func 'h' [Var 'y']])

-- proceed ([(Func 'p' [Func 'a' [], Var 'x', Func 'h' [Func 'g' [Var 'z']]], Func 'p' [Var 'z', Func 'h' [Var 'y'], Func 'h' [Var 'y']])], [])


--t = Func 'f' [Func 'g' [Var 'x'], Node 'h' [Var 'y', Var 'z']]
--main :: IO ()
--main = do
--   print t
--   putStrLn "Hello"
