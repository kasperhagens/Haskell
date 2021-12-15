--newtype Variable t = Var t deriving (Eq, Show)
--data Term t = Variable t| Func t [Term t] deriving (Show, Eq)
--
--The definition above gives problems: if we write
--Func 'f' [ Var 'x']
--then we receive the error:
--Couldn't match expected type ‘Term Char’
--with actual type ‘Variable Char’
--In the expression: Var 'x'
--In the second argument of ‘Func’, namely ‘[Var 'x']’
--In the expression: Func 'f' [Var 'x']


-- Example:
-- The term-tree corresponding to f(g(x), h(y,z)) is drawn as
--              f
--             /  \
--            g    h
--            |   / \
--            x  y   z
-- which will be encoded as
-- Func 'f' [Func 'g' [Var 'x'], Func 'h' [Var 'y', Var 'z']]

--let t = Func "f" [(Func "g" [Var 1]), (Func "h" [Var 2, Var 3])]

--type Substitution t = [(Variable t, Term t)]
-- Note that the equality considers ordering and duplicates of the tuples ocurring in the list. This may give problems when we want to compare substitutions. For example
-- [(Var 'x', Var 'y'), (Var 'y', Var 'z')]
-- and
-- [(Var 'y', Var 'z'), (Var 'x', Var 'y')]
-- are not considered to be equal, even though they respresent the same substution.
-- SOLUTION: work with sets instead of lists. But how to define a set in Haskell?


