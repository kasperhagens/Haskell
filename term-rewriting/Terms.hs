module Terms where
import qualified Data.Map as Map
type Funcname = String
type Varname = Int
data Term = V Varname| F Funcname [Term] deriving (Eq)

instance Show Term where
    show = remsuperflcommas.convtoStr

-- convtoStr takes a string and concerts it to a string. Note that (convert t) contains additional superfluous commas for any non-variable term. For example convert (F "f" [V "x"]) = f(x,). We write a function remsuperflcommas to remove the superfluous commas
convtoStr :: Term -> String
convtoStr (V x) = show x
convtoStr (F f xs) = f++"(" ++ (concat [convtoStr x ++ "," | x<- xs]) ++ ")"

remsuperflcommas::String ->String
remsuperflcommas l = case l of
    (x:y:ys) -> if x==',' && y==')' then y:remsuperflcommas ys else x:remsuperflcommas (y:ys)
    (x:xs) -> x:xs
    [] -> []

--What you need to know:
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
-- appsub s t = F "f" [F "g" [V 2],F "h" [F "k" [V 4],V 3]]
appsub :: Substitution -> Term -> Term
appsub s (V x) = case (Map.toList s) of
    [] -> V x
    ((y, t) : l) -> if x==y then t else appsub (Map.fromList l) (V x)
appsub s (F f l) = F f [appsub s t | t <- l]

