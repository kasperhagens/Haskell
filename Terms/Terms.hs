import qualified Data.Map as Map
type Name = String
data Term = V | Func Name [Term] deriving (Show, Eq)
-- Example of a Term:
-- Func "f" [(V 1)]

type Substitution = Map.Map Name Term
--Map a b is the type of mappings from type a to type b
--You can make a mapping from a list with the function fromList.
--For example, Map.fromList [((1,2),(3,4),(5,6))] creates a mapping
--{1|->2, 3|->4, 5|->6}
--Conversely you can turn a mapping into a list of tuples by using the function toList. For example
-- Map.toList (Map.fromList [((1,2),(3,4),(5,6))])=[((1,2),(3,4),(5,6))]

appsub :: Substitution -> Term -> Term
appsub s t
    | Map.toList s==[] = t
    | Map.toList s == (x,t):l =
