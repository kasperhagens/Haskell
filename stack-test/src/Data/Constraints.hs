module Data.Constraints where
import Data.Terms
import Data.Side
import  Data.List
import qualified Maybes as Data.Maybe

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

--constrToL is a helper function in order to define constrToList
constrToL :: Constraint -> [[Side]]
constrToL (B f) = [[]]
constrToL (N c) = constrToL c
constrToL (c1 `And` c2) =
    [Data.Side.Left : x | x <- constrToL c1]
    ++
    [Data.Side.Right : y | y <- constrToL c2]
constrToL (c1 `Or` c2) = constrToList (c1 `And` c2)

constrToList :: Constraint -> [[Side]]
constrToList c = [u | y <- constrToList c, u <- inits y]

--listToConsr c l = the subconstraint of c occuring at position l
listToConstr :: Constraint -> [Side] -> Maybe Constraint
listToConstr c [] = Just c
listToConstr (B f) s = if null s then Just (B f) else Nothing
listToConstr (N c) s = if null s then Just (N c) else Nothing
listToConstr (c1 `And` c2) (Data.Side.Left : l) = listToConstr c1 l
listToConstr (c1 `And` c2) (Data.Side.Right : l) = listToConstr c2 l
listToConstr (c1 `Or` c2) s = listToConstr (c1 `And` c2) s

subCstrs :: Constraint -> [([Side], Constraint)]
subCstrs c = [(x, Data.Maybe.fromJust (listToConstr c x))| x <- constrToList c, Data.Maybe.isJust (listToConstr c x)]
