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
    show (Eq t1 t2) = show t1 ++ "=" ++ show t2
    show (Lt t1 t2) = show t1 ++ "<" ++ show t2
    show (Le t1 t2) = show t1 ++ "<="++ show t2
    show (Gt t1 t2) = show t1 ++ ">" ++ show t2
    show (Ge t1 t2) = show t1 ++ ">=" ++ show t2

appsubB :: Substitution -> Basicformula -> Basicformula
appsubB s TT = TT
appsubB s FF = FF
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
    show (Or f1 f2) = "(" ++ show f1 ++ ")" ++ " or " ++ "(" ++ show f2 ++ ")"
    --The brackets around s and t are really necessary for expressions like s \/ (t /\ u)
    show (And f1 f2) = "("++show f1 ++ ")"++ " and "++ "("++show f2 ++")"
    show (N f) = "not("++show f++")"

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
constrToL (c1 `Or` c2) = constrToL (c1 `And` c2)

constrToList :: Constraint -> [[Side]]
constrToList c = nub [u | y <- constrToL c, u <- inits y]

--listToConsr c l = Maybe the subconstraint of c occuring at position l
listToConstr :: Constraint -> [Side] -> Maybe Constraint
listToConstr c [] = Just c
listToConstr (B f) p = if null p then Just (B f) else Nothing
listToConstr (N c) p = if null p then Just (N c) else Nothing
listToConstr (c1 `And` c2) (Data.Side.Left : l) = listToConstr c1 l
listToConstr (c1 `And` c2) (Data.Side.Right : l) = listToConstr c2 l
listToConstr (c1 `Or` c2) p = listToConstr (c1 `And` c2) p

subCstrs :: Constraint -> [([Side], Constraint)]
subCstrs c = [(x, Data.Maybe.fromJust (listToConstr c x))| x <- constrToList c, Data.Maybe.isJust (listToConstr c x)]


--removeTrues c = the constraint obtained by removing all Trues from c, except if c equals B TT. This is used as a helper function to define removeCstrAtPos
removeTrues :: Constraint -> Constraint
removeTrues (B f) = B f
removeTrues (N c) = N (removeTrues c)
removeTrues (c `And` (B TT)) = c

removeTrues (c1 `And` c2)
  | c1 == B TT =
        removeTrues c2
  | c2 == B TT =
        removeTrues c1
  | otherwise =
        removeTrues c1 `And` removeTrues c2

removeTrues (c1 `Or` c2)
  | c1 == B TT =
        removeTrues c2
  | c2 == B TT =
        removeTrues c1
  | otherwise =
        removeTrues c1 `Or` removeTrues c2

remo :: Constraint -> [Side] -> Constraint
remo c p
  | Data.Maybe.isNothing (listToConstr c p) =
        c
  | null p =
        B TT -- If we move the whole constraint then we are left behind with True.
  | otherwise = -- So in this case p is nonempty, which means that it is either of the form Left : l or Right : l
        case c of
            B f -> B TT -- If we remove a single basic-formula constraint then we are left behind with True.
            N c -> B TT
            c1 `And` c2 -> case p of
                [] -> B TT -- This one is not needed but otherwise Visual Studio complains.
                Data.Side.Left : l -> (remo c1 l) `And` c2
                Data.Side.Right : l -> c1 `And` (remo c2 l)
            c1 `Or` c2 -> case p of
                [] -> B TT -- This one is not needed but otherwise Visual Studio complains.
                Data.Side.Left : l -> remo c1 l `Or` c2
                Data.Side.Right : l -> c1 `Or` (remo c2 l)

--removeCstrAtPos c p = the constraint obtained from c by removing the subconstraint of c at position p. If p is an invalid position in c then removeCstrAtPos c p = c.
-- !!!REMARK!!! The algorithm first replaces the subconstraint of c at position p by True. Next we remove ALL Trues from the obtained constraint. This means that if we have for example the constraint
-- x>0 \/ y>0 \/ True
-- and we remove x>0 then we obtain the constraint y>0 instead of y>0 \/ True
removeCstrAtPos :: Constraint -> [Side] -> Constraint
removeCstrAtPos c p = removeTrues (remo c p)
