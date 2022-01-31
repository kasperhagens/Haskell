module Main where
import Lib
import Z3.Monad
import Data.Terms
import Data.Rules
import Data.Equations
import Data.Constraints
import Data.Zz
import Data.Char
import Data.List (inits, nub)
import Data.Maybe
import Data.Deductionsystem (
    Proofstate,
    Side (..),
    Rules,
    showsimps,
    simplification,
    equationSide,
    expansion,
    deletion,
    eqdeletion)

getHoles :: String -> IO Int
getHoles message =
    do  putStrLn message
        x <- getLine
        if all isDigit x && (read x >= 1)
            then
                return (read x :: Int)
            else
                getHoles "The number of holes must be an integer >0"

getLeftRight :: String -> IO Side
getLeftRight message =
    do  putStrLn message -- show a message like "Wchich side?"
        x <- getLine
        if map toLower x `elem` tail (inits "left")
            then
                return Data.Deductionsystem.Left
            else
                if map toLower x `elem` tail (inits "right")
                    then
                        return Data.Deductionsystem.Right
                    else
                        getLeftRight "Left or Right?"

getRuleSet :: String -> IO String
getRuleSet message =
    do  putStrLn message --
        x <- getLine
        if x == "R" || x == "r"
            then
                return "rs"
            else
                if x == "H" || x == "h"
                    then
                        return "hs"
                    else
                        getRuleSet "R or H?"

getRule :: String -> [Rule] -> String -> IO Int
getRule message rules symb = do
    putStrLn message
    l <- getLine
    let lth = length rules
        eval = (fmap (\n x -> (n,x == (symb ++ show n) || x == show n)) [0..(lth -1)])<*> [l]
        evaltrue = filter (\x -> snd x == True) eval
    if null evaltrue
        then
            getRule "This rule does not exist. Enter a valid rule." rules symb
        else do
            let n = fst (head evaltrue)
            if (n > lth || n<0)
                then
                    getRule "This rule does not exist. Enter a valid rule." rules symb
                else
                    return n

getEq :: String -> [Equation] -> IO Int
getEq message eqs = do
    if null (tail eqs)
        then
            return 0
        else do
            putStrLn message
            l <- getLine
            let lth = length eqs
                eval = (fmap (\n x -> (n,x == ("e" ++ show n) || x == show n)) [0..(lth -1)]) <*> [l]
                evaltrue = filter (\x -> snd x == True) eval
            if null evaltrue
                then
                    getEq "This equation does not exist. Enter a valid equation." eqs
                else do
                    let n = fst (head evaltrue)
                    if (n > lth || n<0)
                        then
                        getEq "This equation does not exist. Enter a valid equation." eqs
                        else
                            return n

-- !!WARNING!! The function getPosition will not do a safety check to deterine whether p is really a position (we could implement this later). If we enter an invalid position then it will crash.
getPosition :: String -> IO Position
getPosition message = do
    putStrLn message
    p <- getLine
    return (read p :: Position)

getPositions :: String -> IO [Position]
getPositions message = do
    putStrLn message
    p <- getLine
    return (read p :: [Position])

getStrategy :: String -> IO String
getStrategy message = do
    putStrLn message
    str <- getLine
    if ((map toLower str) `elem` (tail (inits "simplification")))
        then
            return "simp"
        else
            if (map toLower str) `elem` (tail (inits "expansion"))
                then
                    return "exp"
                else
                    if (map toLower str) `elem` (tail (inits "deletion"))
                        then
                            return "del"
                        else
                            if (
                                (map toLower str) `elem` (tail (inits "equation deletion"))
                                ||
                                (map toLower str) `elem` (tail (inits "eq-deletion"))
                                ||
                                (map toLower str) `elem` (tail (inits "equation-deletion"))
                                    )
                                    then
                                        return "eq-del"
                                    else
                                        getStrategy "Enter a valid strategy."

printEqs :: String -> [Equation] -> IO ()
printEqs message eqs = do
    let l = length eqs
    if l==0
        then do
            putStrLn ("No " ++ (map toLower message))
            putStrLn " "
        else do
        let eqsindex = zipWith (++) (replicate l "e") (fmap show [0..l])
            numberedeqs = zipWith (\x y->x ++ ": " ++ y) eqsindex (fmap show eqs)
        putStrLn message
        mapM_ putStrLn numberedeqs
        putStrLn " "

printRules :: String -> [Rule] -> String -> IO ()
printRules message rs symb = do
    let l = length rs
    if l==0
        then do
            putStrLn ("No " ++ (map toLower message))
            putStrLn " "
        else do
        let rsindex = zipWith (++) (replicate l symb) (fmap show [0..l])
            numberedrs = zipWith (\x y->x ++ ": " ++ y) rsindex (fmap show rs)
        putStrLn message
        mapM_ putStrLn numberedrs
        putStrLn " "

printPfst :: Proofstate -> IO ()
printPfst (eqs, hs) = do
    printEqs "Equations" eqs
    printRules "Hypothesis" hs "h"

interactiveSimplification :: Rules -> Proofstate -> IO Proofstate
interactiveSimplification rs (eqs, hs) = do
--    putStrLn "Current proofstate:"
--    printPfst (eqs,hs)
    n <- getEq "Choose an equation to simplify?" eqs
    putStrLn (show (eqs!!n))
    putStrLn " "
    s <- getLeftRight "On which side of this equation to simplify: Left or Right?"
    putStrLn (show ((equationSide (eqs !! n) s)))
    putStrLn " "
    p <- getPosition (
        "Enter the position of the subterm"
        ++
    --    show (equationSide (eqs !! n) s)
    --    ++
        " to simplify"
        )
    let u = postoterm (equationSide (eqs !! n) s) p
    if (u == Nothing)
        then do
            putStrLn "Invalid position, try again."
            putStrLn " "
            interactiveSimplification rs (eqs, hs)
        else do
            let t = fromJust u
            putStrLn (show t)
            putStrLn " "
            if null hs
                then do
                    printRules "Rules" rs "r"
                    m <- getRule ("Choose the rule to use for simplification ") rs "r"
                    putStrLn " "
                    if (null (equalize (leftsideR (rs!!m)) t))
                        then do
                            putStrLn "No simplification possible. Proofstate has not been changed."
                            putStrLn " "
                            return (eqs, hs)
                        else do
                            y <- simplification n s p (rs!!m) (eqs, hs)
                            return y
                else do
                    putStrLn "These are your choices for simplification"
                    printRules "Rules" rs "r"
                    printRules "Hypothesis" hs "h"
                    l <- getRuleSet ("Using a Rule or an Hypothesis? Press R or H.")
                    if l == "rs"
                        then do
                            m <- getRule "Which rule from R to use in the simplification?" rs "r"
                            if null (equalize (leftsideR (rs!!m)) t)
                                then do
                                        putStrLn "No simplification possible. Proofstate has not been changed."
                                        putStrLn " "
                                        return (eqs, hs)
                                else
                                        simplification n s p (rs!!m) (eqs, hs)
                    else do
                            m <- getRule "Which rule from H to use in the simplification?" hs "h"
                            if null (equalize (leftsideR (hs!!m)) t)
                                 then do
                                        putStrLn "No simplification possible. Proofstate has not been changed."
                                        putStrLn " "
                                        return (eqs, hs)
                                else do
                                        simplification n s p (hs!!m) (eqs, hs)

interactiveExpansion :: Rules -> Proofstate -> IO Proofstate
interactiveExpansion rs (eqs, hs) = do
    putStrLn "Current proofstate:"
    printPfst (eqs,hs)
    n <- getEq "Which equation to expand?" eqs
    putStrLn (show (eqs!!n))
    putStrLn " "
    s <- getLeftRight "On which side of this equation to expand: Left or Right?"
    putStrLn (show ((equationSide (eqs !! n) s)))
    putStrLn " "
    p <- getPosition (
        "Enter the position of the subterm"
        ++
    --    show (equationSide (eqs !! n) s)
    --    ++
        " to expand"
        )
    let u = postoterm (equationSide (eqs !! n) s) p
    if (u == Nothing)
        then do
            putStrLn "Invalid position, try again."
            putStrLn " "
            interactiveExpansion rs (eqs, hs)
        else
            expansion n s p rs (eqs, hs)

interactiveDeletion :: Proofstate -> IO Proofstate
interactiveDeletion (eqs,hs) = do
    putStrLn "Current proofstate:"
    putStrLn " "
    printPfst (eqs,hs)
    n <- getEq "Which equation to delete?" eqs
    putStrLn (show (eqs!!n))
    putStrLn " "
    deletion n (eqs,hs)

interactiveEqDeletion :: Proofstate -> IO Proofstate
interactiveEqDeletion (eqs,hs) = do
    putStrLn "Current proofstate:"
    putStrLn " "
    printPfst (eqs,hs)
    n <- getEq "On which equation do you want to apply Equation Deletion?" eqs
    putStrLn (show (eqs!!n))
    putStrLn " "
    h <- getHoles "How many holes does the context contain?"
    pl <- getPositions "Enter the list of positions of these holes on the left-side of the equation."
    let m = length (nub pl)
    if (m /= h)
        then do
            putStrLn ("Invalid input: " ++ (show h) ++ " different holes were expected. Proofstate has not been changed")
            putStrLn " "
            return (eqs, hs)
        else do
            pr <- getPositions "Enter the list of positions of these holes on the right-side of the equation."
            let k = length (nub pr)
            if (k /= h)
                then do
                    putStrLn ("Invalid input: " ++ (show h) ++ " different holes were expected. Proofstate has not been changed")
                    putStrLn " "
                    return (eqs, hs)
                else
                    eqdeletion n h pl pr (eqs,hs)

playRound :: Rules -> Proofstate -> IO Proofstate
playRound rs pfst = do
    putStrLn "Current proofstate:"
    putStrLn " "
    printPfst pfst
    str <- getStrategy "Choose a strategy: Simplification, Expansion, Equation deletion or Deletion"
    putStrLn " "
    if str == "simp"
        then
            interactiveSimplification rs pfst
        else
            if str == "exp"
                then
                    interactiveExpansion rs pfst
                else
                    if str == "del"
                        then
                            interactiveDeletion pfst
                        else
                            interactiveEqDeletion pfst

play :: Rules -> Proofstate -> IO Proofstate
play rs (eqs, hs) = do
    if null rs
        then do
            putStrLn "The set of rules must be nonempty."
            return (eqs, hs)
        else
            if null eqs
                then do
                    putStrLn "Proof finished."
                    return (eqs, hs)
                else do
                    pfst <- playRound rs (eqs, hs)
                    play rs pfst

r0 = R (F "sum" [V 0]) (F "error" []) (B (V 0 `Lt` F "0" []))
r1 = R (F "sum" [V 0]) (F "v" [V 0, F "sum" [F "-" [V 0, F "1" []]]]) (B (V 0 `Gt` F "0" []))
r2 = R (F "sum" [V 0]) (F "return" [F "0" []]) (B (V 0 `Eq` F "0" []))
r3 = R (F "v" [V 0, F "return" [V 1]]) (F "return" [F "+" [V 0, V 1]]) (B TT)
rs = [r0, r1, r2, r3]

e = E (F "sum" [V 0]) (F "return" [F "/" [F "*" [V 0, F "+" [V 0, F "1" []]], F "2" []]]) (B (V 0 `Ge` F "0" []))
eqs = [e]
pfst = (eqs, rs)
hs = []

main :: IO ()
main = do
    printRules "Rules " rs "r"
    x <- play rs (eqs, hs)
    print x
