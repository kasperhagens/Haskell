module Z3 where
import Z3.Monad
import Data.Terms
import Data.Equations
import Data.Constraints
import Data.Make
import Data.Assert
import Data.Maybe
-- A simple check
-- v0>2 -> v0>0 or equivalently not(v0>2) \/ v0>0
c = Or (N (B ( V 0 `Gt` F "2" []))) (B (V 0 `Gt` F "2" []))
script :: Z3 ()
script = do
        assertConstraint c
--     a <- mkFreshIntVar "a"
--     b <- mkFreshIntVar "b"
--     aMb <- mkMul [a,b]
--     aAb <- mkAdd [a,b]
--     _0 <- mkInteger 0
--     _3 <- mkInteger 3
--     assert =<< aMb `mkLt` aAb
--     assert =<< a `mkGt` _0
--     assert =<< b `mkGt` _0

checkSat :: Z3 Result
checkSat = do
    script
    check

returnModel :: Z3 (Maybe Model)
returnModel = do
    script
    p <- getModel
    return $ snd p

getValue :: Z3 (Maybe Integer)
getValue = do
--    a <- mkFreshIntVar "a"
--    b <- mkFreshIntVar "a"
--    aMb <- mkMul [a,b]
--    aAb <- mkAdd [a,b]
--    _0 <- mkInteger 0
--    assert =<< aMb `mkLt` aAb --a*b<a+b
--    assert =<< a `mkGt` _0    --a>0
--    assert =<< b `mkGt` _0    --b>0
    assertConstraint c
    snd <$> (withModel $ (\m -> fromJust <$> evalInt m a))



printResult :: IO ()
printResult = do
    c <- evalZ3 checkSat
    m <- evalZ3 returnModel
    print c
    case m of
        Nothing -> putStr "There is no Model."
        Just model -> do
            m' <- evalZ3 $ modelToString model
            putStrLn $ concat ["The string of the model is\n", m']
    a <- evalZ3 getValue
    print a
