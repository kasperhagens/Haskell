module UnitTest.Terms where

import Data.Terms

printTest :: IO ()
printTest = do
    putStrLn "\n Testing Terms module"
    print t

t = V 1
