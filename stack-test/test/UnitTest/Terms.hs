module UnitTest.Terms where

import Data.Terms
import Z3

printTest :: IO ()
printTest = do
    putStrLn "\n Testing Terms module"
    print t

t = V 1
