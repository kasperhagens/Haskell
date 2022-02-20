module Data.Side where
import Data.Terms

data Side = Left | Right deriving (Eq, Show, Read)

oppositeSide :: Side -> Side
oppositeSide Data.Side.Left = Data.Side.Right
oppositeSide Data.Side.Right = Data.Side.Left
