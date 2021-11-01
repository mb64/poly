-- | Some general helper functions
module Utils where

import Data.List
import Data.Char
import Data.Text (Text)

type Name = Text

-- TODO: iter does not fuse, due to cross-module inlining issues.
-- Probably worth filing a GHC bug report.
iter :: Int -> (a -> a) -> a -> a
iter count f x = iterate' f x !! count

-- | Show an integer as a subscript: 'showSubscript 123 == "₁₂₃"'
showSubscript :: Int -> String
showSubscript = map subscript . show
  where subscript c = "₀₁₂₃₄₅₆₇₈₉" !! (ord c - ord '0')
