{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Built-in things
--
-- They are expanded to 'λ x. λ y. Builtin b [x, y]' in the 'Poly' IR.
--
-- Their types are defined in ElabUtils.
module Builtins where

-- TODO: some of these do computation and others are just constructors.
-- In the future, when adding algebraic data types, make the constructors their
-- own thing.
data Builtin
  = Unit      -- : Unit
  | Pair      -- : forall a b. a -> b -> Pair a b
  | Add       -- : int -> int -> int
  | Sub       -- : int -> int -> int
  | Mul       -- : int -> int -> int
  deriving (Eq, Show)

-- builtinArity :: Builtin -> Int
-- builtinArity Unit = 0
-- builtinArity Pair = 2
-- builtinArity Add = 2
-- builtinArity Sub = 2
-- builtinArity Mul = 2

