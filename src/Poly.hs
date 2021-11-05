{-# LANGUAGE StrictData #-}


-- | The polymorphic core language.
--
-- Roughly, ANF'd System F with no impredicative polymorphism
module Poly where

import Data.Text qualified as T
import Data.IntMap.Strict qualified as IMap
import Utils

-- Types
------------------------------------------------------------

newtype TId = TId Int deriving (Show, Eq, Ord)

data Ty = TVar TId
        | TFun Ty Ty
        | TForall Name TId Ty
        -- TODO: these can all eventually be coalesced into a single variant for
        -- rigid type constructors
        | TUnit
        | TInt
        | TPair Ty Ty
        deriving (Show, Eq)


-- Terms
------------------------------------------------------------

newtype Id = Id Int deriving (Show, Eq, Ord)

-- | Values are characterized by no runtime behavior (except possibly
-- allocation)
type Value = Value' Ty
data Value' ty
  = Var Id
  | Lit Int
  -- | Pair (Value' ty) (Value' ty)
  | Lam Name Id ty (Exp' ty)
  | TLam Name TId (Value' ty) -- Value restriction!
  | TApp (Value' ty) ty -- hmmm
  deriving (Show, Eq, Functor, Foldable, Traversable)

-- | Computations
type Comp = Comp' Ty
data Comp' ty
  = Val (Value' ty)
  | App (Value' ty) (Value' ty)
  -- TODO
  -- | Builtin Builtin [Value]
  -- | If (Value' ty) (Exp' ty) (Exp' ty) -- TODO
  deriving (Show, Eq, Functor, Foldable, Traversable)

-- | Expressions
type Exp = Exp' Ty
data Exp' ty
  = Let Name Id ty (Comp' ty) (Exp' ty)
  -- only recursively define values.
  | LetRec Name Id ty (Value' ty) (Exp' ty)
  | Comp (Comp' ty)
  deriving (Show, Eq, Functor, Foldable, Traversable)


-- TODO: pretty-printing

prettyTy :: Ty -> String
prettyTy = go IMap.empty False
  where
    parens p s = if p then "(" ++ s ++ ")" else s
    go ctx _ (TVar (TId i)) = IMap.findWithDefault "UNNAMED" i ctx ++ showSubscript i
    go ctx p (TFun a b) = parens p $ go ctx True a ++ " -> " ++ go ctx False b
    go ctx p (TForall n (TId i) ty) = parens p $ "forall " ++ T.unpack n ++ showSubscript i ++ ". " ++ go (IMap.insert i (T.unpack n) ctx) False ty
    go ctx _ (TPair a b) = "(" ++ go ctx False a ++ ", " ++ go ctx False b ++ ")"
    go _ _ TUnit = "unit"
    go _ _ TInt = "int"


