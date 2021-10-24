{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

-- | The source AST.  Meant to be imported qualified
--
-- TODO: this module needs some attention
module Src where

import Builtins

import Data.Text (Text)
import Data.Text qualified as T

type Name = Text

data Ty = TVar Name
        | TUnit
        | TInt
        | TPair Ty Ty
        | TFun Ty Ty
        | TForall Name Ty
        deriving (Eq, Show)

data Exp = EVar Name
         | ELit Int
         | EBuiltin Builtin
         | EApp Exp Exp
         | ELam Name (Maybe Ty) Exp
         | ELet Name (Maybe Ty) Exp Exp
         | EAnnot Exp Ty
         -- | ELet [(Name, Maybe Ty, Exp)] Exp
         -- | EIf Exp Exp Exp
        deriving (Eq, Show)

epair :: Exp -> Exp -> Exp
epair a b = EApp (EApp (EBuiltin Pair) a) b

eunit :: Exp
eunit = EBuiltin Unit

tforall :: Name -> (Ty -> Ty) -> Ty
tforall n f = TForall n (f (TVar n))
lam :: Name -> (Exp -> Exp) -> Exp
lam n f = ELam n Nothing (f (EVar n))

-- lef f :: (forall a. a -> a) -> Int = λ x. x 3 in f (λ x. x)
goodExample :: Exp
goodExample = ELet "f" (Just ty) (lam "x" \x -> EApp x (ELit 3))
    $ EApp (EVar "f") (lam "x" \x -> x)
  where ty = TFun (tforall "a" \a -> TFun a a) TInt

-- let f :: forall a. (forall s. s -> a) -> a = λ x. x 3 in f (λ x. x)
badExample :: Exp
badExample = ELet "f" (Just ty) (lam "x" \x -> EApp x (ELit 3))
    $ EApp (EVar "f") (lam "x" \x -> x)
  where ty = tforall "a" \a -> TFun (tforall "s" \s -> TFun s a) a


-- From here on, it's just parsing/pretty-printing

-- TODO: parsing, pretty-printing

