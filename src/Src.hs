{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

-- | The source AST.  Meant to be imported qualified
--
-- TODO: this module needs some attention
module Src where

import Builtins

import Control.Applicative
import Control.Monad
import Data.Text (Text)
import Data.Text qualified as T
import Data.Functor
import Text.Parsec (Parsec, parse, eof, try, optionMaybe, (<?>), oneOf)
import Text.Parsec.Char (letter, alphaNum, char, string)
import Text.Parsec.Token
import Text.Parsec.Expr
import Data.Maybe


type Name = Text

data Ty = TVar Name
        | TUnit
        | TInt
        | THole -- _ in a type
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

isSyntacticValue :: Exp -> Bool
isSyntacticValue (ELam _ _ _) = True
isSyntacticValue (EAnnot e _) = isSyntacticValue e
isSyntacticValue _ = False

-- | Top-level declarations/definitions
-- 
-- TODO: more things (standalone type declarations? imports? modules?)
data Top = Defn Name (Maybe Ty) Exp
         deriving Show

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

parser :: Parsec String () [Top]
exprParser :: Parsec String () Exp
(parser, exprParser) = (whiteSpace *> many top, whiteSpace *> expr)
  where
    TokenParser{..} = makeTokenParser LanguageDef{
        commentStart = "(*"
      , commentEnd = "*)"
      , commentLine = "--"
      , nestedComments = True
      , identStart = letter <|> char '_'
      , identLetter = alphaNum <|> char '_'
      , opStart = oneOf "!#$%&*+./<=>?@\\^|-~:"
      , opLetter = oneOf "!#$%&*+./<=>?@\\^|-~:"
      , reservedNames =
        ["forall", "_", "if", "then", "else", "val", "let", "in", "end", "fun", "fn", "int"] -- TODO int is not reserved
      , reservedOpNames = ["->", "=>", "=", ":", "*", "+", "-", "."]
      , caseSensitive = True
      }

    ident = T.pack <$> identifier

    letExpr = do
      reserved "let"
      ds <- many defn
      reserved "in"
      exp <- expr
      reserved "end"
      pure $ foldr (\(n,ty,val) -> ELet n ty val) exp ds

    atomic = EVar <$> ident
      <|> ELit . fromInteger <$> natural
      <|> try (parens (pure $ EBuiltin Unit))
      <|> parens expr
      <|> letExpr
      <?> "simple expression"

    factor = foldl1 EApp <$> some atomic

    arithExpr = buildExpressionParser table factor
      <?> "arithmetic expression"
    table = [[op "*" Mul], [op "+" Add, op "-" Sub]]
    op name b =
      Infix (reservedOp name $> \x y -> EApp (EApp (EBuiltin b) x) y) AssocLeft

    annotExpr = do
      e <- arithExpr
      maybe e (EAnnot e) <$> optionMaybe (reservedOp ":" *> typ)
    ifExpr = do
      reserved "if"
      _cond <- expr
      reserved "then"
      _trueBranch <- expr
      reserved "else"
      _falseBranch <- expr
      pure $ error "TODO: implement if expressions"
    lambda = do
      reserved "fn"
      args <- some param
      reservedOp "=>"
      body <- expr
      pure $ foldr (uncurry ELam) body args
    expr = ifExpr <|> lambda <|> annotExpr <?> "expression"

    param :: Parsec String () (Name, Maybe Ty)
    param = (, Nothing) <$> ident
      <|> parens ((,) <$> ident <* reservedOp ":" <*> (Just <$> typ))
      <?> "parameter"

    simpleTyp = try (parens (pure TUnit))
      <|> reserved "int" $> TInt
      <|> reserved "_" $> THole
      <|> TVar <$> ident
      <|> parens typ
    typ :: Parsec String () Ty
    typ = liftA2 maybe id TFun <$> simpleTyp <*> optionMaybe (reservedOp "->" *> typ)
      <|> flip (foldr TForall) <$> (reserved "forall" *> many ident) <*> (reservedOp "." *> typ)
      <?> "type"

    -- currently no difference, but eventually 'fun' will be a letrec
    defn = val <|> fun <?> "definition"
    val = do
      reserved "val"
      n <- ident
      t <- optionMaybe (reservedOp ":" *> typ)
      reservedOp "="
      v <- expr
      pure (n,t,v)
    fun = do
      reserved "fun"
      n <- ident
      args <- some param
      retTy <- optionMaybe (reservedOp ":" *> typ)
      reservedOp "="
      body <- expr
      let ty = foldr (\(_, argTy) -> TFun (fromMaybe THole argTy)) (fromMaybe THole retTy) args
      pure (n, Just ty, foldr (uncurry ELam) body args)

    top = (\(n,ty,val) -> Defn n ty val) <$> defn


