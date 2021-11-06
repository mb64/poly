{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

-- | The source AST and parser.  Meant to be imported qualified
module Src where

import Utils

import Control.Applicative
import Control.Monad
import Data.Text (Text)
import Data.Text qualified as T
import Data.Functor
import Text.Parsec (Parsec, parse, eof, try, optionMaybe, option, (<?>), oneOf)
import Text.Parsec.Char (letter, alphaNum, char, string)
import Text.Parsec.Token
import Text.Parsec.Expr
import Data.Maybe

data Ty
  = TVar Name
  | THole -- _ in a type
  | TPair Ty Ty
  | TFun Ty Ty
  | TForall Name Ty
  deriving (Eq, Show)

data Pat
  = PWildcard
  | PVar Name
  | PConstr Name [Pat]
  deriving (Eq, Show)

data Exp
  = EVar Name
  | ELit Int
  | EApp Exp Exp
  | ELam Name (Maybe Ty) Exp
  | EAnnot Exp Ty
  | ECase Exp [(Pat, Exp)]
  | EIf Exp Exp Exp
  | ELet Defn Exp
  deriving (Eq, Show)

data Defn
  -- fun is generalizing letrec, val is non-generalizing non-recursive let
  = Val Name Ty Exp
  | Fun Name Ty Exp
  -- Local datatypes!
  | Datatype Name [(Name,[Ty])]
  deriving (Eq, Show)

isSyntacticValue :: Exp -> Bool
isSyntacticValue ELam{} = True
isSyntacticValue (EAnnot e _) = isSyntacticValue e
isSyntacticValue _ = False

-- From here on, it's just parsing/pretty-printing

-- TODO: pretty-printing

-- parser :: Parsec String () [Top]
exprParser :: Parsec String () Exp
exprParser = whiteSpace *> expr
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
        ["forall", "_", "if", "then", "else", "val", "let", "in", "end", "fun", "fn"]
      , reservedOpNames = ["->", "=>", "=", ":", "*", "+", "-", ".", "|"]
      , caseSensitive = True
      }

    ident = T.pack <$> identifier

    letExpr = do
      reserved "let"
      ds <- many defn
      reserved "in"
      exp <- expr
      reserved "end"
      pure $ foldr ELet exp ds

    atomic = EVar <$> ident
      <|> ELit . fromInteger <$> natural
      <|> try (parens (pure $ EVar "()"))
      <|> parens expr
      <|> letExpr
      <?> "simple expression"

    factor = foldl1 EApp <$> some atomic

    -- TODO: make if, fn, case prefix operators
    arithExpr = buildExpressionParser table factor
      <?> "arithmetic expression"
    table = [[op "*"], [op "+", op "-"]]
    op o = Infix (reservedOp o $> \x y -> EApp (EApp (EVar (T.pack o)) x) y) AssocLeft

    annotExpr = do
      e <- arithExpr
      maybe e (EAnnot e) <$> optionMaybe (reservedOp ":" *> typ)
    ifExpr = do
      reserved "if"
      cond <- expr
      reserved "then"
      trueBranch <- expr
      reserved "else"
      falseBranch <- expr
      pure $ EIf cond trueBranch falseBranch
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

    simpleTyp = reserved "_" $> THole
      <|> TVar <$> ident
      <|> parens typ
    typ :: Parsec String () Ty
    typ = liftA2 maybe id TFun <$> simpleTyp <*> optionMaybe (reservedOp "->" *> typ)
      <|> flip (foldr TForall) <$> (reserved "forall" *> many ident) <*> (reservedOp "." *> typ)
      <?> "type"

    defn = val <|> fun <?> "definition"
    val = do
      reserved "val"
      n <- ident
      t <- option THole (reservedOp ":" *> typ)
      reservedOp "="
      v <- expr
      pure $ Val n t v
    fun = do
      reserved "fun"
      n <- ident
      args <- some param
      retTy <- option THole (reservedOp ":" *> typ)
      reservedOp "="
      body <- expr
      let ty = foldr (\(_, argTy) -> TFun (fromMaybe THole argTy)) retTy args
      pure $ Fun n ty (foldr (uncurry ELam) body args)


