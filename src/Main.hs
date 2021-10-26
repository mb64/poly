{-# LANGUAGE OverloadedStrings #-}

module Main where

import Data.Text (Text)
import Data.Text qualified as T
import Src (exprParser, isSyntacticValue)
import Text.Parsec (parse, eof)
import Elab qualified
import ElabUtils qualified as Elab
import Poly
import Control.Exception
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map

main :: IO ()
main = do
  contents <- getContents
  case parse (exprParser <* eof) "stdin" contents of
    Left err -> print err
    Right exp -> do
      -- print exp
      (ty, ir) <- Elab.runM $
        if isSyntacticValue exp then do
          (val, ty) <- Elab.underExtendedCtx (error "no type here") $ Elab.syn Map.empty 1 exp
          (val', ty') <- Elab.generalizeLet 0 "it" val ty
          pure (ty', Comp (Val val'))
        else do
          (val, ty) <- Elab.syn Map.empty 0 exp
          pure (ty, Comp (Val val))
      showTy <- Elab.debugTy 0 ty
      putStrLn $ "result : " ++ showTy
      -- TODO: pretty-printers
      -- print ir

