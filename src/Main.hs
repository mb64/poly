{-# LANGUAGE OverloadedStrings #-}

module Main where

import Src (exprParser)
import Text.Parsec (parse, eof)
import Elab qualified
import Elab.Types qualified as Elab
import Elab.Builtins qualified as Elab
import Poly

main :: IO ()
main = do
  contents <- getContents
  case parse (exprParser <* eof) "stdin" contents of
    Left err -> print err
    Right e -> do
      print e
      let ctx = Elab.initialCtx
      (ty, ir) <- Elab.runM $ do
        (val, ty) <- Elab.syn ctx e
        (, Comp (Val val)) <$> Elab.displayTyCtx ctx ty
      putStrLn $ "result : " ++ ty
      -- TODO: pretty-printers
      -- print ir

