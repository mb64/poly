{-# LANGUAGE OverloadedStrings #-}

module Main where

import Src (exprParser, isSyntacticValue)
import Text.Parsec (parse, eof)
import Elab qualified
import Elab.Types qualified as Elab
import Elab.Utils qualified as Elab
import Poly

main :: IO ()
main = do
  contents <- getContents
  case parse (exprParser <* eof) "stdin" contents of
    Left err -> print err
    Right e -> do
      -- print exp
      let ctx = Elab.Ctx 0 mempty mempty mempty
      (ty, ir) <- Elab.runM $
        if isSyntacticValue e then do
          (val, ty) <- Elab.syn (ctx { Elab.ctxLvl = 1 }) e
          (val', ty') <- Elab.generalizeLet ctx "result" val ty
          (, Comp (Val val')) <$> Elab.displayTyCtx ctx ty'
        else do
          (val, ty) <- Elab.syn ctx e
          (, Comp (Val val)) <$> Elab.displayTyCtx ctx ty
      putStrLn $ "result : " ++ ty
      -- TODO: pretty-printers
      -- print ir

