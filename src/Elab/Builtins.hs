{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Built-in things
module Elab.Builtins where

import Elab.Types

-- I should add this to the context
data Builtins = Builtins
  { tInt :: TyVal
  , tBool :: TyVal
  , tUnit :: TyVal
  }

-- TODO: actually have built-in things in it
initialCtx :: Ctx
initialCtx = Ctx
  { ctxLvl = 0
  , typeTIds = mempty
  , typeNames = mempty
  , typeEnv = []
  , boundVars = mempty }

