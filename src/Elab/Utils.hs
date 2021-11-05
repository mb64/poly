{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}

-- | Utils used by the elaborator
--
--  * Smart constructors for the 'Poly' IR, including getting the type of a
--    built-in
--  * Some convenient helper functions for dealing with typechecker 'TyVal's
module Elab.Utils where

import Poly hiding (Value, Ty(..))
import Poly qualified
import Utils
import Elab.Types

import Control.Monad.State.Strict
import Control.Monad.Writer.CPS
import Data.IORef
-- import Debug.Trace

-- some local helper functions
runLocally :: (a -> Exp' GonnaBeATy) -> M a -> M (a, Exp' GonnaBeATy)
runLocally k ma = pass $ do
  (a, lets) <- listen ma
  pure ((a, appEndo lets (k a)), const mempty)

letBindComp :: Ctx -> Name -> TyVal -> Comp' GonnaBeATy -> M Value
letBindComp ctx n ty e = do
  ident <- freshId
  tell $ Endo $ Let n ident (resolveTy ctx ty) e
  pure (Var ident)


-- smart constructors for IR values
var :: Id -> Value
var = Var

lit :: Int -> Value
lit = Lit

-- Probably not :/
letBind :: Ctx -> Name -> TyVal -> Value -> M Value
letBind ctx n ty val = letBindComp ctx n ty (Val val)

letRec :: Ctx -> Name -> TyVal -> (Value -> M (a, Value)) -> M (a, Value)
letRec ctx n ty f = do
  ident <- freshId
  ((a, _), e) <- runLocally (Comp . Val . snd) $ f (Var ident)
  -- lets should be mempty
  case e of
    Comp (Val val) -> do
      tell $ Endo $ LetRec n ident (resolveTy ctx ty) val
      pure (a, Var ident)
    _ -> error "internal error: should only letrec a value"

app :: Ctx -> TyVal -> Value -> Value -> M Value
app ctx ty f x = letBindComp ctx "tmp" ty (App f x)

tapp :: Ctx -> Value -> TyVal -> Value
tapp ctx x a = TApp x (resolveTy ctx a)

-- | Like 'lam' but with a more convenient type signature for the 'infer' function
inferLam :: Ctx -> Name -> TyVal -> (Value -> M (Value, TyVal)) -> M (Value, TyVal)
inferLam ctx n a f = do
  ident <- freshId
  ((_, b), body) <- runLocally (Comp . Val . fst) $ f (Var ident)
  pure (Lam n ident (resolveTy ctx a) body, b)

lam :: Ctx -> Name -> TyVal -> (Value -> M Value) -> M Value
lam ctx n a f = do
  ident <- freshId
  (_, body) <- runLocally (Comp . Val) $ f (Var ident)
  pure (Lam n ident (resolveTy ctx a) body)
  -- fst <$> inferLam n a \arg -> (,b) <$> f arg

tlam :: Name -> (Poly.Ty -> M Value) -> M Value
tlam n tm = do
  tid <- freshTId
  (_, body) <- runLocally (Comp . Val) $ tm (Poly.TVar tid)
  case body of
    Comp (Val v) -> pure (TLam n tid v)
    _ -> typeError "Value restriction: not a value!"

-- | Dereference if it's a hole.
--
-- If it returns a 'VHole ref', then 'ref' is guaranteed to be empty
deref :: TyVal -> M TyVal
deref (VHole ref) = liftIO $ go ref
  where
    go r = readIORef r >>= \case
      Filled (VHole ref') -> do
        contents <- go ref'
        writeIORef r (Filled contents)
        pure contents
      Filled contents -> pure contents
      _ -> pure $ VHole r
deref x = pure x

-- | Fill an empty hole
fill :: IORef Hole -> Hole -> M ()
fill ref contents = liftIO $ modifyIORef' ref \case
  Empty _ -> contents
  _ -> error "internal error: can only fill empty holes"

-- | Generalize a let-binding
--
-- Returns a tuple of:
--  - TIds the holes were filled with
--  - generalized type
generalizeLet :: Ctx -> TyVal -> M ([Poly.TId], TyVal)
generalizeLet ctx ty = mdo
  let initialLvl = ctxLvl ctx
  let base = initialLvl + 1 -- the type lives a level higher
  -- go finds holes and also shifts levels and also quotes TyVal to TyExp
  -- important: it returns its result lazily...
  let go :: Lvl -> TyVal -> StateT Lvl (WriterT [Poly.TId] M) TyExp
      go lvl = lift . lift . deref >=> \case
        VVar l -> pure $ case compare l base of
          LT -> TVar (lvl - l - 1)
          EQ -> error "internal error: should not have type vars of this level"
          GT -> TVar (lvl - (l + newLvl - base) - 1)
        VFun a b -> TFun <$> go lvl a <*> go lvl b
        VForall n a -> TForall n <$> go (lvl + 1) (a $$ VVar lvl)
        VHole hole -> liftIO (readIORef hole) >>= \case
          Empty s | s > initialLvl -> do
            -- add another TLam and another TApp
            tid <- lift $ lift freshTId
            newBinderLvl <- get
            modify' (+1)
            tell [tid]
            -- set the hole to Generalized
            lift $ lift $ fill hole (Generalized newBinderLvl tid)
            pure (TVar (lvl - newBinderLvl - 1))
          Empty _ -> pure (THole hole)
          Generalized l _ -> pure (TVar (lvl - l - 1))
          Filled _ -> error "oh no"
  -- ... because it uses the newLvl it returns
  ((tyExp, newLvl), tids) <- runWriterT $ go newLvl ty `runStateT` ctxLvl ctx
  let tyExp' = iter (newLvl - ctxLvl ctx) (TForall "t") tyExp
      tyVal = evalTy (typeEnv ctx) tyExp'
  pure (tids, tyVal)


