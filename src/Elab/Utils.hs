{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}

-- | Utils used by the elaborator
--
--  * Smart constructors for the 'Poly' IR, including getting the type of a
--    built-in
--  * Some convenient helper functions for dealing with typechecker 'Ty's
module Elab.Utils where

import Poly hiding (Value, Ty(..))
import Poly qualified
import Builtins
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

letBindComp :: Ctx -> Name -> Ty -> Comp' GonnaBeATy -> M Value
letBindComp ctx n ty e = do
  ident <- freshId
  tell $ Endo $ Let n ident (resolveTy ctx ty) e
  pure (Var ident)


-- smart constructors for IR values
var :: Id -> Value
var = Var

lit :: Int -> Value
lit = Lit

letBind :: Ctx -> Name -> Ty -> Value -> M Value
letBind ctx n ty val =
  if simple val
    then pure val
    else letBindComp ctx n ty (Val val)
  where
    simple v = case v of
      Var _ -> True
      Lit _ -> True
      TApp v' _ -> simple v'
      TLam _ _ v' -> simple v'
      _ -> False

app :: Ctx -> Ty -> Value -> Value -> M Value
app ctx ty f x = letBindComp ctx "tmp" ty (App f x)

tapp :: Ctx -> Value -> Ty -> Value
tapp ctx x a = TApp x (resolveTy ctx a)

-- | Like 'lam' but with a more convenient type signature for the 'syn' function
synlam :: Ctx -> Name -> Ty -> (Value -> M (Value, Ty)) -> M (Value, Ty)
synlam ctx n a f = do
  ident <- freshId
  ((_, b), body) <- runLocally (Comp . Val . fst) $ f (Var ident)
  pure (Lam n ident (resolveTy ctx a) body, b)

lam :: Ctx -> Name -> Ty -> (Value -> M Value) -> M Value
lam ctx n a f = do
  ident <- freshId
  (_, body) <- runLocally (Comp . Val) $ f (Var ident)
  pure (Lam n ident (resolveTy ctx a) body)
  -- fst <$> synlam n a \arg -> (,b) <$> f arg

tlam :: Name -> (Poly.Ty -> M Value) -> M Value
tlam n tm = do
  tid <- freshTId
  (_, body) <- runLocally (Comp . Val) $ tm (Poly.TVar tid)
  case body of
    Comp (Val v) -> pure (TLam n tid v)
    _ -> typeError "Value restriction: not a value!"

-- TODO: this is very special-cased. Figure out a more systematic way to do
-- this?
builtin :: Ctx -> Builtin -> M (Value, Ty)
builtin ctx Unit = (,TUnit) <$> letBindComp ctx "Unit" TUnit (Builtin Unit [])
builtin ctx Pair = do
  x <- freshId
  y <- freshId
  let a = TVar (ctxLvl ctx)
      b = TVar (ctxLvl ctx)
      a' = resolveTy ctx a
      b' = resolveTy ctx a
      ty = TForall "a" $ TForall "b" $ TFun a (TFun b (TPair a b))
  pure (Lam "x" x a' $ Comp $ Val $ Lam "y" y b' $ Comp
    $ Builtin Pair [Var x,Var y], ty)
builtin _ b = do -- b is one of Add, Sub, Mul
  x <- freshId
  y <- freshId
  let ty = TFun TInt (TFun TInt TInt)
      int = pure Poly.TInt
  pure (Lam "x" x int $ Comp $ Val $ Lam "y" y int $ Comp
    $ Builtin b [Var x,Var y], ty)

-- | Dereference if it's a hole.
--
-- If it returns a 'THole ref', then 'ref' is guaranteed to be empty
deref :: Ty -> M Ty
deref (THole ref) = liftIO $ go ref
  where
    go = readIORef >=> \case
      Empty _ -> pure $ THole ref
      Filled (THole ref') -> do
        contents <- go ref'
        -- path compression
        writeIORef ref (Filled contents)
        pure contents
      Filled contents -> pure contents
      Generalized _ _ -> error "internal error"
deref x = pure x

-- | Fill an empty hole
fill :: IORef Hole -> Hole -> M ()
fill ref contents = liftIO $ modifyIORef' ref \case
  Empty _ -> contents
  _ -> error "internal error: can only fill empty holes"

-- | Instantiate a 'TForall' with a fresh hole.
--
-- This also requires re-numbering binders:
--  input:  [at lvl 3]  ∀. v₃ -> (∀. v₄)
-- (call: 'instantiate 3 (TFun (TVar 3) ...)')
--  output: [at lvl 3]   [H₃] -> (∀. v₃)
-- (where [H₃] represents an empty hole at level 3)
--
-- Edge case with holes: since the scope of any holes under a quantifier won't
-- include the quantified-over variable, we can safely ignore empty holes when
-- re-numbering binders.
instantiate :: Lvl -> Ty -> M (Ty, IORef Hole)
instantiate lvl ty = do
    newHole <- freshHole lvl
    ty' <- go (THole newHole) ty
    pure (ty', newHole)
  where
    go newHole = deref >=> \case
      TVar l -> pure $ case compare l lvl of
        LT -> TVar l
        EQ -> newHole
        GT -> TVar (l-1)
      TUnit -> pure TUnit
      TInt -> pure TInt
      TPair a b -> TPair <$> go newHole a <*> go newHole b
      TFun a b -> TFun <$> go newHole a <*> go newHole b
      TForall name t -> TForall name <$> go newHole t
      THole ref -> do
        Empty l <- liftIO $ readIORef ref
        unless (l <= lvl) $ error "internal error: scope of hole is too big"
        pure $ THole ref

-- | Lower a type down to a new level
--
-- Suppose you're checking like
--   (∀ x. x -> (∀ y. y)) <: (∀ a. a -> a)
-- or with de Bruijn levels (I picked level 3 arbitrarily)
--   [at lvl 3] ⊢  (∀. v₃ -> (∀. v₄)) <: (∀. v₃ -> v₃)
-- You first instantiate the RHS with a new rigid var, adding it to the context.
-- With de Bruijn levels, this conveniently doesn't change the RHS.
-- but to move the LHS into the context with move variables, we have to
-- re-number all its bindings:
--   [at lvl 4] ⊢  (∀. v₄ -> (∀. v₅)) <: v₃ -> v₃
-- That's what this function does ('moveUnderBinders 3 4 lhs' in this case)
--
-- Edge case with holes: since the scope of any holes under a quantifier won't
-- include the quantified over variable, we can ignore empty holes when
-- re-numbering binders.
moveUnderBinders :: Lvl -> Lvl -> Ty -> M Ty
moveUnderBinders oldLvl newLvl = go
  where
    go = deref >=> \case
      TVar l -> pure $! if l < oldLvl
        then TVar l
        else TVar (l + (newLvl - oldLvl))
      TUnit -> pure TUnit
      TInt -> pure TInt
      TPair a b -> TPair <$> go a <*> go b
      TFun a b -> TFun <$> go a <*> go b
      TForall name ty -> TForall name <$> go ty
      THole ref -> do
        Empty l <- liftIO $ readIORef ref
        unless (l <= oldLvl) $ error "internal error: scope of hole is too big"
        pure $ THole ref

-- | Generalize a let-binding
--
-- TODO: document how this works.
generalizeLet :: Ctx -> Name -> Value -> Ty -> M (Value, Ty)
generalizeLet ctx name val ty = mdo
  let lvl = ctxLvl ctx
  -- important: go returns its result lazily
  let go :: Ty -> StateT Lvl (WriterT (Endo Value) M) Ty
      go (TVar l) = pure $ case compare l lvl of
        LT -> TVar l
        EQ -> error "internal error: should not have type vars of this level"
        GT -> TVar (l - lvl - 1 + lvl')
      go TUnit = pure TUnit
      go TInt = pure TInt
      go (TPair a b) = TPair <$> go a <*> go b
      go (TFun a b) = TFun <$> go a <*> go b
      go (TForall n a) = TForall n <$> go a
      go (THole ref) = liftIO (readIORef ref) >>= \case
        Filled a -> go a
        Generalized l _ -> pure (TVar l)
        Empty l -> if l < lvl then pure (THole ref) else do
          -- add another TLam
          tid <- lift $ lift freshTId
          newBinderLvl <- get
          modify' (+1)
          tell $ Endo $ TLam "t" tid
          -- set the hole to Generalized
          lift $ lift $ fill ref (Generalized newBinderLvl tid)
          pure (TVar newBinderLvl)
  ((ty', lvl'), w) <- runWriterT (runStateT (go ty) lvl)
  let tyWithForalls = iter (lvl'-lvl) (TForall "t") ty'
      valWithTLams = appEndo w val
  (, tyWithForalls) <$> letBind ctx name tyWithForalls valWithTLams


