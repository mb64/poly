{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Unification and polymorphic subtyping
module Elab.Unify where

import Utils
import Elab.Types
import Elab.Utils

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IMap
import Data.IORef
import qualified Data.Text as T
import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class

-- | only need some of the context during unification
data UnifyCtx = UnifyCtx { uctxLvl :: Lvl, uctxTypeNames :: ~(IntMap Name) }

addTyToUnifyCtx :: Name -> UnifyCtx -> UnifyCtx
addTyToUnifyCtx n UnifyCtx{..} = UnifyCtx
  { uctxLvl = uctxLvl + 1
  , uctxTypeNames = IMap.insert uctxLvl n uctxTypeNames }

ctxToUnifyCtx :: Ctx -> UnifyCtx
ctxToUnifyCtx Ctx{..} = UnifyCtx ctxLvl typeNames

-- | Occurs check and scope check
unifyHolePrechecks :: UnifyCtx -> IORef Hole -> Lvl -> TyVal -> M ()
unifyHolePrechecks !ctx ref scope = go ctx
  where
    initialLvl = uctxLvl ctx
    go !ctx = deref >=> \case
      VVar lvl -> when (lvl >= scope && lvl < initialLvl) $ do
        let name = uctxTypeNames ctx IMap.! lvl
        typeError $ "type variable " <> name <> " escaping its scope"
      VFun a b -> go ctx a >> go ctx b
      VForall n a -> go (addTyToUnifyCtx n ctx) (a $$ VVar (uctxLvl ctx))
      VHole h | h == ref -> typeError "occurs check: can't make infinite type"
      VHole h -> do
        Empty l <- liftIO $ readIORef h
        when (l > scope) $ fill h (Empty scope)

-- | Unify two monotypes
--
-- 'unify a b' fills in the holes in 'a' and 'b' so that 'a = b'
unify :: UnifyCtx -> TyVal -> TyVal -> M ()
unify !ctx t1 t2 = liftA2 (,) (deref t1) (deref t2) >>= \case
  (VHole refX, y) -> unifyHoleTy ctx refX y
  (x, VHole refY) -> unifyHoleTy ctx refY x
  (VVar x, VVar y) | x == y -> pure ()
  (VFun a b, VFun a' b') -> unify ctx a a' >> unify ctx b b'
  (VForall name a, VForall _ b) -> do
    let x = VVar (uctxLvl ctx)
    unify (addTyToUnifyCtx name ctx) (a $$ x) (b $$ x)
  (x, y) -> do
    let disp = displayTy (uctxLvl ctx) (uctxTypeNames ctx)
    x' <- disp x
    y' <- disp y
    typeError $ "mismatch between " <> T.pack x' <> " and " <> T.pack y'

-- | unifyHoleTy ref ty: fill in ref to satisfy 'ref = ty'
unifyHoleTy :: UnifyCtx -> IORef Hole -> TyVal -> M ()
unifyHoleTy !ctx refX = deref >=> \case
  VHole refY | refX == refY -> pure ()
  ty -> do
    Empty lvl <- liftIO $ readIORef refX
    unifyHolePrechecks ctx refX lvl ty
    fill refX (Filled ty)

-- | Fancy subsumption for potentially polymorphic types
--
-- 'sub ctx tm a b' fills in the holes in 'a' and 'b' so that 'a <: b'
--
-- It also takes a term 'tm : a' and returns a term with type 'b'
sub :: Ctx -> Value -> TyVal -> TyVal -> M Value
sub !ctx tm t1 t2 = liftA2 (,) (deref t1) (deref t2) >>= \case
  (VHole a, b) -> subHoleTy ctx tm a b
  (a, VHole b) -> subTyHole ctx tm a b
  (a, VForall n b) -> do
    let x = VVar (ctxLvl ctx)
    tlam n \arg -> sub (addTyToCtx n arg ctx) tm a (b $$ x)
  (VForall _ a, b) -> do
    newHole <- VHole <$> freshHole (ctxLvl ctx)
    sub ctx (tapp ctx tm newHole) (a $$ newHole) b
  (VFun a a', VFun b b') -> lam ctx "eta" b \arg -> do
    arg' <- sub ctx arg b a
    tm' <- app ctx a' tm arg'
    sub ctx tm' a' b'
  (a, b) -> unify (ctxToUnifyCtx ctx) a b >> pure tm

-- | 'subHoleTy ctx tm hole ty': fill in hole so that 'hole <: ty'
--
-- Also takes a term 'tm : hole' and coerces it to type 'ty'
subHoleTy :: Ctx -> Value -> IORef Hole -> TyVal -> M Value
subHoleTy !ctx tm hole ty = deref ty >>= \case
  VForall n b -> do
    let x = VVar (ctxLvl ctx)
    tlam n \arg -> subHoleTy (addTyToCtx n arg ctx) tm hole (b $$ x)
  VFun b b' -> do
    liftIO $ putStrLn "subHoleTy of a function"
    Empty scope <- liftIO $ readIORef hole
    a <- freshHole scope
    a' <- freshHole scope
    fill hole $ Filled (VFun (VHole a) (VHole a'))
    lam ctx "eta" b \arg -> do
      arg' <- subTyHole ctx arg b a
      tm' <- app ctx (VHole a') tm arg'
      subHoleTy ctx tm' a' b'
  b -> unifyHoleTy (ctxToUnifyCtx ctx) hole b >> pure tm

-- | 'subTyHole ctx tm ty hole': fill in hole so that 'ty <: hole'
--
-- Also takes a term 'tm : ty' and coerces it to type 'hole'
subTyHole :: Ctx -> Value -> TyVal -> IORef Hole -> M Value
subTyHole !ctx tm ty hole = deref ty >>= \case
  VForall _ a -> do
    newHole <- VHole <$> freshHole (ctxLvl ctx)
    subTyHole ctx (tapp ctx tm newHole) (a $$ newHole) hole
  VFun a a' -> do
    liftIO $ putStrLn "subTyHole of a function"
    Empty scope <- liftIO $ readIORef hole
    b <- freshHole scope
    b' <- freshHole scope
    fill hole $ Filled (VFun (VHole b) (VHole b'))
    lam ctx "eta" (VHole b) \arg -> do
      arg' <- subHoleTy ctx arg b a
      tm' <- app ctx a' tm arg'
      subTyHole ctx tm' a' b'
  a -> unifyHoleTy (ctxToUnifyCtx ctx) hole a >> pure tm



