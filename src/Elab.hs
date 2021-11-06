{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}

-- | Type inference and elaboration to the polymorphic core language
--
-- This module ties everything together to implement the mutually recursive type
-- inference functions
module Elab where

import Utils
import Elab.Types
import Elab.Utils
import Elab.Unify
import qualified Src
import qualified Poly

import Data.Text qualified as T
import Data.HashMap.Strict qualified as HMap
import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Data.IORef
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IMap

-- | The mutually recursive type inference functions

check :: Ctx -> Src.Exp -> TyVal -> M Value
-- check !ctx = uncurry $ traverse deref >=> \case
check !ctx e ty = do
  ty' <- deref ty
  case (e, ty') of
    (_, VForall n a) -> do
      let x = VVar (ctxLvl ctx)
      tlam n \arg -> check (addTyToCtx n arg ctx) e (a $$ x)
    (Src.ELam n Nothing body, VFun a b) -> lam ctx n a \x ->
      check (addVarToCtx n x a ctx) body b
    (Src.ELam n (Just srcTy) body, VFun a b) -> lam ctx n a \x -> do
      a' <- srcTyToTy ctx srcTy
      x' <- sub ctx x a a'
      check (addVarToCtx n x' a' ctx) body b
    (Src.ELet defn body, a) -> do
      ctx' <- define ctx defn
      check ctx' body a
    (Src.ECase _ _, a) -> error "TODO"
    (Src.EIf cond then_ else_, a) -> do
      c <- check ctx cond (error "TODO: add built-in types to context")
      t <- check ctx then_ a
      e <- check ctx else_ a
      pure (error "TODO")
    _ -> do
      (tm, a) <- infer ctx e
      sub ctx tm a ty

infer :: Ctx -> Src.Exp -> M (Value, TyVal)
infer !ctx e = case e of
  Src.ELit x -> do
    -- pure (lit x, the int type)
    error "TODO: add built-in types to context"
  Src.EVar n -> case HMap.lookup n (boundVars ctx) of
    Nothing -> typeError $ "variable " <> n <> " not in scope"
    Just (val,ty) -> pure (val,ty)
  Src.EAnnot e' srcTy -> do
    ty <- srcTyToTy ctx srcTy
    tm <- check ctx e' ty
    pure (tm, ty)
  Src.EApp f arg -> do
    (f', funcTy) <- infer ctx f
    apply ctx funcTy f' arg
  Src.ELam n srcTy body -> do
    a <- maybe (VHole <$> freshHole (ctxLvl ctx)) (srcTyToTy ctx) srcTy
    fmap (VFun a) <$> inferLam ctx n a \x ->
      infer (addVarToCtx n x a ctx) body
  Src.ELet defn body -> do
    ctx' <- define ctx defn
    infer ctx' body
  Src.ECase _ _ -> error "TODO"
  Src.EIf cond then_ else_ -> do
    c <- check ctx cond (error "TODO: add built-in types to context")
    (t, ty) <- infer ctx then_
    e <- check ctx else_ ty
    pure (error "TODO", ty)

-- | Helper function for the 'EApp' case in 'infer'.
--
-- If 'f : fTy', 'apply ctx lvl fTy f x' returns '(f x, resultTy)' where
-- 'f x : resultTy'
apply :: Ctx -> TyVal -> Value -> Src.Exp -> M (Value, TyVal)
apply !ctx fTy f x = deref fTy >>= \case
  VFun a b -> do
    x' <- check ctx x a
    fx <- app ctx b f x'
    pure (fx, b)
  VForall _ a -> do
    newHole <- VHole <$> freshHole (ctxLvl ctx)
    apply ctx (a $$ newHole) (tapp ctx f newHole) x
  VHole ref -> do
    Empty scope <- liftIO $ readIORef ref
    a <- VHole <$> freshHole scope
    b <- VHole <$> freshHole scope
    fill ref (Filled (VFun a b))
    x' <- check ctx x a
    fx <- app ctx b f x'
    pure (fx, b)
  _ -> typeError "should be a function type"


-- | Helper function for lets (for both check and infer directions)
define :: Ctx -> Src.Defn -> M Ctx
define !ctx (Src.Val n srcTy e) = do
  -- non-generalizing, non-recursive let
  ty <- srcTyToTy ctx srcTy
  x <- check ctx e ty
  x' <- letBind ctx n ty x
  pure (addVarToCtx n x' ty ctx)

define !ctx (Src.Fun n srcTy e) = do
  -- generalizing letrec
  let ctx' = moveDownLevelCtx ctx
  ty <- srcTyToTy ctx' srcTy
  (ty', val) <- letRec ctx' n ty \val -> mdo
    -- fuck it, recursive do
    x <- check (addVarToCtx n this ty ctx') e ty
    (tids, ty') <- generalizeLet ctx ty
    let this = foldr (\tid v -> Poly.TApp v (pure (Poly.TVar tid))) val tids
    pure (ty', foldr (Poly.TLam "t") x tids)
  -- for debugging:
  liftIO . putStrLn . ((T.unpack n ++ " : ") ++) =<< displayTyCtx ctx ty'
  pure (addVarToCtx n val ty' ctx)

define !ctx (Src.Datatype n constrs) = do
  error "TODO"


