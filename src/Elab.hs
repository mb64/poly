{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

-- | Type inference and elaboration to the polymorphic core language
module Elab where

import Utils
import Elab.Types
import Elab.Utils
import qualified Src

import Data.Text qualified as T
import Data.HashMap.Strict qualified as HMap
import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Data.IORef
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IMap

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
  (VForall name_a a, VForall name_b b) -> do
    let x = VVar (uctxLvl ctx)
    unify (addTyToUnifyCtx name_a ctx) (a $$ x) (b $$ x)
  (x, y) -> do
    -- TODO: pass around the relevant parts of the context
    typeError "(rigid) unification error :/"

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
    Empty scope <- liftIO $ readIORef hole
    a <- freshHole scope
    a' <- freshHole scope
    fill hole $ Filled (VFun (VHole a) (VHole a'))
    lam ctx "eta" b \arg -> do
      arg' <- subTyHole ctx arg b a
      tm' <- app ctx (VHole a') tm arg'
      subHoleTy ctx tm' a' b'
  b -> unifyHoleTy (ctxToUnifyCtx ctx) hole b >> pure tm

-- | 'subTyHole lvl tm ty hole': fill in hole so that 'ty <: hole'
--
-- Also takes a term 'tm : ty' and coerces it to type 'hole'
subTyHole :: Ctx -> Value -> TyVal -> IORef Hole -> M Value
subTyHole !ctx tm ty hole = deref ty >>= \case
  VForall _ a -> do
    newHole <- VHole <$> freshHole (ctxLvl ctx)
    subTyHole ctx (tapp ctx tm newHole) (a $$ newHole) hole
  VFun a a' -> do
    Empty scope <- liftIO $ readIORef hole
    b <- freshHole scope
    b' <- freshHole scope
    fill hole $ Filled (VFun (VHole b) (VHole b'))
    lam ctx "eta" (VHole b) \arg -> do
      arg' <- subHoleTy ctx arg b a
      tm' <- app ctx a' tm arg'
      subTyHole ctx tm' a' b'
  a -> unifyHoleTy (ctxToUnifyCtx ctx) hole a >> pure tm

-- | The mutually recursive type inference functions

check :: Ctx -> Src.Exp -> TyVal -> M Value
-- check !ctx = uncurry $ traverse deref >=> \case
check !ctx e ty = do
  ty' <- deref ty
  case (e, ty') of
    -- (_, VHole ref) -> do
    --   (tm, a) <- syn ctx e
    --   subTyHole ctx tm a ref
    (_, VForall n a) -> do
      let x = VVar (ctxLvl ctx)
      tlam n \arg -> check (addTyToCtx n arg ctx) e (a $$ x)
    (Src.ELam n Nothing body, VFun a b) -> lam ctx n a \x ->
      check (addVarToCtx n x a ctx) body b
    (Src.ELam n (Just srcTy) body, VFun a b) -> lam ctx n a \x -> do
      a' <- srcTyToTy ctx srcTy
      x' <- sub ctx x a a'
      check (addVarToCtx n x' a' ctx) body b
    (Src.ELet n srcTy val body, a) | Src.isSyntacticValue val -> do
      -- syntactic value: generalize!
      let ctx' = moveDownLevelCtx ctx
      ty <- srcTyToTy ctx' srcTy
      x <- check ctx' val ty
      (x',ty') <- generalizeLet ctx n x ty
      check (addVarToCtx n x' ty' ctx) body a
    (Src.ELet n srcTy val body, a) -> do
      -- value restriction: don't generalize :(
      ty <- srcTyToTy ctx srcTy
      x <- check ctx val ty
      x' <- letBind ctx n ty x
      check (addVarToCtx n x' ty ctx) body a
    _ -> do
      (tm, a) <- syn ctx e
      sub ctx tm a ty

syn :: Ctx -> Src.Exp -> M (Value, TyVal)
syn !ctx e = case e of
  Src.EVar n -> case HMap.lookup n (boundVars ctx) of
    Nothing -> typeError $ "variable " <> n <> " not in scope"
    Just (val,ty) -> pure (val,ty)
  Src.EAnnot e' srcTy -> do
    ty <- srcTyToTy ctx srcTy
    tm <- check ctx e' ty
    pure (tm, ty)
  Src.EApp f arg -> do
    (f', funcTy) <- syn ctx f
    apply ctx funcTy f' arg
  Src.ELam n srcTy body -> do
    -- a <- case srcTy of
    --   Nothing -> THole <$> freshHole lvl
    --   Just srcTy -> srcTyToTy lvl srcTy
    a <- maybe (VHole <$> freshHole (ctxLvl ctx)) (srcTyToTy ctx) srcTy
    fmap (VFun a) <$> synlam ctx n a \x ->
      syn (addVarToCtx n x a ctx) body
  Src.ELet n srcTy val body | Src.isSyntacticValue val -> do
    -- syntactic value: generalize!
    let ctx' = moveDownLevelCtx ctx
    ty <- srcTyToTy ctx' srcTy
    x <- check ctx' val ty
    (x',ty') <- generalizeLet ctx n x ty
    -- for debugging:
    liftIO . putStrLn . ((T.unpack n ++ " : ") ++) =<< displayTyCtx ctx ty'
    syn (addVarToCtx n x' ty' ctx) body
  Src.ELet n srcTy val body -> do
    -- value restriction: don't generalize :(
    ty <- srcTyToTy ctx srcTy
    x <- check ctx val ty
    x' <- letBind ctx n ty x
    syn (addVarToCtx n x' ty ctx) body


-- | Helper function for the 'EApp' case in 'syn'.
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





