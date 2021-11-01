{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

-- | Type inference and elaboration to the polymorphic core language
module Elab where

import Elab.Types
import Elab.Utils
import qualified Src

import Data.Text qualified as T
import Data.HashMap.Strict qualified as HMap
import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Data.IORef

-- | Occurs check and scope check
unifyHolePreChecks :: IORef Hole -> Lvl -> Ty -> M ()
unifyHolePreChecks ref lvl = go
  where
    go = deref >=> \case
      TVar v ->
        if v < lvl
        then pure ()
        else typeError "type variable escaping its scope"
      TUnit -> pure ()
      TInt -> pure ()
      TPair a b -> go a >> go b
      TFun a b -> go a >> go b
      TForall _ _ -> error "it was supposed to be a monotype?" -- TODO don't
      THole r ->
        if r == ref
        then typeError "occurs check: infinite type"
        else do
          Empty l <- liftIO $ readIORef r
          when (l > lvl) $ fill r (Empty lvl)

-- | unifyHoleTy ref ty: fill in ref to satisfy 'ref = ty'
-- ref must be empty
unifyHoleTy :: IORef Hole -> Ty -> M ()
unifyHoleTy refX = deref >=> \case
  THole refY | refX == refY -> pure ()
  THole refY | otherwise -> do
    Empty lvlX <- liftIO $ readIORef refX
    Empty lvlY <- liftIO $ readIORef refY
    if lvlX > lvlY
      then fill refX (Filled (THole refY))
      else fill refY (Filled (THole refX))
  ty -> do
    Empty lvl <- liftIO $ readIORef refX
    unifyHolePreChecks refX lvl ty
    fill refX (Filled ty)

-- | Unify two monotypes
--
-- 'unify a b' fills in the holes in 'a' and 'b' so that 'a = b'
unify :: Ty -> Ty -> M ()
unify t1 t2 = liftA2 (,) (deref t1) (deref t2) >>= \case
  (THole refX, y) -> unifyHoleTy refX y
  (x, THole refY) -> unifyHoleTy refY x
  (TVar x, TVar y)
    | x == y -> pure ()
    | otherwise -> typeError "I should give the tyvars nice names"
  (TPair a b, TPair a' b') -> unify a a' >> unify b b'
  (TFun a b, TFun a' b') -> unify a a' >> unify b b'
  (TUnit, TUnit) -> pure ()
  (TInt, TInt) -> pure ()
  (TForall _ _, _) -> error "should be monotype?"
  (_, TForall _ _) -> error "should be monotype?"
  (x, y) -> do
    -- TODO: pass around a mapping from type variables to their names in order to
    -- pretty-print the types in the error message
    -- x' <- liftIO $ debugTy lvl x
    -- y' <- liftIO $ debugTy lvl y
    -- typeError $ "mismatch between " <> T.pack x' <> " and " <> T.pack y'
    typeError "(rigid) unification error :/"


-- | Fancy subsumption for potentially polymorphic types
--
-- 'sub ctx tm a b' fills in the holes in 'a' and 'b' so that 'a <: b'
--
-- It also takes a term 'tm : a' and returns a term with type 'b'
sub :: Ctx -> Value -> Ty -> Ty -> M Value
sub !ctx tm t1 t2 = liftA2 (,) (deref t1) (deref t2) >>= \case
  (THole x, y) -> subHoleTy ctx tm x y
  (x, THole y) -> subTyHole ctx tm x y
  (x, TForall n y) -> do
    x' <- moveUnderBinders (ctxLvl ctx) (ctxLvl ctx+1) x
    tlam n \arg -> sub (addTyToCtx n arg ctx) tm x' y
  (TForall _ x, y) -> do
    (x', hole) <- instantiate (ctxLvl ctx) x
    sub ctx (tapp ctx tm (THole hole)) x' y
  (TFun ax bx, TFun ay by) -> lam ctx "eta" ay \arg -> do
    arg' <- sub ctx arg ay ax
    tm' <- app ctx bx tm arg'
    sub ctx tm' bx by
  (x, y) -> unify x y >> pure tm -- everything else is a monotype

-- | 'subHoleTy ctx tm ref ty': fill in ref so that 'ref <: ty'
--
-- Also takes a term 'tm : ref' and coerces it to type 'ty'
subHoleTy :: Ctx -> Value -> IORef Hole -> Ty -> M Value
subHoleTy !ctx tm ref ty = deref ty >>= \case
  TForall n a ->
    tlam n \arg -> subHoleTy (addTyToCtx n arg ctx) tm ref a
  TFun a b -> do
    Empty l <- liftIO $ readIORef ref
    aRef <- freshHole l
    bRef <- freshHole l
    fill ref $ Filled (TFun (THole aRef) (THole bRef))
    lam ctx "eta" a \arg -> do
      arg' <- subTyHole ctx arg a aRef
      tm' <- app ctx (THole bRef) tm arg'
      subHoleTy ctx tm' bRef b
  a -> unifyHoleTy ref a >> pure tm -- everything else is a monotype

-- | 'subTyHole lvl tm ty ref': fill in ref so that 'ty <: ref'
--
-- Also takes a term 'tm : ty' and coerces it to type 'ref'
subTyHole :: Ctx -> Value -> Ty -> IORef Hole -> M Value
subTyHole !ctx tm ty ref = deref ty >>= \case
  TForall _ a -> do
    (a',hole) <- instantiate (ctxLvl ctx) a
    subTyHole ctx (tapp ctx tm (THole hole)) a' ref
  TFun a b -> do
    Empty l <- liftIO $ readIORef ref
    aRef <- freshHole l
    bRef <- freshHole l
    fill ref $ Filled (TFun (THole aRef) (THole bRef))
    lam ctx "eta" (THole aRef) \arg -> do
      arg' <- subHoleTy ctx arg aRef a
      tm' <- app ctx b tm arg'
      subTyHole ctx tm' b bRef
  a -> unifyHoleTy ref a >> pure tm -- everything else is a monotype

-- | The mutually recursive type inference functions (finally)

check :: Ctx -> Src.Exp -> Ty -> M Value
-- check !ctx = uncurry $ traverse deref >=> \case
check !ctx e ty = do
  ty' <- deref ty
  case (e, ty') of
    (_, THole ref) -> do
      (tm, a) <- syn ctx e
      subTyHole ctx tm a ref
    (_, TForall n a) ->
      tlam n \arg -> check (addTyToCtx n arg ctx) e a
    (Src.ELam n Nothing body, TFun a b) -> lam ctx n a \x ->
      check (addVarToCtx n x a ctx) body b
    (Src.ELam n (Just srcTy) body, TFun a b) -> lam ctx n a \x -> do
      a' <- srcTyToTy ctx srcTy
      x' <- sub ctx x a a'
      check (addVarToCtx n x' a' ctx) body b
    (Src.ELam _ _ _, _) -> typeError "didn't expect a function"
    (Src.ELet n srcTy val body, a) | Src.isSyntacticValue val -> do
      -- syntactic value: generalize!
      -- TODO: 'addLvlToCtx' function
      let ctx' = ctx { ctxLvl = ctxLvl ctx + 1 }
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

syn :: Ctx -> Src.Exp -> M (Value, Ty)
syn !ctx e = case e of
  Src.EVar n -> do
    (val,lvl,ty) <- maybe (typeError $ "variable " <> n <> " not in scope") pure
                      $ HMap.lookup n (boundVars ctx)
    case compare lvl (ctxLvl ctx) of
      EQ -> pure (val, ty)
      GT -> error "internal error"
      LT -> (val,) <$> moveUnderBinders lvl (ctxLvl ctx) ty
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
    a <- maybe (THole <$> freshHole (ctxLvl ctx)) (srcTyToTy ctx) srcTy
    fmap (TFun a) <$> synlam ctx n a \x ->
      syn (addVarToCtx n x a ctx) body
  Src.ELet n srcTy val body | Src.isSyntacticValue val -> do
    -- syntactic value: generalize!
    let ctx' = ctx { ctxLvl = ctxLvl ctx + 1 }
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

  Src.ELit x -> pure (lit x, TInt)
  Src.EBuiltin b -> builtin ctx b


-- | Helper function for the 'EApp' case in 'syn'.
--
-- If 'f : fTy', 'apply ctx lvl fTy f x' returns '(f x, resultTy)' where
-- 'f x : resultTy'
apply :: Ctx -> Ty -> Value -> Src.Exp -> M (Value, Ty)
apply !ctx fTy f x = deref fTy >>= \case
  TForall n ty -> do
    (ty', hole) <- instantiate (ctxLvl ctx) ty
    apply ctx ty' (tapp ctx f (THole hole)) x
  TFun a b -> do
    x' <- check ctx x a
    fx <- app ctx b f x'
    pure (fx, b)
  THole ref -> do
    Empty l <- liftIO $ readIORef ref
    a <- THole <$> freshHole l
    b <- THole <$> freshHole l
    fill ref (Filled (TFun a b))
    x' <- check ctx x a
    fx <- app ctx b f x'
    pure (fx, b)
  _ -> typeError "should be a function type"





