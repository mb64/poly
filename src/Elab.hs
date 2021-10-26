{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

-- | Type inference and elaboration to the polymorphic core language
module Elab where

import ElabUtils
import qualified Src

import Data.Text (Text)
import Data.Text qualified as T
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Control.Exception
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
      TForall a b -> error "it was supposed to be a monotype?"
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
  -- TODO: pass around a mapping from type variables to their names in order to
  -- pretty-print the types in the error message
  _ -> typeError "(rigid) unification error :/"


-- | Fancy subsumption for potentially polymorphic types
--
-- 'sub lvl tm a b' fills in the holes in 'a' and 'b' so that 'a <: b'
--
-- It also takes a term 'tm : a' and returns a term with type 'b'
sub :: Lvl -> Value -> Ty -> Ty -> M Value
sub !lvl tm t1 t2 = liftA2 (,) (deref t1) (deref t2) >>= \case
  (THole x, y) -> subHoleTy lvl tm x y
  (x, THole y) -> subTyHole lvl tm x y
  (x, TForall n y) -> do
    x' <- moveUnderBinders lvl (lvl+1) x
    tlam n $ sub (lvl+1) tm x' y
  (TForall _ x, y) -> do
    (x', hole) <- instantiate lvl x
    tm' <- tapp tm (THole hole)
    sub lvl tm' x' y
  (TFun ax bx, TFun ay by) -> lam "eta" ay \arg -> do
    arg' <- sub lvl arg ay ax
    tm' <- app bx tm arg'
    sub lvl tm' bx by
  (x, y) -> unify x y >> pure tm -- everything else is a monotype

-- | 'subHoleTy lvl tm ref ty': fill in ref so that 'ref <: ty'
--
-- Also takes a term 'tm : ref' and returns a term with type 'ty'
subHoleTy :: Lvl -> Value -> IORef Hole -> Ty -> M Value
subHoleTy !lvl tm ref ty = deref ty >>= \case
  TForall n a ->
    tlam n $ subHoleTy (lvl + 1) tm ref a
  TFun a b -> do
    Empty l <- liftIO $ readIORef ref
    aRef <- freshHole l
    bRef <- freshHole l
    fill ref $ Filled (TFun (THole aRef) (THole bRef))
    lam "eta" a \arg -> do
      arg' <- subTyHole lvl arg a aRef
      tm' <- app (THole bRef) tm arg'
      subHoleTy lvl tm' bRef b
  a -> unifyHoleTy ref a >> pure tm -- everything else is a monotype

-- | 'subTyHole lvl tm ty ref': fill in ref so that 'ty <: ref'
--
-- Also takes a term 'tm : ty' and returns a term with type 'ref'
subTyHole :: Lvl -> Value -> Ty -> IORef Hole -> M Value
subTyHole !lvl tm ty ref = deref ty >>= \case
  TForall _ a -> do
    (a',hole) <- instantiate lvl a
    tm' <- tapp tm (THole hole)
    subTyHole lvl tm' a' ref
  TFun a b -> do
    Empty l <- liftIO $ readIORef ref
    aRef <- freshHole l
    bRef <- freshHole l
    fill ref $ Filled (TFun (THole aRef) (THole bRef))
    lam "eta" (THole aRef) \arg -> do
      arg' <- subHoleTy lvl arg aRef a
      tm' <- app b tm arg'
      subTyHole lvl tm' b bRef
  a -> unifyHoleTy ref a >> pure tm -- everything else is a monotype

-- | The mutually recursive type inference functions (finally)

type Ctx = Map Name (Value, Ty)

check :: Ctx -> Lvl -> Src.Exp -> Ty -> M Value
-- check !ctx !lvl = uncurry $ traverse deref >=> \case
check !ctx !lvl e ty = do
  ty' <- deref ty
  case (e, ty') of
    (_, THole ref) -> do
      (tm, a) <- syn ctx lvl e
      subHoleTy lvl tm ref a
    (_, TForall n a) -> tlam n $ check ctx (lvl + 1) e a
    (Src.ELam n Nothing body, TFun a b) -> lam n a \x ->
      check (Map.insert n (x,a) ctx) lvl body b
    (Src.ELam n (Just srcTy) body, TFun a b) -> lam n a \x -> do
      a' <- srcTyToTy lvl srcTy
      x' <- sub lvl x a a'
      check (Map.insert n (x',a') ctx) lvl body b
    (Src.ELam _ _ _, _) -> typeError "didn't expect a function"
    (Src.ELet n Nothing val body, a) | Src.isSyntacticValue val -> do
      -- syntactic value: generalize!
      (x,ty) <- underExtendedCtx (error "no type here") $ syn ctx (lvl+1) val
      (x',ty') <- generalizeLet lvl n x ty
      check (Map.insert n (x',ty') ctx) lvl body a
    (Src.ELet n Nothing val body, a) -> do
      -- value restriction: don't generalize :(
      liftIO $ putStrLn $ "not generalizing " ++ show n
      (x,ty) <- syn ctx lvl val
      check (Map.insert n (x,ty) ctx) lvl body a
    (Src.ELet n (Just srcTy) val body, a) -> do
      -- TODO: this should also have generalization for when there's a
      -- partial type signature
      ty <- srcTyToTy lvl srcTy
      x <- check ctx lvl val ty
      x' <- letBind n ty x
      check (Map.insert n (x',ty) ctx) lvl body a
    _ -> do
      (tm, a) <- syn ctx lvl e
      sub lvl tm a ty

syn :: Ctx -> Lvl -> Src.Exp -> M (Value, Ty)
syn !ctx !lvl e = case e of
  Src.EVar n ->
    maybe (typeError $ "variable " <> n <> " not in scope") pure
      $ Map.lookup n ctx
  Src.EAnnot e' srcTy -> do
    ty <- srcTyToTy lvl srcTy
    tm <- check ctx lvl e' ty
    pure (tm, ty)
  Src.EApp f arg -> do
    (f', funcTy) <- syn ctx lvl f
    apply ctx lvl funcTy f' arg
  Src.ELam n srcTy body -> do
    -- a <- case srcTy of
    --   Nothing -> THole <$> freshHole lvl
    --   Just srcTy -> srcTyToTy lvl srcTy
    a <- maybe (THole <$> freshHole lvl) (srcTyToTy lvl) srcTy
    fmap (TFun a) <$> synlam n a \x ->
      syn (Map.insert n (x, a) ctx) lvl body
  Src.ELet n Nothing val body | Src.isSyntacticValue val -> do
    -- syntactic value: generalize!
    (x,ty) <- underExtendedCtx (error "no type here") $ syn ctx (lvl+1) val
    (x',ty') <- generalizeLet lvl n x ty
    -- for debugging:
    liftIO $ putStrLn . ((T.unpack n ++ " : ") ++) =<< debugTy lvl ty'
    syn (Map.insert n (x',ty') ctx) lvl body
  Src.ELet n Nothing val body -> do
    -- value restriction: don't generalize :(
    (x,ty) <- syn ctx lvl val
    syn (Map.insert n (x,ty) ctx) lvl body
  Src.ELet n (Just srcTy) val body -> do
    -- TODO: this should also have generalization for when there's a partial
    -- type signature
    ty <- srcTyToTy lvl srcTy
    x <- check ctx lvl val ty
    x' <- letBind n ty x
    syn (Map.insert n (x',ty) ctx) lvl body

  Src.ELit x -> pure (lit x, TInt)
  Src.EBuiltin b -> builtin lvl b


-- | Helper function for the 'EApp' case in 'syn'.
--
-- If 'f : fTy', 'apply ctx lvl fTy f x' returns '(f x, resultTy)' where
-- 'f x : resultTy'
apply :: Ctx -> Lvl -> Ty -> Value -> Src.Exp -> M (Value, Ty)
apply ctx !lvl fTy f x = deref fTy >>= \case
  TForall n ty -> do
    (ty', hole) <- instantiate lvl ty
    f' <- tapp f (THole hole)
    apply ctx lvl ty' f' x
  TFun a b -> do
    x' <- check ctx lvl x a
    fx <- app b f x'
    pure (fx, b)
  THole ref -> do
    Empty l <- liftIO $ readIORef ref
    a <- THole <$> freshHole l
    b <- THole <$> freshHole l
    fill ref (Filled (TFun a b))
    x' <- check ctx lvl x a
    fx <- app b f x'
    pure (fx, b)
  _ -> typeError "should be a function type"





