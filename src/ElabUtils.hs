{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Monad and utils used by the elaborator to generate core IR.
--
-- This module defines three things:
--  * The 'Ty' datatype used during elaboration, and some helper functions on it
--  * The monad 'M' that elaboration operates in
--  * Smart constructors for the 'Poly' IR, including getting the type of a
--    built-in
module ElabUtils
  ( Lvl
  , Name
  , Hole(..)
  , Ty(..)
  , srcTyToTy
  , Value
  , M
  , runM
  , TypeError(..)
  , typeError
  , var
  , lit
  , app
  , lam
  , synlam
  , tapp
  , tlam
  , letBind
  , builtin
  , deref
  , fill
  , freshHole
  , instantiate
  , moveUnderBinders
  , generalizeLet
) where

import Poly hiding (Value, Ty(..))
import Poly qualified
import Src qualified
import Builtins

import Data.Text (Text)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IMap
import Data.Map.Strict qualified as Map
-- import Control.Monad.Cont
-- import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.Writer.CPS
import Control.Monad.RWS.Strict
import Control.Exception (Exception, throw)
import Data.Coerce
import Data.IORef
import Data.Monoid
import Debug.Trace

type Lvl = Int

-- | A hole in a type.
--
-- The level in 'Empty lvl' represents its scope: when filling it in, the only
-- allowed type variables are those < lvl.
data Hole = Empty Lvl | Filled Ty

data Ty = TVar Lvl
        | TFun Ty Ty
        | TForall Name Ty -- the name is just for pretty-printing
        | THole (IORef Hole)
        -- TODO: these can all eventually be coalesced into a single variant for
        -- rigid type constructors
        | TUnit
        | TInt
        | TPair Ty Ty

-- Two invariants about holes and foralls:
--  * No impredicativity: don't put a Forall in a Hole
--  * Scope of holes: in '∀ x. ... [H] ...', the scope of the hole '[H]' never
--    includes the type variable 'x'.


-- | Convert a source-code 'Src.Ty' to a typechecker 'Ty', at a given level
--
-- TODO: check the type isn't impredicative
srcTyToTy :: Lvl -> Src.Ty -> Ty
srcTyToTy = go Map.empty
  where
    go !env !lvl (Src.TVar name) = -- TODO better errors
      Map.findWithDefault (error "type variable not in scope") name env
    go !env !lvl Src.TUnit = TUnit
    go !env !lvl Src.TInt = TInt
    go !env !lvl (Src.TPair a b) = TPair (go env lvl a) (go env lvl b)
    go !env !lvl (Src.TFun a b) = TFun (go env lvl a) (go env lvl b)
    go !env !lvl (Src.TForall name ty) =
      TForall name $ go (Map.insert name (TVar lvl) env) (lvl + 1) ty


-- General strategy: we first build up a `Exp' GonnaBeATy`, where each
-- 'GonnaBeATy' action converts 'Ty's to 'Poly.Ty's (using 'resolveTy').
--
-- Then at the end we use 'sequence' to run all the 'GonnaBeATy's and get an
-- `Exp' Poly.Ty`.
--
-- We need to do that conversion at the end bc during elaboration the types
-- still have holes in them.
--
-- Differences between 'Ty' and 'Poly.Ty':
--  * 'Ty's can have holes
--  * Type variables in 'Ty' are represented with de Bruijn levels

type GonnaBeATy = StateT Int IO Poly.Ty
--                ^^^^^^^^^^ for generating fresh type ids

type Value = Poly.Value' GonnaBeATy

-- | The elaboration monad.
--
--            read-only state: currently-in-scope type vars
--            vvv                          vvv read-write state for fresh ids
type M = RWST Ctx (Endo (Exp' GonnaBeATy)) Int IO
--                ^^^^^^^^^^^^^^^^^^^^^^^^
--                write-only state for building up 'let's in the IR

data Ctx = Ctx Lvl (IntMap Poly.Ty) deriving Show

runM :: M (a, Exp' GonnaBeATy) -> IO (a, Exp)
runM ma = do
  ((a, exp), s, lets) <- runRWST ma (Ctx 0 IMap.empty) 0
  (a,) <$> evalStateT (sequence $ appEndo lets exp) s

-- TODO: nicer type errors
newtype TypeError = TypeError Text deriving (Show)
instance Exception TypeError

typeError :: Text -> M a
typeError = liftIO . throw . TypeError


-- some local helper functions
runLocally :: (a -> Exp' GonnaBeATy) -> M a -> M (a, Exp' GonnaBeATy)
runLocally k ma = pass $ do
  (a, lets) <- listen ma
  pure ((a, appEndo lets (k a)), const mempty)

fresh :: M Id
fresh = state \i -> (Id i, i + 1)

freshTy :: M TId
freshTy = state \i -> (TId i, i + 1)

letBindComp :: Name -> Ty -> Comp' GonnaBeATy -> M Value
letBindComp n ty e = do
  ident <- fresh
  ctx <- ask
  tell $ Endo $ Let n ident (resolveTy ctx ty) e
  pure (Var ident)

extendCtx :: Poly.Ty -> Ctx -> Ctx
extendCtx ty (Ctx lvl env) =
  Ctx (lvl + 1) (IMap.insert lvl ty env)


-- smart constructors for IR values
var :: Id -> Value
var = Var

lit :: Int -> Value
lit = Lit

letBind :: Name -> Ty -> Value -> M Value
letBind n ty val =
  if simple val
    then pure val
    else letBindComp n ty (Val val)
  where
    simple v = case v of
      Var _ -> True
      Lit _ -> True
      TApp v' _ -> simple v'
      TLam _ _ v' -> simple v'
      _ -> False

app :: Ty -> Value -> Value -> M Value
app ty f x = letBindComp "tmp" ty (App f x)

tapp :: Value -> Ty -> M Value
tapp x a = do
  ctx <- ask
  pure (TApp x (resolveTy ctx a))

-- | Like 'lam' but with a more convenient type signature for the 'syn' function
synlam :: Name -> Ty -> (Value -> M (Value, Ty)) -> M (Value, Ty)
synlam n a f = do
  ident <- fresh
  ((_, b), body) <- runLocally (Comp . Val . fst) $ f (Var ident)
  ctx <- ask
  pure (Lam n ident (resolveTy ctx a) body, b)

lam :: Name -> Ty -> (Value -> M Value) -> M Value
lam n a f = do
  ident <- fresh
  (_, body) <- runLocally (Comp . Val) $ f (Var ident)
  ctx <- ask
  pure (Lam n ident (resolveTy ctx a) body)
  -- fst <$> synlam n a \arg -> (,b) <$> f arg

tlam :: Name -> M Value -> M Value
tlam n tm = do
  tid <- freshTy
  (_, body) <- runLocally (Comp . Val) $ local (extendCtx (Poly.TVar tid)) tm
  case body of
    Comp (Val v) -> pure (TLam n tid v)
    _ -> typeError "Value restriction: not a value!"

-- TODO: this is very special-cased. Figure out a more systematic way to do
-- this?
builtin :: Lvl -> Builtin -> M (Value, Ty)
builtin _ Unit = (,TUnit) <$> letBindComp "Unit" TUnit (Builtin Unit [])
builtin lvl Pair = do
  x <- fresh
  y <- fresh
  ctx <- ask
  let a = TVar lvl
      b = TVar lvl
      a' = resolveTy ctx a
      b' = resolveTy ctx a
      ty = TForall "a" $ TForall "b" $ TFun a (TFun b (TPair a b))
  pure (Lam "x" x a' $ Comp $ Val $ Lam "y" y b' $ Comp
    $ Builtin Pair [Var x,Var y], ty)
builtin _ b = do -- b is one of Add, Sub, Mul
  x <- fresh
  y <- fresh
  ctx <- ask
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
    go ref = readIORef ref >>= \case
      Empty _ -> pure $ THole ref
      Filled (THole ref') -> do
        contents <- go ref'
        -- path compression
        writeIORef ref (Filled contents)
        pure contents
      Filled contents -> pure contents
deref x = pure x

-- | Fill an empty hole
fill :: IORef Hole -> Hole -> M ()
fill ref contents = liftIO $ modifyIORef' ref \case
  Empty _ -> contents
  Filled _ -> error "internal error: can only fill empty holes"

-- | A fresh hole at the specified level
freshHole :: Lvl -> M (IORef Hole)
freshHole l = liftIO $ newIORef (Empty l)

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
-- It's also used in let-generalization, which introduces new foralls at the
-- start of a type, and so needs to shift the type over.
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
generalizeLet :: Lvl -> Name -> Value -> Ty -> M (Value, Ty)
generalizeLet lvl n val ty = do
    ((ty', lvl'), w) <- runWriterT (runStateT (go ty) lvl)
    ty'' <- iter (lvl'-lvl) (TForall "t") <$> moveUnderBinders (lvl+1) lvl' ty'
    val' <- letBind n ty'' (appEndo w val)
    pure (val', ty'')
  where
    go :: Ty -> StateT Lvl (WriterT (Endo Value) M) Ty
    go = lift . lift . deref >=> \case
      TVar l -> pure $ TVar l
      TUnit -> pure TUnit
      TInt -> pure TInt
      TPair a b -> TPair <$> go a <*> go b
      TFun a b -> TFun <$> go a <*> go b
      THole ref -> do
        Empty l <- liftIO $ readIORef ref
        if l < lvl then pure $ THole ref else do
          tid <- lift $ lift freshTy
          tell $ Endo $ TLam "t" tid
          -- HACK (see below)
          liftIO $ writeIORef ref $! Filled (TVar (-coerce tid-1))
          tlamLvl <- get
          modify' (+1)
          pure $ TVar tlamLvl
    -- TODO: this does not fuse, due to cross-module inlining issues.
    -- Probably worth filing a GHC bug report.
    iter n f x = iterate f x !! n


resolveTy :: Ctx -> Ty -> StateT Int IO Poly.Ty
resolveTy ctx@(Ctx lvl env) ty = case ty of
  TVar lvl -> pure $ env IMap.! lvl
  TUnit -> pure Poly.TUnit
  TInt -> pure Poly.TInt
  TPair a b -> Poly.TPair <$> resolveTy ctx a <*> resolveTy ctx b
  TFun a b -> Poly.TFun <$> resolveTy ctx a <*> resolveTy ctx b
  TForall n ty' -> do
    tid <- state \i -> (TId i, i + 1)
    let ctx' = extendCtx (Poly.TVar tid) ctx
    Poly.TForall n tid <$> resolveTy ctx' ty'
  THole ref -> do
    contents <- liftIO $ readIORef ref
    case contents of
      Empty _ -> error "ambiguous type" -- TODO better error
      -- HACK: (Filled (TVar -tid-1)) is used to denote tyvars that have been
      -- generalized with TLam argument 'tid'
      Filled (TVar l)
        | l < 0 -> pure $ Poly.TVar (TId (-l-1))
      Filled ty -> resolveTy ctx ty


