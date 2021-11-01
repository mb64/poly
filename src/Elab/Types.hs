{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Datatypes used for type checking, and helper functions to convert to/from
-- other datatypes.
--
-- It also contains a couple generally useful helper functions
module Elab.Types where

import Utils
import Poly qualified
import Src qualified

import Control.Monad.RWS.Strict
import Control.Monad.State.Strict
import Control.Exception (Exception, throw)
import Data.Text (Text)
import Data.Text qualified as T
import Data.IORef
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IMap
import Data.Map.Strict qualified as Map
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HMap


type Lvl = Int

-- | A hole in a type.
data Hole
  = Filled Ty
  | Empty Lvl
  -- ^ The level represents its scope: when filling it in, the  only allowed
  -- type variables are those < lvl.
  | Generalized Lvl Poly.TId
  -- ^ The hole was filled during let-generalization.
  -- During let-generalization, holes get filled with 'Generalized Lvl TId'

-- | Differences between 'Ty' and 'Poly.Ty':
--  * Typechecker 'Ty's can have holes
--  * Type variables in 'Ty' are represented with de Bruijn levels
--    (TODO: represent them with 'TIds' instead)
data Ty = TVar Lvl
        | TFun Ty Ty
        | TForall Name Ty -- the name is just for pretty-printing
        | THole (IORef Hole)
        -- TODO: these can all eventually be coalesced into a single variant for
        -- rigid type constructors
        | TUnit
        | TInt
        | TPair Ty Ty

-- An invariant about the scope of holes: in '∀ x. ... [H] ...', the scope of
-- the hole '[H]' never includes the type variable 'x'.


-- | Read-only state used during elaboration
data Ctx = Ctx
  { ctxLvl :: Lvl
  , typeTIds :: IntMap Poly.Ty
  , typeNames :: ~(IntMap Name)
  , boundVars :: HashMap Name (Value,Lvl,Ty)
  }

addTyToCtx :: Name -> Poly.Ty -> Ctx -> Ctx
addTyToCtx n ty Ctx{..} = Ctx
  { ctxLvl = ctxLvl + 1
  , typeTIds = IMap.insert ctxLvl ty typeTIds
  , typeNames = IMap.insert ctxLvl n typeNames
  , boundVars = boundVars }

addVarToCtx :: Name -> Value -> Ty -> Ctx -> Ctx
addVarToCtx n val ty ctx =
  ctx { boundVars = HMap.insert n (val,ctxLvl ctx,ty) (boundVars ctx) }

-- TODO: nicer type errors
newtype TypeError = TypeError Text deriving (Show)
instance Exception TypeError

-- | Raise a type error
typeError :: Text -> M a
typeError = liftIO . throw . TypeError

-- | General strategy: we first build up a `Exp' GonnaBeATy`, where each
-- 'GonnaBeATy' action converts 'Ty's to 'Poly.Ty's (using 'resolveTy').
--
-- Then at the end we use 'sequence' to run all the 'GonnaBeATy's and get an
-- `Exp' Poly.Ty`.
--
-- We need to do that conversion at the end bc during elaboration the types
-- still have holes in them.
type GonnaBeATy = StateT Int IO Poly.Ty
--                ^^^^^^^^^^ for generating fresh type ids

type Value = Poly.Value' GonnaBeATy

-- | The elaboration monad.
--
--             read-write state for fresh ids
--                                        vvv
type M = RWST () (Endo (Poly.Exp' GonnaBeATy)) Int IO
--               ^^^^^^^^^^^^^^^^^^^^^^^^
--               write-only state for building up 'let's in the IR

runM :: M (a, Poly.Exp' GonnaBeATy) -> IO (a, Poly.Exp)
runM ma = do
  ((a, e), s, lets) <- runRWST ma () 0
  (a,) <$> evalStateT (sequence $ appEndo lets e) s

freshHole :: Lvl -> M (IORef Hole)
freshHole l = liftIO $ newIORef (Empty l)

freshId :: M Poly.Id
freshId = state \i -> (Poly.Id i, i + 1)

freshTId :: M Poly.TId
freshTId = state \i -> (Poly.TId i, i + 1)


-- | Convert a source-code 'Src.Ty' to a typechecker 'Ty', at a given level
srcTyToTy :: Ctx -> Src.Ty -> M Ty
srcTyToTy ctx = go Map.empty lvl
  where
    lvl = ctxLvl ctx
    go !_   !_ Src.THole = THole <$> freshHole lvl
    go !env !_ (Src.TVar name) =
      maybe (typeError $ "type variable " <> name <> " not in scope") pure
        $ Map.lookup name env
    go !_   !_ Src.TUnit = pure TUnit
    go !_   !_ Src.TInt = pure TInt
    go !env !l (Src.TPair a b) = TPair <$> go env l a <*> go env l b
    go !env !l (Src.TFun a b) = TFun <$> go env l a <*> go env l b
    go !env !l (Src.TForall name ty) =
      TForall name <$> go (Map.insert name (TVar l) env) (l + 1) ty


-- | Pretty-print a type.
displayTyCtx :: Ctx -> Ty -> M String
displayTyCtx ctx = displayTy (ctxLvl ctx) (typeNames ctx)

-- | Pretty-print a type.
displayTy :: Lvl -> IntMap Name -> Ty -> M String
displayTy = go False
  where
    parens p s = if p then "(" ++ s ++ ")" else s
    go _ !_ !tyNames (TVar v) =
      pure $ T.unpack (tyNames IMap.! v) ++ showSubscript v
    go p lvl tyNames (TFun a b) = parens p <$> do
      x <- go True lvl tyNames a
      y <- go False lvl tyNames b
      pure $ x ++ " -> " ++ y
    go p lvl tyNames (TForall n ty) = parens p <$> do
      x <- go False (lvl+1) (IMap.insert lvl n tyNames) ty
      pure $ "forall " ++ T.unpack n ++ showSubscript lvl ++ ". " ++ x
    go p lvl tyNames (THole ref) = liftIO (readIORef ref) >>= \case
      -- TODO: should empty holes have names?
      -- I think they should.
      Empty l -> pure $ "?[at level " ++ show l ++ "]"
      Filled ty -> go p lvl tyNames ty
      Generalized _ _ -> error "internal error"
    go _ lvl tyNames (TPair a b) = do
      x <- go False lvl tyNames a
      y <- go False lvl tyNames b
      pure $ "(" ++ x ++ ", " ++ y ++ ")"
    go _ _ _ TUnit = pure "unit"
    go _ _ _ TInt = pure "int"


-- | Convert a typechecker 'Ty' to an IR 'Poly.Ty'.
resolveTy :: Ctx -> Ty -> StateT Int IO Poly.Ty
resolveTy ctx@Ctx{..} ty = case ty of
  TVar lvl -> pure (typeTIds IMap.! lvl)
  TUnit -> pure Poly.TUnit
  TInt -> pure Poly.TInt
  TPair a b -> Poly.TPair <$> resolveTy ctx a <*> resolveTy ctx b
  TFun a b -> Poly.TFun <$> resolveTy ctx a <*> resolveTy ctx b
  TForall n a -> do
    tid <- state \i -> (Poly.TId i, i + 1)
    let ctx' = addTyToCtx n (Poly.TVar tid) ctx
    Poly.TForall n tid <$> resolveTy ctx' a
  THole ref -> do
    contents <- liftIO $ readIORef ref
    case contents of
      Empty _ -> pure Poly.TUnit -- error "ambiguous type" -- TODO better error
      Filled a -> resolveTy ctx a
      Generalized _ tid -> pure (Poly.TVar tid)



