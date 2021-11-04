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
import Data.List
import Data.IORef
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IMap
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HMap


type Lvl = Int
type Idx = Int

data TyExp
  = TVar Idx
  | TFun TyExp TyExp
  | TForall Name TyExp
  | THole (IORef Hole)

data TyVal
  = VVar Lvl
  | VFun TyVal TyVal
  | VForall Name {-# UNPACK #-} Closure
  | VHole (IORef Hole)

data Closure = Closure [TyVal] TyExp

-- | A hole in a type.
data Hole
  = Filled TyVal
  | Empty Lvl
  | Generalized Lvl Poly.TId
  -- ^ The hole was filled during let-generalization.
  -- During let-generalization, holes get filled with 'Generalized Lvl TId'

-- An invariant about the scope of holes: in '∀ x. ... [H] ...', the scope of
-- the hole '[H]' never includes the type variable 'x'.


-- | Read-only state used during elaboration
data Ctx = Ctx
  { ctxLvl :: Lvl
  , typeTIds :: IntMap Poly.Ty
  , typeNames :: ~(IntMap Name)
  , typeEnv :: [TyVal]
  , boundVars :: HashMap Name (Value,TyVal)
  -- , boundTypes :: HashMap Name Lvl
  }

addTyToCtx :: Name -> Poly.Ty -> Ctx -> Ctx
addTyToCtx n ty Ctx{..} = Ctx
  { ctxLvl = ctxLvl + 1
  , typeTIds = IMap.insert ctxLvl ty typeTIds
  , typeNames = IMap.insert ctxLvl n typeNames
  , typeEnv = VVar ctxLvl : typeEnv
  , boundVars = boundVars }

-- | Like addTyToCtx, but without actually adding a type.
--
-- It's used in let-generalization, to identify holes local to the let binding.
moveDownLevelCtx :: Ctx -> Ctx
moveDownLevelCtx ctx =
  ctx { ctxLvl = ctxLvl ctx + 1, typeEnv = error "no type here" : typeEnv ctx }

addVarToCtx :: Name -> Value -> TyVal -> Ctx -> Ctx
addVarToCtx n val ty ctx =
  ctx { boundVars = HMap.insert n (val,ty) $ boundVars ctx }

-- TODO: nicer type errors
newtype TypeError = TypeError Text deriving (Show)
instance Exception TypeError

-- | Raise a type error
typeError :: Text -> M a
typeError = liftIO . throw . TypeError

-- | General strategy: we first build up a `Exp' GonnaBeATy`, where each
-- 'GonnaBeATy' action converts 'TyVal's to 'Poly.Ty's (using 'resolveTy').
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
--                  read-write state for fresh ids
--                                             vvv
type M = RWST () (Endo (Poly.Exp' GonnaBeATy)) Int IO
--               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
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


-- | Can't spell NbE without 'evalTy'
evalTy :: [TyVal] -> TyExp -> TyVal
evalTy env (TVar idx) = env !! idx
evalTy env (TFun a b) = VFun (evalTy env a) (evalTy env b)
evalTy env (TForall n ty) = VForall n (Closure env ty)
evalTy _ (THole h) = VHole h

-- | Apply a closure to an argument
infixr 0 $$
($$) :: Closure -> TyVal -> TyVal
Closure env body $$ arg = evalTy (arg : env) body


-- | Convert a source-code 'Src.Ty' to a typechecker 'TyVal'
srcTyToTy :: Ctx -> Src.Ty -> M TyVal
srcTyToTy ctx t = evalTy [] <$> go [] t
  where
    -- TODO: look up types in the type context
    lvl = ctxLvl ctx
    go env ty = case ty of
      Src.THole -> THole <$> freshHole lvl
      Src.TVar name
        | Just idx <- name `elemIndex` env -> pure (TVar idx)
        | otherwise -> typeError $ "type " <> name <> " not in scope"
      Src.TFun a b -> TFun <$> go env a <*> go env b
      Src.TForall name a -> TForall name <$> go (name:env) a
      _ -> error "TODO"


-- | Pretty-print a type.
displayTyCtx :: Ctx -> TyVal -> M String
displayTyCtx ctx = displayTy (ctxLvl ctx) (typeNames ctx)

-- | Pretty-print a type.
displayTy :: Lvl -> IntMap Name -> TyVal -> M String
displayTy = go False
  where
    parens p s = if p then "(" ++ s ++ ")" else s
    go _ !_ !tyNames (VVar l) =
      pure $ T.unpack (tyNames IMap.! l) ++ showSubscript l
    go p !lvl !tyNames (VFun a b) = do
      x <- go True lvl tyNames a
      y <- go False lvl tyNames b
      pure $ parens p $ x ++ " -> " ++ y
    go p !lvl !tyNames (VForall n a) = do
      x <- go False (lvl+1) (IMap.insert lvl n tyNames) (a $$ VVar lvl)
      pure $ parens p $ "forall " ++ T.unpack n ++ showSubscript lvl ++ ". " ++ x
    go p !lvl !tyNames (VHole ref) = liftIO (readIORef ref) >>= \case
      -- TODO: should empty holes have names?  I think they should.
      Empty l -> pure $ "?[at level " ++ show l ++ "]"
      Filled ty -> go p lvl tyNames ty
      Generalized _ _ -> error "internal error"


-- | Convert a typechecker 'TyVal' to an IR 'Poly.Ty'.
resolveTy :: Ctx -> TyVal -> StateT Int IO Poly.Ty
resolveTy ctx@Ctx{..} ty = case ty of
  VVar lvl -> pure (typeTIds IMap.! lvl)
  VFun a b -> Poly.TFun <$> resolveTy ctx a <*> resolveTy ctx b
  VForall n a -> do
    tid <- state \i -> (Poly.TId i, i + 1)
    let ctx' = addTyToCtx n (Poly.TVar tid) ctx
    Poly.TForall n tid <$> resolveTy ctx' (a $$ VVar ctxLvl)
  VHole ref -> liftIO (readIORef ref) >>= \case
    Empty _ -> pure Poly.TUnit -- error "ambiguous type" -- TODO better error
    Filled a -> resolveTy ctx a
    Generalized _ tid -> pure (Poly.TVar tid)



