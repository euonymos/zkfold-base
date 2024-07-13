{-# LANGUAGE
AllowAmbiguousTypes
, DerivingStrategies
, DerivingVia
, QuantifiedConstraints
, RankNTypes
, TypeOperators
, UndecidableInstances
, UndecidableSuperClasses
#-}

module ZkFold.Symbolic.Base.Circuit
  ( Circuit (..), circuit, evalC
  , SysVar (..)
  , OutVar (..)
  , MonadCircuit (..)
  , IxMonadCircuit (..)
  , Blueprint (..)
  ) where

import Control.Applicative
import Control.Category
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Indexed
import Data.Either
import Data.Eq
import Data.Function (($))
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Maybe
import Data.Monoid
import Data.Ord
import Data.Semigroup
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Type.Equality
import qualified Prelude

import           ZkFold.Symbolic.Base.Num
import           ZkFold.Symbolic.Base.Polynomial
import           ZkFold.Symbolic.Base.Vector

data Circuit x i o = Circuit
  { systemC  :: Set (Poly (SysVar x i) Natural x)
    -- ^ The system of polynomial constraints,
    -- each polynomial constitutes a "multi-edge" of the circuit graph,
    -- whose "vertices" are variables.
    -- Polynomials constrain input variables and new variables.
    -- Constant variables are absorbed into the polynomial coefficients.
  , witnessC :: IntMap (i x -> x)
    -- ^ The witness generation map,
    -- witness functions for new variables.
    -- Input and constant variables don't need witness functions.
  , outputC  :: o (OutVar x i)
    -- ^ The output variables,
    -- they can be input, constant or new variables.
  }

circuit
  :: (Ord x, VectorSpace x i)
  => (forall t m. (IxMonadCircuit x t, Monad m) => t i i m (o (OutVar x i)))
  -> Circuit x i o
circuit m = case unPar1 (runBlueprint m mempty) of
  (o, c) -> c {outputC = o}

evalC :: (VectorSpace x i, Functor o) => Circuit x i o -> i x -> o x
evalC c i = fmap (witnessIndex i (witnessC c)) (outputC c)

data SysVar x i
  = InVar (Basis x i)
  | NewVar Int
deriving stock instance VectorSpace x i => Eq (SysVar x i)
deriving stock instance VectorSpace x i => Ord (SysVar x i)

data OutVar x i
  = SysVar (SysVar x i)
  | ConstVar x
deriving stock instance (Eq x, VectorSpace x i) => Eq (OutVar x i)
deriving stock instance (Ord x, VectorSpace x i) => Ord (OutVar x i)

witnessIndex
  :: VectorSpace x i
  => i x -> IntMap (i x -> x) -> OutVar x i -> x
witnessIndex inp witnessMap = \case
  SysVar (InVar basisIx) -> indexV inp basisIx
  SysVar (NewVar ix) -> fromMaybe zero (($ inp) <$> witnessMap IntMap.!? ix)
  ConstVar x -> x

instance (Ord x, VectorSpace x i, o ~ U1) => Monoid (Circuit x i o) where
  mempty = Circuit mempty mempty U1
instance (Ord x, VectorSpace x i, o ~ U1) => Semigroup (Circuit x i o) where
  c0 <> c1 = Circuit
    { systemC = systemC c0 <> systemC c1
    , witnessC = witnessC c0 <> witnessC c1
    , outputC = U1
    }

class Monad m
  => MonadCircuit x i m | m -> x, m -> i where
    runCircuit
      :: VectorSpace x i
      => Circuit x i o -> m (o (OutVar x i))
    input :: VectorSpace x i => m (i (OutVar x i))
    input = return (fmap (SysVar . InVar) (basisV @x))
    constraint
      :: VectorSpace x i
      => (forall a. Algebra x a => (SysVar x i -> a) -> a) -> m ()
    newConstrained
      :: VectorSpace x i
      => (forall a. Algebra x a => (Int -> a) -> Int -> a)
      -> ((Int -> x) -> x)
      -> m (OutVar x i)

class
  ( forall i m. Monad m => MonadCircuit x i (t i i m)
  , IxMonadTrans t
  ) => IxMonadCircuit x t | t -> x where
    apply
      :: (VectorSpace x i, VectorSpace x j, Monad m)
      => i x -> t (i :*: j) j m ()
    newInput
      :: (VectorSpace x i, VectorSpace x j, Monad m)
      => t j (i :*: j) m ()

newtype Blueprint x i j m r = Blueprint
  {runBlueprint :: Circuit x i U1 -> m (r, Circuit x j U1)}
  deriving Functor

instance (Field x, Ord x, Monad m)
  => Applicative (Blueprint x i i m) where
    pure x = Blueprint $ \c -> return (x,c)
    (<*>) = apIx

instance (Field x, Ord x, Monad m)
  => Monad (Blueprint x i i m) where
    return = pure
    (>>=) = Prelude.flip bindIx

instance (Field x, Ord x, Monad m)
  => MonadCircuit x i (Blueprint x i i m) where

    runCircuit c = Blueprint $ \c' -> return
      (outputC c, c {outputC = U1} <> c')

    constraint p = Blueprint $ \c -> return
      ((), c {systemC = Set.insert (p var) (systemC c)})

    newConstrained p w = Blueprint $ \c ->
      let
        (maxIndex, _) = IntMap.findMax (witnessC c)
        newIndex = maxIndex + 1
        newWitness i = w (fromMaybe zero . ((($ i) <$> witnessC c) IntMap.!?))
      in return
        ( SysVar (NewVar newIndex)
        , c { systemC = Set.insert (p (var . NewVar) newIndex) (systemC c)
            , witnessC = IntMap.insert newIndex newWitness (witnessC c)
            }
        )

instance (i ~ j, Ord x, Field x)
  => MonadTrans (Blueprint x i j) where
    lift m = Blueprint $ \c -> (, c) <$> m

instance (Field x, Ord x) => IxMonadTrans (Blueprint x) where
  joinIx (Blueprint f) = Blueprint $ \c -> do
    (Blueprint g, c') <- f c
    g c'

instance (Field x, Ord x)
  => IxMonadCircuit x (Blueprint x) where
    apply i = Blueprint $ \c -> return
      ( ()
      , c { systemC = Set.map (mapPoly sysF) (systemC c)
          , witnessC = fmap witF (witnessC c)
          , outputC = U1
          }
      ) where
          sysF = \case
            InVar (Left bi) -> Left (indexV i bi)
            InVar (Right bj) -> Right (InVar bj)
            NewVar n -> Right (NewVar n)
          witF f j = f (i :*: j)

    newInput = Blueprint $ \c -> return
      ( ()
      , c { systemC = Set.map (mapPoly sysF) (systemC c)
          , witnessC = fmap witF (witnessC c)
          , outputC = U1
          }
      )
      where
          sysF = \case
            InVar bj -> Right (InVar (Right bj))
            NewVar n -> Right (NewVar n)
          witF f (_ :*: j) = f j
