{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Bool (
    Bool (Bool),
    Boolean (..),
    bool,
    ifThenElse,
    (?),
    and,
    or,
    all,
    any,
    Eq (..),
    (/=)
) where

import           Data.Functor.Rep                      (Representable)
import           GHC.Generics
import qualified Prelude                               as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.VectorSpace
import           ZkFold.Symbolic.Data.Container

-- TODO (Issue #18): hide this constructor
newtype Bool a = Bool a
  deriving stock
    ( Haskell.Functor
    , Haskell.Foldable
    , Haskell.Traversable
    )
deriving via Par1 instance VectorSpace a Bool
instance (Haskell.Eq a, MultiplicativeMonoid a) => Haskell.Show (Bool a) where
    show (Bool a) = if a Haskell.== one then "true" else "false"

class Boolean a b where
  true :: b a
  false :: b a
  not :: b a -> b a
  infixr 3 &&
  (&&) :: b a -> b a -> b a
  infixr 2 ||
  (||) :: b a -> b a -> b a
  xor :: b a -> b a -> b a

instance Ring a => Boolean a Bool where
  true = Bool one
  false = Bool zero
  not (Bool b) = Bool (one - b)
  Bool b1 && Bool b2 = Bool (b1 * b2)
  Bool b1 || Bool b2 = Bool (b1 + b2 - b1 * b2)
  xor (Bool b1) (Bool b2) = Bool (b1 + b2 - (b1 * b2 + b1 * b2))

bool :: (Ring a, VectorSpace a u) => u a -> u a -> Bool a -> u a
bool f t (Bool b) = scaleV b (t `subtractV` f) `addV` f

ifThenElse, (?)
  :: (Ring a, VectorSpace a u) => Bool a -> u a -> u a -> u a
ifThenElse b t f = bool f t b
(?) = ifThenElse

and :: (Haskell.Foldable f, Ring a) => (f :.: Bool) a -> Bool a
and = all Haskell.id

or :: (Haskell.Foldable f, Ring a) => (f :.: Bool) a -> Bool a
or = any Haskell.id

all :: (Haskell.Foldable f, Ring a) => (u a -> Bool a) -> (f :.: u) a -> Bool a
all condition (Comp1 xs) = Haskell.foldl (\b x -> b && condition x) true xs

any :: (Haskell.Foldable f, Ring a) => (u a -> Bool a) -> (f :.: u) a -> Bool a
any condition (Comp1 xs) = Haskell.foldl (\b x -> b || condition x) false xs

class Eq a u where
    infix 4 ==
    (==) :: u a -> u a -> Bool a
    default (==)
      :: (DiscreteField a, Haskell.Foldable u, VectorSpace a u)
      => u a -> u a -> Bool a
    u == v = Bool (Haskell.foldl (*) one (zipWithV equal u v))
instance DiscreteField a => Eq a Bool
instance DiscreteField a => Eq a Par1
instance (Ring a, Eq a u, Eq a v) => Eq a (u :*: v) where
  (u1 :*: v1) == (u2 :*: v2) = u1 == u2 && v1 == v2
instance (Representable f, Haskell.Foldable f, Ring a, Eq a u) => Eq a (f :.: u) where
  fu == fv = and (zipWith (==) fu fv)

infix 4 /=
(/=) :: (Ring a, Eq a u) => u a -> u a -> Bool a
u /= b = not (u == b)
