{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -freduction-depth=0 #-} -- Avoid reduction overflow error caused by NumberOfRegisters
{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Symbolic.Data.Ed25519  where

import           Control.Applicative                       ((<*>))
import           Data.Functor                              ((<$>))
import           Prelude                                   (type (~), ($))
import qualified Prelude                                   as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.EllipticCurve.Ed25519
import           ZkFold.Base.Control.HApplicative          (hliftA2)
import qualified ZkFold.Base.Data.Vector                   as V
import qualified ZkFold.Symbolic.Class                     as S
import           ZkFold.Symbolic.Class                     (Symbolic)
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Conditional
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.UInt
import           Control.DeepSeq (NFData)

instance
    ( Symbolic c
    , KnownRegisterSize rs
    , S.BaseField c ~ a
    , r ~ NumberOfRegisters a 256 rs
    , KnownNat r
    ) => SymbolicData c (Point (Ed25519 c rs)) where

    type Support c (Point (Ed25519 c rs)) = Support c (UInt 256 rs c)
    type TypeSize c (Point (Ed25519 c rs)) = TypeSize c (UInt 256 rs c) + TypeSize c (UInt 256 rs c)

    -- (0, 0) is never on a Twisted Edwards curve for any curve parameters.
    -- We can encode the point at infinity as (0, 0), therefore.
    pieces Inf         = hliftA2 V.append <$> pieces (zero :: UInt 256 rs c) <*> pieces (zero :: UInt 256 rs c)
    pieces (Point x y) = hliftA2 V.append <$> pieces x <*> pieces y

    restore f = bool @(Bool c) @(Point (Ed25519 c rs)) (Point x y) Inf ((x == zero) && (y == zero))
        where
            (x, y) = restore f

instance (Symbolic c, Eq (Bool c) (BaseField (Ed25519 c r))) => Eq (Bool c) (Point (Ed25519 c r)) where
    Inf == Inf                     = true
    Inf == _                       = false
    _ == Inf                       = false
    (Point x1 y1) == (Point x2 y2) = x1 == x2 && y1 == y2

    Inf /= Inf                     = false
    Inf /= _                       = true
    _ /= Inf                       = true
    (Point x1 y1) /= (Point x2 y2) = x1 /= x2 || y1 /= y2

-- | Ed25519 with @UInt 256 ArithmeticCircuit a@ as computational backend
--
instance
    ( Symbolic c
    , KnownRegisterSize rs 
    , KnownNat (NumberOfRegisters (S.BaseField c) 256 rs)
    , KnownNat (NumberOfRegisters (S.BaseField c) 512 rs)
    , NFData (c (V.Vector (NumberOfRegisters (S.BaseField c) 512 rs)))
    ) => EllipticCurve (Ed25519 c rs)  where

    type BaseField (Ed25519 c rs) = UInt 256 rs c
    type ScalarField (Ed25519 c rs) = UInt 256 rs c

    inf = Inf

    gen = Point
            (fromConstant (15112221349535400772501151409588531511454012693041857206046113283949847762202 :: Natural))
            (fromConstant (46316835694926478169428394003475163141307993866256225615783033603165251855960 :: Natural))

    add x y = bool @(Bool c) @(Point (Ed25519 c rs)) (acAdd25519 x y) (acDouble25519 x) (x == y)

    -- pointMul uses natScale which converts the scale to Natural.
    -- We can't convert arithmetic circuits to Natural, so we can't use pointMul either.
    --
    mul sc x = sum $ P.zipWith (\b p -> bool @(Bool c) zero p (isSet bits b)) [255, 254 .. 0] (P.iterate (\e -> e + e) x)
        where
            bits :: ByteString 256 c
            bits = from sc

acAdd25519
    :: forall c rs
    .  Symbolic c
    => KnownRegisterSize rs
    => KnownNat (NumberOfRegisters (S.BaseField c) 512 rs)
    => NFData (c (V.Vector (NumberOfRegisters (S.BaseField c) 512 rs)))
    => Point (Ed25519 c rs)
    -> Point (Ed25519 c rs)
    -> Point (Ed25519 c rs)
acAdd25519 Inf q = q
acAdd25519 p Inf = p
acAdd25519 (Point x1 y1) (Point x2 y2) = Point (shrink x3) (shrink y3)
    where
        -- We will perform multiplications of UInts of up to n bits, therefore we need 2n bits to store the result.
        --
        x1e, y1e, x2e, y2e :: UInt 512 rs c
        x1e = extend x1
        y1e = extend y1
        x2e = extend x2
        y2e = extend y2

        m :: UInt 512 rs c
        m = fromConstant $ value @Ed25519_Base

        plusM :: UInt 512 rs c -> UInt 512 rs c -> UInt 512 rs c
        plusM x y = (x + y) `mod` m

        mulM :: UInt 512 rs c -> UInt 512 rs c -> UInt 512 rs c
        mulM x y = (x * y) `mod` m

        d :: UInt 512 rs c
        d = fromConstant $ fromZp @Ed25519_Base $ (toZp (-121665) // toZp 121666)

        x3n :: UInt 512 rs c
        x3n = (x1e `mulM` y2e) `plusM` (y1e `mulM` x2e)

        x3d :: UInt 512 rs c
        x3d = one `plusM` (d `mulM` x1e `mulM` x2e `mulM` y1e `mulM` y2e)

        -- Calculate the modular inverse using Extended Euclidean algorithm
        x3di :: UInt 512 rs c
        (x3di, _, _) = eea x3d m

        x3 :: UInt 512 rs c
        x3 = x3n `mulM` x3di

        y3n :: UInt 512 rs c
        y3n = (y1e `mulM` y2e) `plusM` (x1e `mulM` x2e)

        y3d :: UInt 512 rs c
        y3d = one `plusM` ((m - d) `mulM` x1e `mulM` x2e `mulM` y1e `mulM` y2e)

        -- Calculate the modular inverse using Extended Euclidean algorithm
        y3di :: UInt 512 rs c
        (y3di, _, _) = eea y3d m

        y3 :: UInt 512 rs c
        y3 = y3n `mulM` y3di

acDouble25519
    :: forall c rs
    .  Symbolic c
    => KnownRegisterSize rs
    => KnownNat (NumberOfRegisters (S.BaseField c) 512 rs)
    => NFData (c (V.Vector (NumberOfRegisters (S.BaseField c) 512 rs)))
    => Point (Ed25519 c rs)
    -> Point (Ed25519 c rs)
acDouble25519 Inf = Inf
acDouble25519 (Point x1 y1) = Point (shrink x3) (shrink y3)
    where
        -- We will perform multiplications of UInts of up to n bits, therefore we need 2n bits to store the result.
        --
        xe, ye :: UInt 512 rs c
        xe = extend x1
        ye = extend y1

        m :: UInt 512 rs c
        m = fromConstant $ value @Ed25519_Base

        plusM :: UInt 512 rs c -> UInt 512 rs c -> UInt 512 rs c
        plusM x y = (x + y) `mod` m

        mulM :: UInt 512 rs c -> UInt 512 rs c -> UInt 512 rs c
        mulM x y = (x * y) `mod` m

        x3n :: UInt 512 rs c
        x3n = (xe `mulM` ye) `plusM` (xe `mulM` ye)

        x3d :: UInt 512 rs c
        x3d = ((m - one) `mulM` xe `mulM` xe) `plusM` (ye `mulM` ye)

        -- Calculate the modular inverse using Extended Euclidean algorithm
        x3di :: UInt 512 rs c
        (x3di, _, _) = eea x3d m

        x3 :: UInt 512 rs c
        x3 = x3n `mulM` x3di

        y3n :: UInt 512 rs c
        y3n = (ye `mulM` ye) `plusM` (xe `mulM` xe)

        y3d :: UInt 512 rs c
        y3d = (one + one) `plusM` (xe `mulM` xe) `plusM` ((m - one) `mulM` ye `mulM` ye)

        -- Calculate the modular inverse using Extended Euclidean algorithm
        y3di :: UInt 512 rs c
        (y3di, _, _) = eea y3d m

        y3 :: UInt 512 rs c
        y3 = y3n `mulM` y3di
