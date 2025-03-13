{-# LANGUAGE TypeOperators #-}

module Examples.BLS12_381 (
    exampleBLS12_381Scale
  ) where

import           Prelude                                      (type (~))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381  (BLS12_381_Base, BLS12_381_Scalar)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.EllipticCurve.BLS12_381 (BLS12_381_G1_Point)
import           ZkFold.Symbolic.Data.Combinators             (RegisterSize (Auto))
import           ZkFold.Symbolic.Data.FFA

exampleBLS12_381Scale
    :: ( Symbolic ctx
       , a ~ BaseField ctx
       , nativeBits ~ NumberOfBits a
       , uintBits ~ FFAUIntSize BLS12_381_Scalar (Order a)
       , KnownNat (nativeBits + uintBits)
       , KnownFFA BLS12_381_Base 'Auto ctx
       , KnownFFA BLS12_381_Scalar 'Auto ctx
       )
    => ScalarFieldOf (BLS12_381_G1_Point ctx)
    -> BLS12_381_G1_Point ctx
    -> BLS12_381_G1_Point ctx
exampleBLS12_381Scale = scale
