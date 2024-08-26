module ZkFold.Symbolic.Cardano.Types.Basic
    ( F
    , FieldElement
    , FieldElementBits
    , Bool
    , Symbolic.ByteString
    , Symbolic.UInt
    , Symbolic.UTCTime
    ) where

import           Prelude                                     hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Base.Data.Vector                     (Vector)
import qualified ZkFold.Symbolic.Data.Bool                   as Symbolic
import qualified ZkFold.Symbolic.Data.ByteString             as Symbolic
import qualified ZkFold.Symbolic.Data.FieldElement           as Symbolic
import qualified ZkFold.Symbolic.Data.UInt                   as Symbolic
import qualified ZkFold.Symbolic.Data.UTCTime                as Symbolic

type F = Zp BLS12_381_Scalar

type FieldElement context     = Symbolic.FieldElement context
type FieldElementBits context = context (Vector 256)

type Bool context = Symbolic.Bool context
