{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.FieldElement where

import           Numeric.Natural                                     (Natural)
import           Prelude                                             hiding (Num (..), drop, length, product, splitAt,
                                                                      sum, take, (!!), (^))

import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Data.Vector                             as V
import           ZkFold.Base.Data.Vector                             (Vector (..))
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (Arithmetic, ArithmeticCircuit (..))
import qualified ZkFold.Symbolic.Compiler.Arithmetizable             as A

newtype FieldElement c a = FieldElement { fromFieldElement :: c 1 a }
    deriving (Eq, Show)

-- | A class for serializing data types into containers holding finite field elements.
-- Type `a` is the finite field.
-- Type `b` is the container type.
-- Type `x` represents the data type.
class Arithmetic a => FieldElementData a c x where

    type TypeSize a c x :: Natural

    -- | Returns the representation of `x` as a container of finite field elements.
    toFieldElements :: x -> c (TypeSize a c x) a

    -- | Restores `x` from its representation as a container of finite field elements.
    fromFieldElements :: c (TypeSize a c x) a -> x

-- | Returns the number of finite field elements needed to describe `x`.
typeSize :: forall a c x . KnownNat (TypeSize a c x) => Natural
typeSize = value @(TypeSize a c x)

instance Arithmetic a => FieldElementData a Vector () where
    type TypeSize a Vector () = 0

    toFieldElements () = V.empty

    fromFieldElements _ = ()

instance Arithmetic a => FieldElementData a Vector (FieldElement Vector a) where
    type TypeSize a Vector (FieldElement Vector a) = 1

    toFieldElements (FieldElement x) = V.singleton $ V.item x

    fromFieldElements = FieldElement . V.singleton . V.head

instance
    ( FieldElementData a Vector x
    , FieldElementData a Vector y
    , m ~ TypeSize a Vector x
    , KnownNat m
    ) => FieldElementData a Vector (x, y) where

    type TypeSize a Vector (x, y) = TypeSize a Vector x + TypeSize a Vector y

    toFieldElements (a, b) = toFieldElements a `V.append` toFieldElements b

    fromFieldElements v = (fromFieldElements v1, fromFieldElements v2)
        where
            (v1, v2) = V.splitAt @m v

instance
    ( FieldElementData a Vector x
    , FieldElementData a Vector y
    , FieldElementData a Vector z
    , m ~ TypeSize a Vector x
    , n ~ TypeSize a Vector y
    , KnownNat m
    , KnownNat n
    ) => FieldElementData a Vector (x, y, z) where

    type TypeSize a Vector (x, y, z) = TypeSize a Vector x + TypeSize a Vector y + TypeSize a Vector z

    toFieldElements (a, b, c) = toFieldElements a `V.append` toFieldElements b `V.append` toFieldElements c

    fromFieldElements v = (fromFieldElements v1, fromFieldElements v2, fromFieldElements v3)
        where
            (v1, v2, v3) = V.splitAt3 @m @n v

instance
    ( FieldElementData a Vector x
    , m ~ TypeSize a Vector x
    , KnownNat m
    ) => FieldElementData a Vector (Vector n x) where

    type TypeSize a Vector (Vector n x) = n * TypeSize a Vector x

    toFieldElements xs = V.concat $ toFieldElements <$> xs

    fromFieldElements v = fromFieldElements <$> V.chunks v

instance A.SymbolicData a x => FieldElementData a ArithmeticCircuit x where
    type TypeSize a ArithmeticCircuit x = A.TypeSize a x

    toFieldElements = A.pieces

    fromFieldElements ArithmeticCircuit {..} = A.restore acCircuit acOutput
