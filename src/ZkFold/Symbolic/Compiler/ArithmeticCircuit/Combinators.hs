{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators (
    boolCheckC,
    embed,
    embedV,
    embedAll,
    embedVar,
    expansion,
    splitExpansion,
    horner,
    desugarRange,
    isZeroC,
    invertC,
    joinCircuits,
    splitCircuit,
    foldCircuit,
    embedVarIndex,
    embedVarIndexV,
    getAllVars
) where

import           Control.Monad                                             (foldM, replicateM)
import           Data.Containers.ListUtils                                 (nubOrd)
import           Data.Foldable                                             (foldlM)
import           Data.List                                                 (sort)
import           Data.Map                                                  (elems)
import           Data.Traversable                                          (for)
import qualified Data.Zip                                                  as Z
import           GHC.IsList                                                (IsList (..))
import           Numeric.Natural                                           (Natural)
import           Prelude                                                   hiding (Bool, Eq (..), length, negate,
                                                                            splitAt, (!!), (*), (+), (-), (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.Polynomials.Multivariate              (variables)
import qualified ZkFold.Base.Data.Vector                                   as V
import           ZkFold.Base.Data.Vector                                   (Vector (..))
import           ZkFold.Prelude                                            (length, splitAt, (!!))
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal       (Arithmetic, ArithmeticCircuit (..),
                                                                            Circuit (acSystem), acInput, joinCircuits)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint
import           ZkFold.Symbolic.Data.Bool                                 (Bool)
import           ZkFold.Symbolic.Data.Conditional                          (Conditional (..))
import           ZkFold.Symbolic.Data.Eq                                   (Eq (..))

boolCheckC :: Arithmetic a => ArithmeticCircuit n a -> ArithmeticCircuit n a
-- ^ @boolCheckC r@ computes @r (r - 1)@ in one PLONK constraint.
boolCheckC r = circuitN $ do
    is <- runCircuit r
    for is $ \i -> newAssigned (\x -> let xi = x i in xi * (xi - one))

-- | TODO: This is ONLY needed in ZkFold.Symbolic.Cardano.Contracts.BatchTransfer
-- Using this function is against the new approach to ArithmeticCircuits
splitCircuit :: forall n a . ArithmeticCircuit n a -> Vector n (ArithmeticCircuit 1 a)
splitCircuit (ArithmeticCircuit c o) = ArithmeticCircuit c <$> V.chunks @n @1 o

foldCircuit :: forall n a. Arithmetic a => (forall i m . MonadBlueprint i a m => i -> i -> m i) -> ArithmeticCircuit n a -> ArithmeticCircuit 1 a
foldCircuit f c = circuit $ do
    outputs <- runCircuit c
    let (element, rest) = V.uncons outputs
    foldlM f element rest

-- | TODO: Think about circuits with multiple outputs
--
embed :: Arithmetic a => a -> ArithmeticCircuit 1 a
embed x = circuit $ newAssigned $ const (fromConstant x)

embedV :: Arithmetic a => Vector n a -> ArithmeticCircuit n a
embedV v = circuitN $ for v $ \x -> newAssigned $ const (fromConstant x)

embedVar :: forall a . a -> (forall i m . MonadBlueprint i a m => m i)
embedVar x = newAssigned $ const (fromConstant x)

embedAll :: forall a n . (Arithmetic a, KnownNat n) => a -> ArithmeticCircuit n a
embedAll x = circuitN $ Vector <$> replicateM (fromIntegral $ value @n) (newAssigned $ const (fromConstant x))

expansion :: MonadBlueprint i a m => Natural -> i -> m [i]
-- ^ @expansion n k@ computes a binary expansion of @k@ if it fits in @n@ bits.
expansion n k = do
    bits <- bitsOf n k
    k' <- horner bits
    constraint (\x -> x k - x k')
    return bits

splitExpansion :: MonadBlueprint i a m => Natural -> Natural -> i -> m (i, i)
-- ^ @splitExpansion n1 n2 k@ computes two values @(l, h)@ such that
-- @k = 2^n1 h + l@, @l@ fits in @n1@ bits and @h@ fits in n2 bits (if such
-- values exist).
splitExpansion n1 n2 k = do
    bits <- bitsOf (n1 + n2) k
    let (lo, hi) = splitAt n1 bits
    l <- horner lo
    h <- horner hi
    constraint (\x -> x k - x l - scale (2 ^ n1 :: Natural) (x h))
    return (l, h)

bitsOf :: MonadBlueprint i a m => Natural -> i -> m [i]
-- ^ @bitsOf n k@ creates @n@ bits and sets their witnesses equal to @n@ smaller
-- bits of @k@.
bitsOf n k = for [0 .. n -! 1] $ \j ->
    newConstrained (\x i -> let xi = x i in xi * (xi - one)) ((!! j) . repr . ($ k))
    where
        repr :: forall b . (BinaryExpansion b, Bits b ~ [b], Finite b) => b -> [b]
        repr = padBits (numberOfBits @b) . binaryExpansion

horner :: MonadBlueprint i a m => [i] -> m i
-- ^ @horner [b0,...,bn]@ computes the sum @b0 + 2 b1 + ... + 2^n bn@ using
-- Horner's scheme.
horner xs = case reverse xs of
    []       -> newAssigned (const zero)
    (b : bs) -> foldlM (\a i -> newAssigned (\x -> let xa = x a in x i + xa + xa)) b bs

desugarRange :: (Arithmetic a, MonadBlueprint i a m) => i -> a -> m ()
desugarRange i b
  | b == negate one = return ()
  | otherwise = do
    let bs = binaryExpansion b
    is <- expansion (length bs) i
    case dropWhile ((== one) . fst) (zip bs is) of
      [] -> return ()
      ((_, k0):ds) -> do
        z <- newAssigned (one - ($ k0))
        ge <- foldM (\j (c, k) -> newAssigned $ forceGE j c k) z ds
        constraint (($ ge) - one)
  where forceGE j c k
          | c == zero = ($ j) * (one - ($ k))
          | otherwise = one + ($ k) * (($ j) - one)

isZeroC :: Arithmetic a => ArithmeticCircuit n a -> ArithmeticCircuit n a
isZeroC r = circuitN $ fst <$> runInvert r

invertC :: Arithmetic a => ArithmeticCircuit n a -> ArithmeticCircuit n a
invertC r = circuitN $ snd <$> runInvert r

runInvert :: MonadBlueprint i a m => ArithmeticCircuit n a -> m (Vector n i, Vector n i)
runInvert r = do
    is <- runCircuit r
    js <- for is $ \i -> newConstrained (\x j -> x i * x j) (isZero . ($ i))
    ks <- for (Z.zip is js) $ \(i, j) -> newConstrained (\x k -> x i * x k + x j - one) (finv . ($ i))
    return (js, ks)
    where
      isZero :: forall a . (Ring a, Eq (Bool a) a, Conditional (Bool a) a) => a -> a
      isZero x = bool @(Bool a) zero one (x == zero)

embedVarIndex :: Arithmetic a => Natural -> ArithmeticCircuit 1 a
embedVarIndex n = ArithmeticCircuit { acCircuit = mempty { acInput = [ n ]}, acOutput = pure n}

embedVarIndexV :: (Arithmetic a, KnownNat n) => Natural -> ArithmeticCircuit n a
embedVarIndexV n = ArithmeticCircuit { acCircuit = mempty { acInput = [ n ]}, acOutput = pure n}

getAllVars :: MultiplicativeMonoid a => Circuit a -> [Natural]
getAllVars ac = nubOrd $ sort $ 0 : acInput ac ++ concatMap (toList . variables) (elems $ acSystem ac)
