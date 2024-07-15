{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.ARK.Plonk.Internal where

import           Data.Bifunctor                             (first)
import           Data.Bool                                  (bool)
import qualified Data.Map                                   as Map
import qualified Data.Vector                                as V
import           GHC.Generics                               (Generic)
import           GHC.IsList                                 (IsList (..))
import           Numeric.Natural                            (Natural)
import           Prelude                                    hiding (Num (..), drop, length, sum, take, (!!), (/), (^))
import           System.Random                              (RandomGen, mkStdGen, uniformR)
import           Test.QuickCheck                            (Arbitrary (..), Gen, shuffle)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class    (EllipticCurve (..), Point)
import           ZkFold.Base.Algebra.Polynomials.Univariate hiding (qr)
import           ZkFold.Prelude                             (take)

log2 :: (Integral a, Integral b) => a -> b
log2 = ceiling @Double . logBase 2 . fromIntegral

getParams :: forall a . (Eq a, FiniteField a) => Natural -> (a, a, a)
getParams n = findK' $ mkStdGen 0
    where
        omega = case rootOfUnity @a (log2 n) of
                  Just o -> o
                  _      -> error "impossible"
        hGroup = map (omega^) [0 .. n-!1]
        hGroup' k = map (k*) hGroup

        findK' :: RandomGen g => g -> (a, a, a)
        findK' g =
            let (k1, g') = first fromConstant $ uniformR (1, order @a -! 1) g
                (k2, g'') = first fromConstant $ uniformR (1, order @a -! 1) g'
            in bool (findK' g'') (omega, k1, k2) $
                all (`notElem` hGroup) (hGroup' k1)
                && all (`notElem` hGroup' k1) (hGroup' k2)

genSubset :: Natural -> Natural -> Gen [Natural]
genSubset maxLength maxValue = take maxLength <$> shuffle [1..maxValue]

type PlonkPermutationSize n = 3 * n

-- The maximum degree of the polynomials we need in the protocol is `4 * n + 5`.
type PlonkPolyExtendedLength n = 4 * n + 6

type PlonkPolyExtended n c = PolyVec (ScalarField c) (PlonkPolyExtendedLength n)

data PlonkSetupParamsProve c1 c2 = PlonkSetupParamsProve {
        omega' :: ScalarField c1,
        k1'    :: ScalarField c1,
        k2'    :: ScalarField c1,
        gs'    :: V.Vector (Point c1),
        h0'    :: Point c2,
        h1'    :: Point c2,
        iPub'  :: V.Vector Natural
    }
instance (Show (ScalarField c1), Show (BaseField c1), Show (BaseField c2),
        EllipticCurve c1, EllipticCurve c2) => Show (PlonkSetupParamsProve c1 c2) where
    show (PlonkSetupParamsProve omega' k1' k2' gs' h0' h1' iPub') =
        "Setup Parameters (Prove): "
        ++ show omega' ++ " "
        ++ show k1' ++ " "
        ++ show k2' ++ " "
        ++ show gs' ++ " "
        ++ show h0' ++ " "
        ++ show h1' ++ " "
        ++ show iPub'

data PlonkSetupParamsVerify c1 c2 = PlonkSetupParamsVerify {
        omega'' :: ScalarField c1,
        k1''    :: ScalarField c1,
        k2''    :: ScalarField c1,
        x2''    :: Point c2,
        pow''   :: Integer,
        n''     :: Integer
    }
instance (Show (ScalarField c1), Show (BaseField c1), Show (BaseField c2),
        EllipticCurve c1, EllipticCurve c2) => Show (PlonkSetupParamsVerify c1 c2) where
    show (PlonkSetupParamsVerify omega'' k1'' k2'' x2'' pow'' n'') =
        "Setup Parameters (Verify): "
        ++ show omega'' ++ " "
        ++ show k1''  ++ " "
        ++ show k2''  ++ " "
        ++ show x2''  ++ " "
        ++ show pow'' ++ " "
        ++ show n''

data PlonkPermutation n c = PlonkPermutation {
        s1 :: PolyVec (ScalarField c) n,
        s2 :: PolyVec (ScalarField c) n,
        s3 :: PolyVec (ScalarField c) n
    }
instance Show (ScalarField c) => Show (PlonkPermutation n c) where
    show (PlonkPermutation s1 s2 s3) = "Permutation: " ++ show s1 ++ " " ++ show s2 ++ " " ++ show s3

data PlonkCircuitPolynomials n c = PlonkCircuitPolynomials {
        ql     :: PlonkPolyExtended n c,
        qr     :: PlonkPolyExtended n c,
        qo     :: PlonkPolyExtended n c,
        qm     :: PlonkPolyExtended n c,
        qc     :: PlonkPolyExtended n c,
        sigma1 :: PlonkPolyExtended n c,
        sigma2 :: PlonkPolyExtended n c,
        sigma3 :: PlonkPolyExtended n c
    }
instance Show (ScalarField c) => Show (PlonkCircuitPolynomials n c) where
    show (PlonkCircuitPolynomials ql qr qo qm qc sigma1 sigma2 sigma3) =
        "Circuit Polynomials: "
        ++ show ql ++ " "
        ++ show qr ++ " "
        ++ show qo ++ " "
        ++ show qm ++ " "
        ++ show qc ++ " "
        ++ show sigma1 ++ " "
        ++ show sigma2 ++ " "
        ++ show sigma3

data PlonkCircuitCommitments c = PlonkCircuitCommitments {
        cmQl :: Point c,
        cmQr :: Point c,
        cmQo :: Point c,
        cmQm :: Point c,
        cmQc :: Point c,
        cmS1 :: Point c,
        cmS2 :: Point c,
        cmS3 :: Point c
    }
instance (Show (BaseField c), EllipticCurve c) => Show (PlonkCircuitCommitments c) where
    show (PlonkCircuitCommitments cmQl cmQr cmQo cmQm cmQc cmS1 cmS2 cmS3) =
        "Circuit Commitments: "
        ++ show cmQl ++ " "
        ++ show cmQr ++ " "
        ++ show cmQo ++ " "
        ++ show cmQm ++ " "
        ++ show cmQc ++ " "
        ++ show cmS1 ++ " "
        ++ show cmS2 ++ " "
        ++ show cmS3

newtype PlonkWitnessMap n c = PlonkWitnessMap
    (Map.Map Natural (ScalarField c) -> (PolyVec (ScalarField c) n, PolyVec (ScalarField c) n, PolyVec (ScalarField c) n))

newtype PlonkWitnessInput c = PlonkWitnessInput (Map.Map Natural (ScalarField c))
instance Show (ScalarField c) => Show (PlonkWitnessInput c) where
    show (PlonkWitnessInput m) = "Witness Input: " ++ show m

data PlonkProverSecret c = PlonkProverSecret {
        b1  :: ScalarField c,
        b2  :: ScalarField c,
        b3  :: ScalarField c,
        b4  :: ScalarField c,
        b5  :: ScalarField c,
        b6  :: ScalarField c,
        b7  :: ScalarField c,
        b8  :: ScalarField c,
        b9  :: ScalarField c,
        b10 :: ScalarField c,
        b11 :: ScalarField c
    } deriving Generic

instance Show (ScalarField c) => Show (PlonkProverSecret c) where
    show (PlonkProverSecret b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11) =
        "Prover Secret: "
        ++ show b1 ++ " "
        ++ show b2 ++ " "
        ++ show b3 ++ " "
        ++ show b4 ++ " "
        ++ show b5 ++ " "
        ++ show b6 ++ " "
        ++ show b7 ++ " "
        ++ show b8 ++ " "
        ++ show b9 ++ " "
        ++ show b10 ++ " "
        ++ show b11

instance Arbitrary (ScalarField c) => Arbitrary (PlonkProverSecret c) where
    arbitrary = PlonkProverSecret <$>
        arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
        <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary

newtype PlonkInput c = PlonkInput { unPlonkInput :: V.Vector (ScalarField c) }
instance Show (ScalarField c) => Show (PlonkInput c) where
    show (PlonkInput v) = "Input: " ++ show v

instance Arbitrary (ScalarField c) => Arbitrary (PlonkInput c) where
    arbitrary = do
        PlonkInput . fromList <$> arbitrary

data PlonkProof c = PlonkProof {
        cmA    :: Point c,
        cmB    :: Point c,
        cmC    :: Point c,
        cmZ    :: Point c,
        cmT1   :: Point c,
        cmT2   :: Point c,
        cmT3   :: Point c,
        proof1 :: Point c,
        proof2 :: Point c,
        a_xi   :: ScalarField c,
        b_xi   :: ScalarField c,
        c_xi   :: ScalarField c,
        s1_xi  :: ScalarField c,
        s2_xi  :: ScalarField c,
        z_xi   :: ScalarField c
    }
instance (Show (ScalarField c), Show (BaseField c), EllipticCurve c) => Show (PlonkProof c) where
    show (PlonkProof cmA cmB cmC cmZ cmT1 cmT2 cmT3 proof1 proof2 a_xi b_xi c_xi s1_xi s2_xi z_xi) =
        "Proof: "
        ++ show cmA ++ " "
        ++ show cmB ++ " "
        ++ show cmC ++ " "
        ++ show cmZ ++ " "
        ++ show cmT1 ++ " "
        ++ show cmT2 ++ " "
        ++ show cmT3 ++ " "
        ++ show proof1 ++ " "
        ++ show proof2 ++ " "
        ++ show a_xi ++ " "
        ++ show b_xi ++ " "
        ++ show c_xi ++ " "
        ++ show s1_xi ++ " "
        ++ show s2_xi ++ " "
        ++ show z_xi

