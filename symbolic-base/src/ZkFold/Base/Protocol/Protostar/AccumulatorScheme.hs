{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant ^." #-}

module ZkFold.Base.Protocol.Protostar.AccumulatorScheme where

import           Control.Lens                                ((^.))
import           Data.List                                   (transpose)
import qualified Data.Vector                                 as DV
import           GHC.IsList                                  (IsList (..))
import           Prelude                                     (concatMap, ($), (.), (<$>))
import qualified Prelude                                     as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Algebra.Polynomials.Univariate  as PU
import           ZkFold.Base.Protocol.Protostar.Accumulator
import           ZkFold.Base.Protocol.Protostar.AlgebraicMap (AlgebraicMap (..))
import           ZkFold.Base.Protocol.Protostar.Commit       (HomomorphicCommit (..))
import           ZkFold.Base.Protocol.Protostar.CommitOpen   (CommitOpen (..))
import           ZkFold.Base.Protocol.Protostar.FiatShamir   (FiatShamir (..))
import           ZkFold.Base.Protocol.Protostar.NARK         (InstanceProofPair (..), NARKProof (..))
import           ZkFold.Base.Protocol.Protostar.Oracle       (RandomOracle (..))

-- | Accumulator scheme for V_NARK as described in Chapter 3.4 of the Protostar paper
--
-- TODO: define the initial accumulator
--
class AccumulatorScheme pi f c m a where
  prover   :: a
           -> Accumulator pi f c m        -- accumulator
           -> InstanceProofPair pi c m    -- instance-proof pair (pi, π)
           -> (Accumulator pi f c m, [c]) -- updated accumulator and accumulation proof

  verifier :: pi                          -- Public input
           -> [c]                         -- NARK proof π.x
           -> AccumulatorInstance pi f c  -- accumulator instance acc.x
           -> AccumulatorInstance pi f c  -- updated accumulator instance acc'.x
           -> [c]                         -- accumulation proof E_j
           -> (f, pi, [f], [c], c)        -- returns zeros if the accumulation proof is correct

  decider  :: a
           -> Accumulator pi f c m        -- final accumulator
           -> ([c], c)                    -- returns zeros if the final accumulator is valid

instance
    ( Scale f c
    , RandomOracle pi f         -- Random oracle for compressing public input
    , RandomOracle c f          -- Random oracle ρ_NARK
    , HomomorphicCommit [f] c
    , HomomorphicCommit m c
    , AlgebraicMap f pi m a
    , AlgebraicMap (PU.PolyVec f (Degree a + 1)) [PU.PolyVec f (Degree a + 1)] [PU.PolyVec f (Degree a + 1)] a
    , KnownNat (Degree a + 1)
    ) => AccumulatorScheme pi f c m (FiatShamir f (CommitOpen m c a)) where
  prover (FiatShamir (CommitOpen sps)) acc (InstanceProofPair pubi (NARKProof pi_x pi_w)) =
        (Accumulator (AccumulatorInstance pi'' ci'' ri'' eCapital' mu') m_i'', pf)
      where
          -- Fig. 3, step 1
          r_i :: [f]
          r_i = P.tail $ P.scanl (P.curry oracle) (oracle pubi) pi_x

          -- Fig. 3, step 2

          -- X + mu as a univariate polynomial
          polyMu :: PU.PolyVec f (Degree a + 1)
          polyMu = PU.polyVecLinear one (acc^.x^.mu)

          -- X * pi + pi' as a list of univariate polynomials
          polyPi :: [PU.PolyVec f (Degree a + 1)]
          polyPi = P.zipWith (PU.polyVecLinear @f) (toList pubi) (toList (acc^.x^.pi))

          -- X * mi + mi'
          polyW :: [PU.PolyVec f (Degree a + 1)]
          polyW = P.zipWith (PU.polyVecLinear @f) (concatMap toList pi_w) (concatMap toList (acc^.w))

          -- X * ri + ri'
          polyR :: [PU.PolyVec f (Degree a + 1)]
          polyR = P.zipWith (P.flip PU.polyVecLinear) (acc^.x^.r) r_i

          -- The @l x d+1@ matrix of coefficients as a vector of @l@ univariate degree-@d@ polynomials
          --
          e_uni :: [PU.PolyVec f (Degree a + 1)]
          e_uni = algebraicMap sps polyPi [polyW] polyR polyMu

          -- e_all are coefficients of degree-j homogenous polynomials where j is from the range [0, d]
          e_all = transpose $ DV.toList . PU.fromPolyVec <$> e_uni

          -- e_j are coefficients of degree-j homogenous polynomials where j is from the range [1, d - 1]
          e_j :: [[f]]
          e_j = P.tail . P.init $ e_all

          -- Fig. 3, step 3
          pf = hcommit <$> e_j

          -- Fig. 3, step 4
          alpha :: f
          alpha = oracle (acc^.x, pubi, pi_x, pf)

          -- Fig. 3, steps 5, 6
          mu'   = alpha + acc^.x^.mu
          pi''  = scale alpha pubi + acc^.x^.pi
          ri''  = scale alpha r_i  + acc^.x^.r
          ci''  = scale alpha pi_x + acc^.x^.c
          m_i'' = scale alpha pi_w + acc^.w

          -- Fig. 3, step 7
          eCapital' = acc^.x^.e + sum (P.zipWith (\e' p -> scale (alpha ^ p) e') pf [1::Natural ..])


  verifier pubi c_i acc acc' pf = (muDiff, piDiff, riDiff, ciDiff, eDiff)
      where
          -- Fig. 4, step 1
          r_i :: [f]
          r_i = P.tail $ P.scanl (P.curry oracle) (oracle pubi) c_i

          -- Fig. 4, step 2
          alpha :: f
          alpha = oracle (acc, pubi, c_i, pf)

          -- Fig. 4, step 3
          mu'  = alpha + acc^.mu
          pi'' = scale alpha pubi + acc^.pi
          ri'' = scale alpha r_i  + acc^.r
          ci'' = scale alpha c_i  + acc^.c

          -- Fig 4, step 4
          muDiff = acc'^.mu - mu'
          piDiff = acc'^.pi - pi''
          riDiff = acc'^.r  - ri''
          ciDiff = acc'^.c  - ci''

          -- Fig 4, step 5
          eDiff = acc'^.e - (acc^.e + sum (P.zipWith scale ((alpha ^) <$> [1 :: Natural ..]) pf))

  decider (FiatShamir (CommitOpen sps)) acc = (commitsDiff, eDiff)
      where
          -- Fig. 5, step 1
          commitsDiff = P.zipWith (\cm m_acc -> cm - hcommit m_acc) (acc^.x^.c) (acc^.w)

          -- Fig. 5, step 2
          err :: [f]
          err = algebraicMap sps (acc^.x^.pi) (acc^.w) (acc^.x^.r) (acc^.x^.mu)


          -- Fig. 5, step 3
          eDiff = (acc^.x^.e) - hcommit err
