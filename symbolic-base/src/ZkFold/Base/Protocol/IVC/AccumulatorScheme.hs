{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant ^." #-}

module ZkFold.Base.Protocol.IVC.AccumulatorScheme where

import           Control.Lens                                ((^.))
import           Data.Constraint                             (withDict)
import           Data.Constraint.Nat                         (plusMinusInverse1)
import           Data.Functor.Rep                            (Representable (..))
import           Data.Kind                                   (Type)
import           Data.Zip                                    (Zip (..))
import           GHC.IsList                                  (IsList (..))
import           Prelude                                     (type (~), fmap, ($), (.), (<$>))
import qualified Prelude                                     as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Algebra.Polynomials.Univariate  as PU
import           ZkFold.Base.Data.Vector                     (Vector, init, mapWithIx, tail, unsafeToVector)
import           ZkFold.Base.Protocol.IVC.Accumulator
import           ZkFold.Base.Protocol.IVC.AlgebraicMap       (algebraicMap)
import           ZkFold.Base.Protocol.IVC.Commit             (HomomorphicCommit (..))
import           ZkFold.Base.Protocol.IVC.FiatShamir         (transcript)
import           ZkFold.Base.Protocol.IVC.NARK               (NARKInstanceProof (..), NARKProof (..))
import           ZkFold.Base.Protocol.IVC.Oracle             (RandomOracle (..), HashAlgorithm)
import           ZkFold.Base.Protocol.IVC.Predicate          (Predicate)

-- | Accumulator scheme for V_NARK as described in Chapter 3.4 of the Protostar paper
data AccumulatorScheme d k i c m o f = AccumulatorScheme
  {
    prover   ::
               Accumulator k i c m f                      -- accumulator
            -> NARKInstanceProof k i c m f                -- instance-proof pair (pi, π)
            -> (Accumulator k i c m f, Vector (d-1) c)    -- updated accumulator and accumulation proof

  , verifier :: i f                                       -- Public input
            -> Vector k c                                 -- NARK proof π.x
            -> AccumulatorInstance k i c f                -- accumulator instance acc.x
            -> AccumulatorInstance k i c f                -- updated accumulator instance acc'.x
            -> Vector (d-1) c                             -- accumulation proof E_j
            -> (f, i f, Vector (k-1) f, Vector k c, c)    -- returns zeros if the accumulation proof is correct

  , decider  ::
               Accumulator k i c m f                      -- final accumulator
            -> (Vector k c, c)                            -- returns zeros if the final accumulator is valid
  }

accumulatorScheme :: forall algo d k a i (p :: Type -> Type) c m o f .
    ( KnownNat (d-1)
    , KnownNat (d+1)
    , KnownNat k
    , Representable i
    , Zip i
    , HashAlgorithm algo f
    , RandomOracle algo f f
    , RandomOracle algo (i f) f    -- Random oracle for compressing public input
    , RandomOracle algo c f        -- Random oracle ρ_NARK
    , RandomOracle algo (f, c) f
    , RandomOracle algo (Vector k c) f
    , RandomOracle algo (Vector (k-1) f) f
    , RandomOracle algo (Vector (d-1) c) f
    , HomomorphicCommit m c
    , m ~ [f]
    , Field f
    , Scale a f
    , Scale a (PU.PolyVec f (d+1))
    , Scale f c
    , Scale f (Vector k c)
    )
    => Predicate a i p
    -> AccumulatorScheme d k i c m o f
accumulatorScheme phi =
  let
      prover acc (NARKInstanceProof pubi (NARKProof pi_x pi_w)) =
        let
            r_0 :: f
            r_0 = oracle @algo pubi

            -- Fig. 3, step 1
            r_i :: Vector (k-1) f
            r_i = transcript @algo r_0 pi_x

            -- Fig. 3, step 2

            -- X + mu as a univariate polynomial
            polyMu :: PU.PolyVec f (d+1)
            polyMu = PU.polyVecLinear one (acc^.x^.mu)

            -- X * pi + pi' as a list of univariate polynomials
            polyPi :: i (PU.PolyVec f (d+1))
            polyPi = zipWith (PU.polyVecLinear @f) pubi (acc^.x^.pi)

            -- X * mi + mi'
            polyW :: Vector k [PU.PolyVec f (d+1)]
            polyW = zipWith (zipWith (PU.polyVecLinear @f)) pi_w (acc^.w)

            -- X * ri + ri'
            polyR :: Vector (k-1) (PU.PolyVec f (d+1))
            polyR = zipWith (P.flip PU.polyVecLinear) (acc^.x^.r) r_i

            -- The @l x d+1@ matrix of coefficients as a vector of @l@ univariate degree-@d@ polynomials
            --
            e_uni :: [Vector (d+1) f]
            e_uni = unsafeToVector . toList <$> algebraicMap @d phi polyPi polyW polyR polyMu

            -- e_all are coefficients of degree-j homogenous polynomials where j is from the range [0, d]
            e_all :: Vector (d+1) [f]
            e_all = tabulate (\i -> fmap (`index` i) e_uni)

            -- e_j are coefficients of degree-j homogenous polynomials where j is from the range [1, d - 1]
            e_j :: Vector (d-1) [f]
            e_j = withDict (plusMinusInverse1 @1 @d) $ tail $ init e_all

            -- Fig. 3, step 3
            pf = hcommit <$> e_j

            -- Fig. 3, step 4
            alpha :: f
            alpha = oracle @algo (acc^.x, pubi, pi_x, pf)

            -- Fig. 3, steps 5, 6
            mu'   = alpha + acc^.x^.mu
            pi''  = zipWith (+) (fmap (* alpha) pubi) (acc^.x^.pi)
            ri''  = scale alpha r_i  + acc^.x^.r
            ci''  = scale alpha pi_x + acc^.x^.c
            m_i'' = zipWith (+) (scale alpha pi_w) (acc^.w)

            -- Fig. 3, step 7
            eCapital' = acc^.x^.e + sum (mapWithIx (\i a -> scale (alpha ^ (i+1)) a) pf)
        in
            (Accumulator (AccumulatorInstance pi'' ci'' ri'' eCapital' mu') m_i'', pf)
        
      verifier pubi pi_x acc acc' pf =
        let
            r_0 :: f
            r_0 = oracle @algo pubi

            -- Fig. 4, step 1
            r_i :: Vector (k-1) f
            r_i = transcript @algo r_0 pi_x

            -- Fig. 4, step 2
            alpha :: f
            alpha = oracle @algo (acc, pubi, pi_x, pf)

            -- Fig. 4, step 3
            mu'  = alpha + acc^.mu
            pi'' = zipWith (+) (fmap (* alpha) pubi) (acc^.pi)
            ri'' = zipWith (+) (scale alpha r_i)     (acc^.r)
            ci'' = zipWith (+) (scale alpha pi_x)    (acc^.c)

            -- Fig 4, step 4
            muDiff = acc'^.mu - mu'
            piDiff = zipWith (-) (acc'^.pi) pi''
            riDiff = zipWith (-) (acc'^.r)  ri''
            ciDiff = acc'^.c  - ci''

            -- Fig 4, step 5
            eDiff = acc'^.e - (acc^.e + sum (mapWithIx (\i a -> scale (alpha ^ (i+1)) a) pf))
        in
            (muDiff, piDiff, riDiff, ciDiff, eDiff)

      decider acc =
        let
            -- Fig. 5, step 1
            commitsDiff = zipWith (\cm m_acc -> cm - hcommit m_acc) (acc^.x^.c) (acc^.w)

            -- Fig. 5, step 2
            err :: [f]
            err = algebraicMap @d phi (acc^.x^.pi) (acc^.w) (acc^.x^.r) (acc^.x^.mu)


            -- Fig. 5, step 3
            eDiff = (acc^.x^.e) - hcommit err
        in
            (commitsDiff, eDiff)
          
  in
      AccumulatorScheme prover verifier decider
