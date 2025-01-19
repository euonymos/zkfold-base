{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant ^." #-}

module ZkFold.Base.Protocol.IVC.AccumulatorScheme where

import           Control.Lens                               ((^.))
import           Data.Constraint                            (withDict)
import           Data.Constraint.Nat                        (plusMinusInverse1)
import           Data.Functor.Rep                           (Representable (..))
import           Data.Zip                                   (Zip (..))
import           GHC.IsList                                 (IsList (..))
import           Prelude                                    (Foldable, fmap, ($), (.), (<$>), Ord)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Algebra.Polynomials.Univariate as PU
import           ZkFold.Base.Data.Vector                    (Vector, init, mapWithIx, tail, unsafeToVector)
import           ZkFold.Base.Protocol.IVC.Accumulator
import           ZkFold.Base.Protocol.IVC.AlgebraicMap      (algebraicMap)
import           ZkFold.Base.Protocol.IVC.Commit            (HomomorphicCommit (..))
import           ZkFold.Base.Protocol.IVC.FiatShamir        (transcript)
import           ZkFold.Base.Protocol.IVC.NARK              (NARKInstanceProof (..), NARKProof (..))
import           ZkFold.Base.Protocol.IVC.Oracle            (HashAlgorithm, oracle)
import           ZkFold.Base.Protocol.IVC.Predicate         (Predicate)
import           ZkFold.Symbolic.Class                      (Symbolic(..))

-- | Accumulator scheme for V_NARK as described in Chapter 3.4 of the Protostar paper
data AccumulatorScheme d k i c ctx = AccumulatorScheme
  {
    prover   ::
               Accumulator k i c (WitnessField ctx)                                           -- accumulator
            -> NARKInstanceProof k i c ctx                                                    -- instance-proof pair (pi, π)
            -> (Accumulator k i c (WitnessField ctx), Vector (d-1) (c (WitnessField ctx)))    -- updated accumulator and accumulation proof

  , verifier :: forall f .
            ( Field f
            , AdditiveMonoid (c f)
            , Scale f (c f)
            )
            => i f                                          -- Public input
            -> Vector k (c f)                               -- NARK proof π.x
            -> AccumulatorInstance k i c f                  -- accumulator instance acc.x
            -> Vector (d-1) (c f)                           -- accumulation proof E_j
            -> AccumulatorInstance k i c f                  -- updated accumulator instance acc'.x

  , decider  :: forall f .
            ( Ring f
            , Scale (BaseField ctx) f
            , HomomorphicCommit [f] (c f)
            )
            => Accumulator k i c f                          -- final accumulator
            -> (Vector k (c f), c f)                        -- returns zeros if the final accumulator is valid

  -- | A version of the decider without the commitment check
  , decider'  :: forall f .
            ( Ring f
            , Scale (BaseField ctx) f
            , HomomorphicCommit [f] (c f)
            )
            => Accumulator k i c f                          -- final accumulator
            -> c f                                          -- returns zeros if the final accumulator is valid
  }

accumulatorScheme :: forall algo d k i p c ctx .
    ( KnownNat (d-1)
    , KnownNat (d+1)
    , Representable i
    , Zip i
    , Ord (Rep i)
    , HashAlgorithm algo
    , Foldable i
    , Foldable c
    , Symbolic ctx
    , HomomorphicCommit [WitnessField ctx] (c (WitnessField ctx))
    , Scale (BaseField ctx) (WitnessField ctx)
    , Scale (WitnessField ctx) (c (WitnessField ctx))
    )
    => Predicate i p ctx
    -> AccumulatorScheme d k i c ctx
accumulatorScheme phi =
  let
      prover acc (NARKInstanceProof pubi (NARKProof pi_x pi_w)) =
        let
            r_0 :: WitnessField ctx
            r_0 = oracle @algo pubi

            -- Fig. 3, step 1
            r_i :: Vector (k-1) (WitnessField ctx)
            r_i = transcript @algo r_0 pi_x

            -- Fig. 3, step 2

            -- X + mu as a univariate polynomial
            polyMu :: PU.PolyVec (WitnessField ctx) (d+1)
            polyMu = PU.polyVecLinear one (acc^.x^.mu)

            -- X * pi + pi' as a list of univariate polynomials
            polyPi :: i (PU.PolyVec (WitnessField ctx) (d+1))
            polyPi = zipWith PU.polyVecLinear pubi (acc^.x^.pi)

            -- X * mi + mi'
            polyW :: Vector k [PU.PolyVec (WitnessField ctx) (d+1)]
            polyW = zipWith (zipWith PU.polyVecLinear) pi_w (acc^.w)

            -- X * ri + ri'
            polyR :: Vector (k-1) (PU.PolyVec (WitnessField ctx) (d+1))
            polyR = zipWith PU.polyVecLinear r_i (acc^.x^.r)

            -- The @l x d+1@ matrix of coefficients as a vector of @l@ univariate degree-@d@ polynomials
            --
            e_uni :: [Vector (d+1) (WitnessField ctx)]
            e_uni = unsafeToVector . toList <$> algebraicMap @d phi polyPi polyW polyR polyMu

            -- e_all are coefficients of degree-j homogenous polynomials where j is from the range [0, d]
            e_all :: Vector (d+1) [WitnessField ctx]
            e_all = tabulate (\i -> fmap (`index` i) e_uni)

            -- e_j are coefficients of degree-j homogenous polynomials where j is from the range [1, d - 1]
            e_j :: Vector (d-1) [WitnessField ctx]
            e_j = withDict (plusMinusInverse1 @1 @d) $ tail $ init e_all

            -- Fig. 3, step 3
            pf :: Vector (d-1) (c (WitnessField ctx))
            pf = hcommit <$> e_j

            -- Fig. 3, step 4
            alpha :: WitnessField ctx
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

      verifier :: forall f .
        ( Field f
        , Scale f (c f)
        , AdditiveMonoid (c f)
        )
        => i f
        -> Vector k (c f)
        -> AccumulatorInstance k i c f
        -> Vector (d-1) (c f)
        -> AccumulatorInstance k i c f
      verifier pubi pi_x acc pf =
        let
            r_0 :: f
            r_0 = oracle @algo pubi

            -- Fig. 4, step 1
            r_i :: Vector (k-1) f
            r_i = transcript @algo r_0 pi_x

            -- Fig. 4, step 2
            alpha :: f
            alpha = oracle @algo (acc, pubi, pi_x, pf)

            -- Fig. 4, steps 3-4
            mu'  = alpha + acc^.mu
            pi'' = zipWith (+) (fmap (* alpha) pubi) (acc^.pi)
            ri'' = zipWith (+) (scale alpha r_i)     (acc^.r)
            ci'' = zipWith (+) (scale alpha pi_x)    (acc^.c)

            -- Fig 4, step 5
            e' = acc^.e + sum (mapWithIx (\i a -> scale (alpha ^ (i+1)) a) pf)
        in
            AccumulatorInstance { _pi = pi'', _c = ci'', _r = ri'', _e = e', _mu = mu' }

      decider :: forall f . (Ring f, Scale (BaseField ctx) f, HomomorphicCommit [f] (c f))
        => Accumulator k i c f
        -> (Vector k (c f), c f)
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

      decider' :: forall f . (Ring f, Scale (BaseField ctx) f, HomomorphicCommit [f] (c f))
        => Accumulator k i c f
        -> c f
      decider' acc =
        let
            -- Fig. 5, step 2
            err :: [f]
            err = algebraicMap @d phi (acc^.x^.pi) (acc^.w) (acc^.x^.r) (acc^.x^.mu)


            -- Fig. 5, step 3
            eDiff = (acc^.x^.e) - hcommit err
        in
            eDiff

  in
      AccumulatorScheme prover verifier decider decider'
