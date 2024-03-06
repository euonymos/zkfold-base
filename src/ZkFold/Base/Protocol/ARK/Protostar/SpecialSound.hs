{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Base.Protocol.ARK.Protostar.SpecialSound where

import           Prelude                                      hiding (length)

import           ZkFold.Base.Algebra.Polynomials.Multivariate (SomePolynomial)
import           ZkFold.Base.Data.Vector                      (Vector)
import           ZkFold.Symbolic.Compiler.Arithmetizable      (Arithmetic)

type SpecialSoundTranscript t a = [(ProverMessage t a, VerifierMessage t a)]

class Arithmetic f => SpecialSoundProtocol f a where
      type Witness f a
      type Input f a
      type ProverMessage t a
      type VerifierMessage t a

      type Dimension a
      -- ^ l in the paper
      type Degree a
      -- ^ d in the paper

      rounds    :: a -> Integer
      -- ^ k in the paper

      prover :: a -> Witness f a -> Input f a -> SpecialSoundTranscript f a -> ProverMessage f a

      verifier' :: a -> Input f a -> SpecialSoundTranscript Integer a
            -> Vector (Dimension a) (SomePolynomial f)

      verifier :: a -> Input f a -> SpecialSoundTranscript f a -> Bool