{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE TypeOperators       #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant ^." #-}

module ZkFold.Base.Protocol.IVC.RecursiveFunction where

import           GHC.Generics                               (Generic)
import           Prelude                                    (id)

import           ZkFold.Base.Algebra.Basic.Number           (type (-))
import           ZkFold.Base.Data.Vector                    (Vector)
import           ZkFold.Base.Protocol.IVC.Accumulator       hiding (pi)
import           ZkFold.Base.Protocol.IVC.Oracle
import           ZkFold.Base.Protocol.IVC.Predicate         (StepFunction)

-- | Public input for the recursive function
data RecursiveI k i c f = RecursiveI (i f) (AccumulatorInstance k i c f)
    deriving (GHC.Generics.Generic)

deriving instance (HashAlgorithm algo f, RandomOracle algo (i f) f, RandomOracle algo (c f) f) => RandomOracle algo (RecursiveI k i c f) f

toRecursiveI :: i f -> i f
toRecursiveI = id

-- | Payload for the recursive function
data RecursiveP d k i p c f = RecursiveP (i f) (p f) f (AccumulatorInstance k i c f) (Vector k (c f)) (Vector (d-1) (c f))
    deriving (GHC.Generics.Generic)

toRecursiveP :: p f -> p f
toRecursiveP = id

-- TODO: Implement the recursive function.
recursiveFunction :: StepFunction a i p -> StepFunction a i p
recursiveFunction f = f
