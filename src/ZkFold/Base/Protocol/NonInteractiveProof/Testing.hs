{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.NonInteractiveProof.Testing where

import           Prelude

import           ZkFold.Base.Protocol.NonInteractiveProof.Internal

class (NonInteractiveProof a, NonInteractiveProof b) => CompatibleNonInteractiveProofs a b where
    nipSetupTransform    :: SetupVerify a -> SetupVerify b
    nipInputTransform    :: Input a -> Input b
    nipProofTransform    :: Proof a -> Proof b

nipCompatibility :: forall a b . CompatibleNonInteractiveProofs a b
    => a -> Witness a -> Bool
nipCompatibility a w =
    let (i, p) = prove @a (setupProve a) w
        s'     = nipSetupTransform @a @b (setupVerify a)
        i'     = nipInputTransform @a @b i
        p'     = nipProofTransform @a @b p
    in verify @b s' i' p'

instance NonInteractiveProof a => CompatibleNonInteractiveProofs a a where
    nipSetupTransform    = id
    nipInputTransform    = id
    nipProofTransform    = id

data NonInteractiveProofTestData a = TestData a (Witness a)

instance (Show a, Show (Input a), Show (Witness a)) =>
    Show (NonInteractiveProofTestData a) where
    show (TestData a w) = "TestData: \n" ++ show a ++ "\n" ++ show w
