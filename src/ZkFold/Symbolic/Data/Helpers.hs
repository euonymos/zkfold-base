{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module ZkFold.Symbolic.Data.Helpers where

import           Data.Constraint
import           Data.Constraint.Nat
import           ZkFold.Base.Algebra.Basic.Number
import           Prelude
import Data.Constraint.Unsafe (unsafeAxiom)


-- type ExtensionBits inputLen = 8 * (128 - Mod inputLen 128)
-- type ExtendedInputByteString inputLen c = ByteString (8 * inputLen + ExtensionBits inputLen) c


with4n6 :: forall n {r}. KnownNat n => (KnownNat (4 * n + 6) => r) -> r
with4n6 f = withDict (timesNat @4 @n) (withDict (plusNat @(4 * n) @6) f)

with8n  :: forall inputLen {r}. KnownNat inputLen => (KnownNat (8 * inputLen) => r) -> r
with8n = withDict (timesNat @8 @inputLen)

withExtensionBits :: forall inputLen {r}. KnownNat inputLen => (KnownNat (8 * (128 - Mod inputLen 128)) => r) -> r
withExtensionBits = withDict (modBound @inputLen @128) $
                        withDict (modNat @inputLen @128) $
                            withDict (minusNat @128 @(Mod inputLen 128)) $
                                withDict (timesNat @8 @(128 - Mod inputLen 128))

withExtendedInputByteString :: forall inputLen {r}. KnownNat inputLen => (KnownNat (8 * inputLen + 8 * (128 - Mod inputLen 128)) => r) -> r
withExtendedInputByteString = withExtensionBits @inputLen $
                                    withDict (timesNat @8 @inputLen) $
                                        withDict (plusNat @(8 * inputLen) @( 8 * (128 - Mod inputLen 128)))

with8nLessExt :: forall inputLen {r}. KnownNat inputLen => (8 * inputLen <= 8 * inputLen +  8 * (128 - Mod inputLen 128) => r) -> r
with8nLessExt = withExtendedInputByteString @inputLen $
                    withDict (zeroLe @( 8 * (128 - Mod inputLen 128))) $
                        withDict (plusMonotone2 @(8 * inputLen) @0 @( 8 * (128 - Mod inputLen 128)))

---
black2bDivConstraint :: forall a b. (Gcd a 8 ~ 8) :- (Div (8 * a + 8 * (2 * 64 - Mod a (2 * b))) 64 * 64 ~ 8 * a + 8 * (2 * 64 - Mod a (2 * 64)) )
black2bDivConstraint = Sub unsafeAxiom

withBlack2bDivConstraint :: forall a b {r}. (Gcd a 8 ~ 8) => (Div (8 * a + 8 * (2 * 64 - Mod a (2 * b))) 64 * 64 ~ 8 * a + 8 * (2 * 64 - Mod a (2 * 64)) => r) -> r
withBlack2bDivConstraint =  withDict (black2bDivConstraint @a @b) 

---
unsafeDiv :: forall a b. Dict (Div a b * b ~ a)
unsafeDiv = unsafeAxiom

withUnsafeDiv :: forall a b {r}. ( (Div a b * b ~ a) => r) -> r
withUnsafeDiv = withDict (unsafeDiv @a @b)

---
divNN :: forall a. Dict (Div a a ~ a)
divNN = unsafeAxiom

withDivNN :: forall a {r}. ( (Div a a ~ a) => r) -> r
withDivNN = withDict (divNN @a)


---
gcdn8 :: forall a. Dict (Gcd a 8 ~ 8)
gcdn8 = unsafeAxiom

withGcdn8 :: forall a {r}. ( (Gcd a 8 ~ 8) => r) -> r
withGcdn8 = withDict (gcdn8 @a)


