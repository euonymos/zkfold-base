{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Symbolic.Cardano.Contracts.BatchTransfer where

import           Data.Maybe                                     (fromJust)
import           Data.Zip                                       (zip)
import           Numeric.Natural                                (Natural)
import           Prelude                                        hiding (Bool, Eq (..), all, length, splitAt, zip, (&&),
                                                                 (*), (+))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Vector                        (Vector, fromVector, toVector)
import           ZkFold.Symbolic.Algorithms.Hash.MiMC
import           ZkFold.Symbolic.Algorithms.Hash.MiMC.Constants (mimcConstants)
import           ZkFold.Symbolic.Cardano.Types
import           ZkFold.Symbolic.Data.Bool                      (BoolType (..), all)
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.UInt                      (StrictConv(..))
import           ZkFold.Symbolic.Types                          (Symbolic)

type Tokens = 10
type TxOut context = Output Tokens () context
type TxIn context  = Input Tokens () context
type Tx context = Transaction 6 0 11 Tokens 0 () context

hash :: forall context x . MiMCHash F context x => x -> FieldElement context
hash = mimcHash mimcConstants zero

type Sig context =
    ( StrictConv (FieldElement context) (UInt 256 context)
    , FromConstant Natural (UInt 256 context)
    , MultiplicativeSemigroup (UInt 256 context)
    , AdditiveMonoid (FieldElement context)
    , Symbolic (FieldElement context)
    , MiMCHash F context (TxOut context, TxOut context)
    , Eq (Bool context) (UInt 256 context)
    , Eq (Bool context) (TxOut context)
    , Iso (UInt 256 context) (ByteString 256 context)
    , Extend (ByteString 224 context) (ByteString 256 context))

verifySignature ::
    forall context . Sig context =>
    ByteString 224 context ->
    (TxOut context, TxOut context) ->
    ByteString 256 context ->
    Bool context
verifySignature pub (pay, change) sig = (from sig * base) == (strictConv mimc * from (extend pub :: ByteString 256 context))
    where
        base :: UInt 256 context
        base = fromConstant (15112221349535400772501151409588531511454012693041857206046113283949847762202 :: Natural)

        mimc :: FieldElement context
        mimc = hash (pay, change)

batchTransfer ::
    forall context.  Sig context
    => Tx context
    -> Vector 5 (TxOut context, TxOut context, ByteString 256 context)
    -> Bool context
batchTransfer tx transfers =
    let -- Extract the payment credentials and verify the signatures
        pkhs       = fromJust $ toVector @5 $ map (paymentCredential . txoAddress . txiOutput) $ init $ fromVector $ txInputs tx
        condition1 = all (\(pkh, (payment, change, signature)) -> verifySignature pkh (payment, change) signature) $ zip pkhs transfers
        outputs    = zip [0..] . init . fromVector $ txOutputs tx

        -- Extract the payments from the transaction and validate them
        payments   = fromJust $ toVector @5 $ map snd $ filter (\(i, _) -> even @Integer i) $ outputs

        condition2 = all (\(p', (p, _, _)) -> p' == p) $ zip payments transfers

        -- Extract the changes from the transaction and validate them
        changes    = fromJust $ toVector @5 $ map snd $ filter (\(i, _) -> odd @Integer i) $ outputs
        condition3 = all (\(c', (_, c, _)) -> c' == c) $ zip changes transfers

    in condition1 && condition2 && condition3
