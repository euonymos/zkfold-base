module ZkFold.Symbolic.Ledger.Types.Transaction where

import           Prelude                                hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types.Basic
import           ZkFold.Symbolic.Ledger.Types.Contract
import           ZkFold.Symbolic.Ledger.Types.Input     (Input)
import           ZkFold.Symbolic.Ledger.Types.Output    (Output)
import           ZkFold.Symbolic.Ledger.Types.OutputRef (TransactionId)
import           ZkFold.Symbolic.Ledger.Types.Value     (Value)

-- TODO: Either inputs or public inputs should be non-empty. It should be checked during validation.

-- | zkFold ledger transaction.
data Transaction context = Transaction
    { txInputs           :: List context (Input context)
    -- A list of inputs to the transaction.
    , txPublicInputs     :: List context (Input context)
    -- A list of public inputs to the transaction.
    , txOutputs          :: List context (Output context)
    -- A list of outputs of the transaction.
    , txPublicOutputs    :: List context (Output context)
    -- A list of public outputs of the transaction.
    , txMint             :: List context (Value context)
    -- A list of minted values.
    , txContractData     :: List context (ContractId context, ContractData context)
    -- A list of contract data items.
    , txValidityInterval :: (UTCTime context, UTCTime context)
    -- The validity interval of the transaction.
    }

txId :: Transaction context -> TransactionId context
txId = undefined
