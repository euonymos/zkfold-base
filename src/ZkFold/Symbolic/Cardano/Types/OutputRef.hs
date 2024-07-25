{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -freduction-depth=0 #-} -- Avoid reduction overflow error caused by NumberOfRegisters

module ZkFold.Symbolic.Cardano.Types.OutputRef where

import           Prelude                             hiding (Bool, Eq, length, splitAt, (*), (+))
import qualified Prelude                             as Haskell

import           ZkFold.Symbolic.Cardano.Types.Basic
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Combinators    (RegisterSize (..))
import           ZkFold.Symbolic.Data.FieldElement   (FieldElementData)

type TxRefId context = ByteString 256 context
type TxRefIndex context = UInt 32 Auto context

newtype OutputRef context = OutputRef (TxRefId context, TxRefIndex context)

deriving instance
    ( Haskell.Eq (TxRefId context)
    , Haskell.Eq (TxRefIndex context)
    ) => Haskell.Eq (OutputRef context)

deriving instance FieldElementData CtxEvaluation (OutputRef CtxEvaluation)

deriving instance SymbolicData F (OutputRef CtxCompilation)

outputRefId :: OutputRef context -> TxRefId context
outputRefId (OutputRef (x, _)) = x

outputRefIndex :: OutputRef context -> TxRefIndex context
outputRefIndex (OutputRef (_, i)) = i
