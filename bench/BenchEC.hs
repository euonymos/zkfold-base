{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Main where

import           Control.DeepSeq                             (NFData, force)
import           Control.Exception                           (evaluate)
import           Control.Monad                               (forM_, replicateM)
import           Prelude                                     hiding (sum, (*), (+), (-), (/), (^))
import qualified Prelude                                     as P
import           System.Random                               (randomRIO)
import           Test.Tasty.Bench
import           GHC.Generics                                (Par1 (Par1), U1)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Vector 
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.EllipticCurve.Ed25519
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit
import           ZkFold.Symbolic.Data.Ed25519
import           ZkFold.Symbolic.Data.FFA
import           ZkFold.Symbolic.Interpreter

type PtFFA ctx = (FFA Ed25519_Base ctx, FFA Ed25519_Base ctx)
type I = Interpreter (Zp BLS12_381_Scalar)
type A = ArithmeticCircuit (Zp BLS12_381_Scalar) U1

mulFFA :: forall ctx . (Symbolic ctx, NFData (ctx (Vector Size))) => Natural -> PtFFA ctx -> PtFFA ctx
mulFFA 0 p = p
mulFFA n p
  | even n = mulFFA (n `P.div` 2) (ffaDouble p)
  | otherwise = ffaAdd (mulFFA (n -! 1) p) p

a :: Symbolic ctx => FFA Ed25519_Base ctx
a = fromConstant (-1)

d :: Symbolic ctx => FFA Ed25519_Base ctx
d = fromConstant (-121665) // fromConstant 121666

ffaDouble :: (Symbolic ctx, NFData (ctx (Vector Size))) => PtFFA ctx -> PtFFA ctx
ffaDouble (x, y) = (x + y, x * y)
--ffaDouble (x, y) = (x3, y3)
    where
        xsq = x * x
        ysq = y * y
        xy = x * y
        x3 = force $ (xy + xy) // (a * xsq + ysq)
        y3 = force $ (ysq - a * xsq) // (one + one - a * xsq  - ysq)

ffaAdd :: (Symbolic ctx, NFData (ctx (Vector Size))) => PtFFA ctx -> PtFFA ctx -> PtFFA ctx
ffaAdd (x1, y1) (x2, y2) = (x1 + x2, y1 * y2)
--ffaAdd (x1, y1) (x2, y2) = (x3, y3)
    where
        prodx = x1 * x2
        prody = y1 * y2
        prod4 = d * prodx * prody
        x3 = force $ (x1 * y2 + y1 * x2) // (one + prod4)
        y3 = force $ (prody - a * prodx) // (one - prod4)

ffaGen :: Symbolic ctx => PtFFA ctx
ffaGen =
    ( fromConstant (15112221349535400772501151409588531511454012693041857206046113283949847762202 :: Natural)
    , fromConstant (46316835694926478169428394003475163141307993866256225615783033603165251855960 :: Natural)
    )

benchOps :: (Show a, NFData a) => String -> a -> (Natural-> a -> a) -> Benchmark
--benchOps desc p0 op = env (fromIntegral <$> randomRIO (1 :: Integer, P.fromIntegral $ value @Ed25519_Base)) $ \ ~n ->
benchOps desc p0 op = env (fromIntegral <$> randomRIO (1 :: Integer, 3)) $ \ ~n ->
    bgroup ("Point scaling") $ [bench desc $ nf (flip op p0) n]


main :: IO ()
main = do
  defaultMain
      [ bgroup "EC operations"
        [ benchOps "FFA Interpreter" (ffaGen :: PtFFA I) mulFFA
        , benchOps "FFA Circuit" (ffaGen :: PtFFA A) mulFFA
--        , benchOps "UInt" (gen :: Point (Ed25519 I)) pointMul 
        ]
      ]
