{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE OverloadedLists      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Base.Algebra.EllipticCurve.BLS6_6 where

import           Control.Monad
import           Data.Bits
import           Data.Foldable
import           Data.Word
import           Prelude                                    hiding (Num (..), (/), (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.EllipticCurve.Pairing
import           ZkFold.Base.Algebra.Polynomials.Univariate
import           ZkFold.Base.Data.ByteString
import qualified ZkFold.Symbolic.Data.Conditional           as Symbolic
import qualified ZkFold.Symbolic.Data.Eq                    as Symbolic

-------------------------------- Introducing Fields ----------------------------------

type BLS6_6_Scalar = 13 -- This is the biggest prime subgroup
instance Prime BLS6_6_Scalar

type BLS6_6_Base = 43
instance Prime BLS6_6_Base

type Fr = Zp BLS6_6_Scalar
type Fq = Zp BLS6_6_Base

type IP1 = "IP1"
instance IrreduciblePoly Fq IP1 where
    irreduciblePoly = toPoly [1, 0, 1] -- FIXME:
type Fq2 = Ext2 Fq IP1

type IP2 = "IP2"
instance IrreduciblePoly Fq2 IP2 where
    irreduciblePoly =
        let e = Ext2 1 1 -- FIXME:
        in toPoly [negate e, zero, zero, one]
type Fq6 = Ext3 Fq2 IP2

------------------------------------- BLS6-6-G1 --------------------------------------

instance WeierstrassCurve "BLS6-6-G1" Fq where
  weierstrassB = 6

type BLS6_6_G1_Point = Weierstrass "BLS6-6-G1" (Point Fq)

-- type BLS6_6_G1_CompressedPoint =
--   Weierstrass "BLS6-6-G1" (CompressedPoint Fq)

-- instance Compressible BLS6_6_G1_Point where
--     type Compressed BLS6_6_G1_Point = BLS6_6_G1_CompressedPoint
--     pointCompressed x yBit = Weierstrass (CompressedPoint x yBit False)
--     compress (Weierstrass (Point x y isInf)) =
--       if isInf then pointInf
--       else pointCompressed @BLS6_6_G1_Point x (y > negate y)
--     decompress (Weierstrass (CompressedPoint x bigY isInf)) =
--       if isInf then pointInf else
--         let b = weierstrassB @"BLS6-6-G1"
--             q = order @Fq
--             sqrt_ z = z ^ ((q + 1) `Prelude.div` 2)
--             y' = sqrt_ (x * x * x + b)
--             y'' = negate y'
--             y = if bigY then max y' y'' else min y' y''
--         in  pointXY x y

instance CyclicGroup BLS6_6_G1_Point where
  type ScalarFieldOf BLS6_6_G1_Point = Fr
  pointGen = pointXY 13 15 -- This is the generator for G1[13]

instance Scale Fr BLS6_6_G1_Point where
  scale n x = scale (toConstant n) x

------------------------------------ BLS6-6-G2 ------------------------------------

-- FIXME: why Fq2 here and not Fq12 (for BLS12-381?)
instance WeierstrassCurve "BLS6-6-G2" Fq2 where
  weierstrassB = Ext2 4 4

type BLS6_6_G2_Point = Weierstrass "BLS6-6-G2" (Point Fq2)

type BLS6_6_G2_CompressedPoint =
  Weierstrass "BLS6-6-G2" (CompressedPoint Fq2)

instance CyclicGroup BLS6_6_G2_Point where
  type ScalarFieldOf BLS6_6_G2_Point = Fr
  pointGen = pointXY
    (Ext2
      0x24aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8
      0x13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e)
    (Ext2
      0xce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801
      0x606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be)

instance Scale Fr BLS6_6_G2_Point where
  scale n x = scale (toConstant n) x

instance Compressible BLS6_6_G2_Point where
    type Compressed BLS6_6_G2_Point = BLS6_6_G2_CompressedPoint
    pointCompressed x yBit = Weierstrass (CompressedPoint x yBit False)
    compress (Weierstrass (Point x y isInf)) =
      if isInf then pointInf
      else pointCompressed @BLS6_6_G2_Point x (y > negate y)
    decompress (Weierstrass (CompressedPoint x bigY isInf)) =
      if isInf then pointInf else
        let b = weierstrassB @"BLS6-6-G2"
            q = order @Fq2
            sqrt_ z = z ^ ((q + 1) `Prelude.div` 2)
            y' = sqrt_ (x * x * x + b)
            y'' = negate y'
            y = if bigY then max y' y'' else min y' y''
        in  pointXY x y

-- ------------------------------------ Encoding ------------------------------------

-- -- infinite list of divMod 256's, little endian order
-- leBytesOf :: Natural -> [(Natural, Word8)]
-- leBytesOf n =
--     let
--         (n', r) = n `Prelude.divMod` 256
--     in
--         (n', fromIntegral r) : leBytesOf n'

-- -- finite list of bytes, big endian order
-- bytesOf :: (ToConstant a, Const a ~ Natural) => Int -> a -> [Word8]
-- bytesOf n
--     = reverse
--     . take n
--     . map snd
--     . leBytesOf
--     . toConstant

-- -- big endian decoding
-- ofBytes :: FromConstant Natural a => [Word8] -> a
-- ofBytes
--   = fromConstant @Natural
--   . foldl' (\n w8 -> n * 256 + fromIntegral w8) 0

-- instance Binary BLS6_6_G1_Point where
--     put (Weierstrass (Point x y isInf)) =
--         if isInf then foldMap putWord8 (bitReverse8 (bit 1) : replicate 95 0)
--                  else foldMap putWord8 (bytesOf 48 x <> bytesOf 48 y)
--     get = do
--         byte <- bitReverse8 <$> getWord8
--         let compressed = testBit byte 0
--             infinite = testBit byte 1
--         if infinite then do
--             skip (if compressed then 47 else 95)
--             return pointInf
--         else do
--             let byteXhead = bitReverse8 $ clearBit (clearBit (clearBit byte 0) 1) 2
--             bytesXtail <- replicateM 47 getWord8
--             let x = ofBytes (byteXhead:bytesXtail)
--                 bigY = testBit byte 2
--             if compressed then return $
--               decompress @BLS6_6_G1_Point
--                 (pointCompressed @BLS6_6_G1_Point x bigY)
--             else do
--                 bytesY <- replicateM 48 getWord8
--                 let y = ofBytes bytesY
--                 return (pointXY x y)

-- instance Binary BLS6_6_G1_CompressedPoint where
--     put (Weierstrass (CompressedPoint x bigY isInf)) =
--         if isInf then foldMap putWord8 (bitReverse8 (bit 0 .|. bit 1) : replicate 47 0) else
--         let
--             flags = bitReverse8 $ if bigY then bit 0 .|. bit 2 else bit 0
--             bytes = bytesOf 48 x
--         in foldMap putWord8 ((flags .|. head bytes) : tail bytes)
--     get = do
--         byte <- bitReverse8 <$> getWord8
--         let compressed = testBit byte 0
--             infinite = testBit byte 1
--         if infinite then do
--             skip (if compressed then 47 else 95)
--             return pointInf
--         else do
--             let byteXhead = bitReverse8 $ clearBit (clearBit (clearBit byte 0) 1) 2
--             bytesXtail <- replicateM 47 getWord8
--             let x = ofBytes (byteXhead:bytesXtail)
--                 bigY = testBit byte 2
--             pointCompressed @BLS6_6_G1_Point x <$>
--               if compressed then return bigY else do
--                 bytesY <- replicateM 48 getWord8
--                 let y :: Fq = ofBytes bytesY
--                     bigY' = y > negate y
--                 return bigY'

-- instance Binary BLS6_6_G2_Point where
--     put (Weierstrass (Point (Ext2 x0 x1) (Ext2 y0 y1) isInf)) =
--         if isInf then foldMap putWord8 (bitReverse8 (bit 1) : replicate 191  0) else
--         let
--             bytes = bytesOf 48 x1
--               <> bytesOf 48 x0
--               <> bytesOf 48 y1
--               <> bytesOf 48 y0
--         in
--             foldMap putWord8 bytes
--     get = do
--         byte <- bitReverse8 <$> getWord8
--         let compressed = testBit byte 0
--             infinite = testBit byte 1
--         if infinite then do
--             skip (if compressed then 95 else 191)
--             return pointInf
--         else do
--             let byteX1head = bitReverse8 $ clearBit (clearBit (clearBit byte 0) 1) 2
--             bytesX1tail <- replicateM 47 getWord8
--             bytesX0 <- replicateM 48 getWord8
--             let x1 = ofBytes (byteX1head:bytesX1tail)
--                 x0 = ofBytes bytesX0
--                 bigY = testBit byte 2
--             if compressed then return $
--               decompress @BLS6_6_G2_Point
--                 (pointCompressed @BLS6_6_G2_Point (Ext2 x0 x1) bigY)
--             else do
--                 bytesY1 <- replicateM 48 getWord8
--                 bytesY0 <- replicateM 48 getWord8
--                 let y0 = ofBytes bytesY0
--                     y1 = ofBytes bytesY1
--                 return (pointXY (Ext2 x0 x1) (Ext2 y0 y1))

-- instance Binary BLS6_6_G2_CompressedPoint where
--     put (Weierstrass (CompressedPoint (Ext2 x0 x1) bigY isInf)) =
--         if isInf then foldMap putWord8 (bitReverse8 (bit 0 .|. bit 1) : replicate 95 0) else
--         let
--             flags = bitReverse8 $ if bigY then bit 0 .|. bit 2 else bit 0
--             bytes = bytesOf 48 x1 <> bytesOf 48 x0
--         in
--             foldMap putWord8 ((flags .|. head bytes) : tail bytes)
--     get = do
--         byte <- bitReverse8 <$> getWord8
--         let compressed = testBit byte 0
--             infinite = testBit byte 1
--         if infinite then do
--             skip (if compressed then 95 else 191)
--             return pointInf
--         else do
--             let byteX1head = bitReverse8 $ clearBit (clearBit (clearBit byte 0) 1) 2
--             bytesX1tail <- replicateM 47 getWord8
--             bytesX0 <- replicateM 48 getWord8
--             let x1 = ofBytes (byteX1head:bytesX1tail)
--                 x0 = ofBytes bytesX0
--                 x = Ext2 x0 x1
--                 bigY = testBit byte 2
--             pointCompressed @BLS6_6_G2_Point x <$>
--               if compressed then return bigY else do
--                 bytesY1 <- replicateM 48 getWord8
--                 bytesY0 <- replicateM 48 getWord8
--                 let y0 = ofBytes bytesY0
--                     y1 = ofBytes bytesY1
--                     y :: Fq2 = Ext2 y0 y1
--                     bigY' = y > negate y
--                 return bigY'

-- --------------------------------------- Pairing ---------------------------------------

-- -- | An image of a pairing is a cyclic multiplicative subgroup of @'Fq12'@
-- -- of order @'BLS6_6_Scalar'@.
-- newtype BLS6_6_GT = BLS6_6_GT Fq12
--     deriving newtype
--         ( Eq
--         , Show
--         , MultiplicativeSemigroup
--         , MultiplicativeMonoid
--         , Symbolic.Conditional Prelude.Bool
--         , Symbolic.Eq
--         )

-- instance Exponent BLS6_6_GT Natural where
--     BLS6_6_GT a ^ p = BLS6_6_GT (a ^ p)

-- instance Exponent BLS6_6_GT Integer where
--     BLS6_6_GT a ^ p = BLS6_6_GT (a ^ p)

-- deriving via (NonZero Fq12) instance MultiplicativeGroup BLS6_6_GT

-- instance Finite BLS6_6_GT where
--     type Order BLS6_6_GT = BLS6_6_Scalar

-- instance Pairing BLS6_6_G1_Point BLS6_6_G2_Point BLS6_6_GT where
--     pairing a b
--       = BLS6_6_GT
--       $ finalExponentiation @Fr
--       $ millerAlgorithmBLS12 param a b
--       where
--         param = [-1
--           ,-1, 0,-1, 0, 0,-1, 0, 0, 0, 0, 0, 0, 0, 0,-1, 0
--           , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
--           , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,-1, 0
--           , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
--           ]
