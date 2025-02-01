{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE OverloadedLists      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Base.Algebra.EllipticCurve.TinyJJ where

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

-- The order of the curve over the base field
type TinyJJ_Scalar = 5  -- the large prime factor of 20
instance Prime TinyJJ_Scalar

-- The order of the base field
type TinyJJ_Base = 13
instance Prime TinyJJ_Base

type Fr = Zp TinyJJ_Scalar -- F20
type Fq = Zp TinyJJ_Base   -- F13

-- Extension F13^4
type IP1 = "IP1"
instance IrreduciblePoly Fq IP1 where
    irreduciblePoly = toPoly [2, 0, 0, 0, 1]  -- 2 + t^4
type Fq4 = Ext4 Fq IP1 -- FIXME: Ext4 is missing


------------------------------------- TinyJJ --------------------------------------

instance Field field => WeierstrassCurve "TinyJJ" field where
  weierstrassA = fromConstant (8 :: Natural)
  weierstrassB = fromConstant (8 :: Natural)

type TinyJJ_Point baseField = Weierstrass "TinyJJ" (Point Bool baseField)

-- type BLS12_381_CompressedPoint baseField =
--   Weierstrass "BLS12-381" (CompressedPoint Bool baseField)

-- instance
--   ( Symbolic.Conditional Bool field
--   , Symbolic.Eq Bool field
--   , FiniteField field
--   , Ord field
--   ) => Compressible Bool (BLS12_381_Point field) where
--     type Compressed (BLS12_381_Point field) = BLS12_381_CompressedPoint field
--     pointCompressed x yBit = Weierstrass (CompressedPoint x yBit False)
--     compress (Weierstrass (Point x y isInf)) =
--       if isInf then pointInf
--       else pointCompressed @Bool @(BLS12_381_Point field) x (y > negate y)
--     decompress (Weierstrass (CompressedPoint x bigY isInf)) =
--       if isInf then pointInf else
--         let b = weierstrassB @"BLS12-381"
--             q = order @field
--             sqrt_ z = z ^ ((q + 1) `Prelude.div` 2)
--             y' = sqrt_ (x * x * x + b)
--             y'' = negate y'
--             y = if bigY then max y' y'' else min y' y''
--         in  pointXY x y

------------------------------------ TinyJJ G1 ------------------------------------

type TinyJJ_G1_Point = TinyJJ_Point Fq

-- type TinyJJ_G1_CompressedPoint = TinyJJ_CompressedPoint Fq

instance CyclicGroup TinyJJ_G1_Point where
  type ScalarFieldOf TinyJJ_G1_Point = Fr
  pointGen = pointXY 1 2 -- FIXME: check!

instance Scale Fr TinyJJ_G1_Point where
  scale n x = scale (toConstant n) x

------------------------------------ TinyJJ G2 ------------------------------------

{-  FIXME: figure this out!
type TinyJJ_G2_Point = TinyJJ_Point Fq4

-- type BLS12_381_G2_CompressedPoint = TinyJJ_CompressedPoint Fq2

instance CyclicGroup TinyJJ_G2_Point where
  type ScalarFieldOf TinyJJ_G2_Point = Fr
  pointGen = pointXY (Ext4 7 0 9 0) (Ext4 0 11 0 1)

instance Scale Fr TinyJJ_G2_Point where
  scale n x = scale (toConstant n) x
-}

------------------------------------ Encoding ------------------------------------

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

-- instance Binary BLS12_381_G1_Point where
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
--               decompress @Bool @BLS12_381_G1_Point
--                 (pointCompressed @Bool @BLS12_381_G1_Point x bigY)
--             else do
--                 bytesY <- replicateM 48 getWord8
--                 let y = ofBytes bytesY
--                 return (pointXY x y)

-- instance Binary BLS12_381_G1_CompressedPoint where
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
--             pointCompressed @Bool @BLS12_381_G1_Point x <$>
--               if compressed then return bigY else do
--                 bytesY <- replicateM 48 getWord8
--                 let y :: Fq = ofBytes bytesY
--                     bigY' = y > negate y
--                 return bigY'

-- instance Binary BLS12_381_G2_Point where
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
--               decompress @Bool @BLS12_381_G2_Point
--                 (pointCompressed @Bool @BLS12_381_G2_Point (Ext2 x0 x1) bigY)
--             else do
--                 bytesY1 <- replicateM 48 getWord8
--                 bytesY0 <- replicateM 48 getWord8
--                 let y0 = ofBytes bytesY0
--                     y1 = ofBytes bytesY1
--                 return (pointXY (Ext2 x0 x1) (Ext2 y0 y1))

-- instance Binary BLS12_381_G2_CompressedPoint where
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
--             pointCompressed @Bool @BLS12_381_G2_Point x <$>
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
-- -- of order @'BLS12_381_Scalar'@.
-- newtype BLS12_381_GT = BLS12_381_GT Fq12
--     deriving newtype (Eq, Show, MultiplicativeSemigroup, MultiplicativeMonoid, Symbolic.Eq Bool)

-- instance Exponent BLS12_381_GT Natural where
--     BLS12_381_GT a ^ p = BLS12_381_GT (a ^ p)

-- instance Exponent BLS12_381_GT Integer where
--     BLS12_381_GT a ^ p = BLS12_381_GT (a ^ p)

-- deriving via (NonZero Fq12) instance MultiplicativeGroup BLS12_381_GT

-- instance Finite BLS12_381_GT where
--     type Order BLS12_381_GT = BLS12_381_Scalar

-- instance Pairing BLS12_381_G1_Point BLS12_381_G2_Point BLS12_381_GT where
--     pairing a b
--       = BLS12_381_GT
--       $ finalExponentiation @Fr
--       $ millerAlgorithmBLS12 param a b
--       where
--         param = [-1
--           ,-1, 0,-1, 0, 0,-1, 0, 0, 0, 0, 0, 0, 0, 0,-1, 0
--           , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
--           , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,-1, 0
--           , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
--           ]
