{-# LANGUAGE TypeApplications #-}

module ZkFold.Crypto.Algebra.Polynomials.GroebnerBasis (
    Monomial,
    Polynomial,
    monomial,
    polynomial,
    groebner,
    fromR1CS,
    property,
    -- * Internal
    -- TODO: Remove these and add wrappers.
    lt, 
    zeroM,
    zeroP,
    similarM,
    makeSPoly,
    reduceMany
    ) where

import           Data.Bool                         (bool)
import           Data.List                         (sortBy, sort)
import           Data.Map                          (Map, toList, elems)
import           Prelude                           hiding (Num(..), length, replicate)

import           ZkFold.Crypto.Algebra.Basic.Class
import           ZkFold.Crypto.Algebra.Basic.Field (Zp)
import           ZkFold.Crypto.Algebra.Polynomials.GroebnerBasis.Internal
import           ZkFold.Crypto.Protocol.Arithmetization.R1CS
import           ZkFold.Prelude                    (replicate, length)

type Monomial p = Monom (Zp p) Integer

-- TODO: Check the list length.
monomial :: Zp p -> [Integer] -> Monomial p
monomial = M

type Polynomial p = Polynom (Zp p) Integer

polynomial :: Prime p => [Monomial p] -> Polynomial p
polynomial = P . sortBy (flip compare) . filter (not . zeroM)

groebner :: Prime p => [Polynomial p] -> [Polynomial p]
groebner = makeGroebner . sort

fromR1CS :: forall p t s . Prime p => R1CS (Zp p) t s -> [Polynomial p]
fromR1CS r = sortBy (flip compare) $ map (fromR1CS' @p xs) $ elems m
    where
        m  = r1csSystem r
        xs = reverse $ elems $ r1csVarOrder r

property :: forall p t s . Prime p => R1CS (Zp p) t s -> Polynomial p
property r = polynomial [var xs j one] - polynomial [var xs 0 one]
    where
        xs = reverse $ elems $ r1csVarOrder r
        j = head $ r1csOutput r

-------------------------------------------------------------------------------

mapVars :: [Integer] -> Integer -> Integer
mapVars xs x
    | x == 0    = 0
    | otherwise = case lookup x (zip xs [1..]) of
        Just i  -> i
        Nothing -> error $ "mapVars: variable " ++ show x ++ " not found!"

var :: [Integer] -> Integer -> Zp p -> Monomial p
var xs i v = M v $ reverse $ go (length xs) (mapVars xs i)
    where
        go 0 _ = []
        go k j = bool 0 1 (k == j) : go (k - 1) j

fromR1CS' :: Prime p => [Integer] -> (Map Integer (Zp p), Map Integer (Zp p), Map Integer (Zp p)) -> Polynomial p
fromR1CS' xs (a, b, c) = mulM pa pb `addPoly` mulPM pc (M (negate 1) (replicate (length xs) 0))
    where
        pa = polynomial $ map (uncurry $ var xs) $ toList a
        pb = polynomial $ map (uncurry $ var xs) $ toList b
        pc = polynomial $ map (uncurry $ var xs) $ toList c