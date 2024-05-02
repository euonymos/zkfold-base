{-# LANGUAGE TypeApplications #-}

module ZkFold.Base.Algebra.Polynomials.Multivariate
    ( module ZkFold.Base.Algebra.Polynomials.Multivariate.Set
    , module ZkFold.Base.Algebra.Polynomials.Multivariate.Substitution
    , Monomial
    , Variable
    , Polynomial
    , Monomial'
    , Polynomial'
    , mapCoeffs
    , monomial
    , polynomial
    , evalMapM
    , evalVectorM
    , evalPolynomial
    , var
    , variables
    , mapVar
    , mapVarMonomial
    , mapVarPolynomial
    ) where

import           Data.Bifunctor                                            (first, second)
import           Data.Containers.ListUtils                                 (nubOrd)
import           Data.Functor                                              ((<&>))
import           Data.Map.Strict                                           (Map, foldrWithKey, fromListWith, keys, filter,
                                                                            mapKeys, singleton)
import           Numeric.Natural                                           (Natural)
import           Prelude                                                   hiding (Num (..), length, product, replicate,
                                                                            sum, (!!), (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Monomial
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Polynomial
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Set
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Substitution
import           ZkFold.Base.Data.Vector
import           ZkFold.Prelude                                            (elemIndex)

-- | Most general type for a multivariate monomial
type Monomial' = M Natural Natural (Map Natural Natural)

-- | Most general type for a multivariate polynomial
type Polynomial' c = P c Natural Natural (Map Natural Natural) [(c, Monomial')]

-- | Monomial constructor
monomial :: Monomial i j => Map i j -> M i j (Map i j)
monomial = M . Data.Map.Strict.filter (/= zero)

-- | Polynomial constructor
polynomial ::
    Polynomial c i j =>
    [(c, M i j (Map i j))] ->
    P c i j (Map i j) [(c, M i j (Map i j))]
polynomial = foldr (\(c, m) x -> if c == zero then x else P [(c, m)] + x) zero

-- | @'var' i@ is a polynomial \(p(x) = x_i\)
var :: Polynomial c i j => i -> P c i j (Map i j) [(c, M i j (Map i j))]
var x = polynomial [(one, monomial (singleton x one))]

evalMapM :: forall i j b .
    MultiplicativeMonoid b =>
    Exponent b j =>
    (i -> b) -> M i j (Map i j) -> b
evalMapM f (M m) =
    foldrWithKey (\i j x -> (f i ^ j) * x) (one @b) m

evalVectorM :: forall i j b d .
    Monomial i j =>
    MultiplicativeMonoid b =>
    Exponent b j =>
    (i -> b) -> M i j (Vector d (i, Bool)) -> b
evalVectorM f (M (Vector v)) =
    evalMapM f . M . fromListWith (+)
        $ foldr (\(i, x) xs -> if x then (i, one @j) : xs else xs) [] v

evalPolynomial :: forall c i j b m .
    Algebra c b =>
    ((i -> b) -> M i j m -> b) -> (i -> b) -> P c i j m [(c, M i j m)] -> b
evalPolynomial e f (P p) = foldr (\(c, m) x -> x + scale c (e f m)) zero p

-- TODO: traverse once
variables :: forall c i j .
    Ord i =>
    P c i j (Map i j) [(c, M i j (Map i j))] -> [i]
variables (P p) = nubOrd
    . concatMap (\(_, M m) -> keys m)
    $ p

mapCoeffs :: forall c c' i j .
    (c -> c')
    -> P c i j (Map i j) [(c, M i j (Map i j))]
    -> P c' i j (Map i j) [(c', M i j (Map i j))]
mapCoeffs f (P p) = P $ p <&> first f

mapVarMonomial :: [Natural] -> Monomial' -> Monomial'
mapVarMonomial vars (M as) = M $ mapKeys (mapVar vars) as

mapVar :: [Natural] -> Natural -> Natural
mapVar vars x = case x `elemIndex` vars of
    Just i  -> i
    Nothing -> error "mapVar: something went wrong"

mapVarPolynomial :: [Natural] -> Polynomial' c -> Polynomial' c
mapVarPolynomial vars (P ms) = P $ second (mapVarMonomial vars) <$> ms
