{-# LANGUAGE PatternSynonyms #-}

-- A way of generating arbitrary points on an arbitrary elliptic curve
--
-- To keep this tractable, we only consider component fields of prime order in
-- the range [11, 100), as otherwise, this becomes impossible.
module GenCurve (
    GenCurvePoints (GenCurvePoints),
) where

import Data.Vector.Unboxed.Sized (Vector)
import Data.Vector.Unboxed.Sized qualified as Vector
import GHC.TypeNats (KnownNat)
import Numeric.Natural (Natural)
import Test.QuickCheck (
    Arbitrary (arbitrary, shrink),
    chooseInt,
    elements,
 )

-- The type parameter is how many points you want
--
-- The reason we do it this way is twofold:
--

-- * Generating a random curve is fairly involved, as we also have to generate

--   all of its points to select (at least) one; and

-- * We generally don't want to generate points on _different_ curves in the

--   same generator.
data GenCurvePoints (n :: Natural) = GCP Int Int Int (Vector n (Int, Int))

instance Show (GenCurvePoints n) where
    show (GenCurvePoints order constantA constantB points) =
        "y^2 = x^3 + "
            <> show constantA
            <> "x + "
            <> show constantB
            <> " (mod "
            <> show order
            <> ")\nPoints:\n"
            <> show points

instance (KnownNat n) => Arbitrary (GenCurvePoints n) where
    arbitrary = do
        primeOrder <- elements primes
        let orderLimit = primeOrder - 1
        constantA <- chooseInt (0, orderLimit)
        constantB <- chooseInt (0, orderLimit)
        let wholeCurve = [(x, y) | x <- [0, 1 .. orderLimit], y <- [0, 1 .. orderLimit], (squared y `rem` primeOrder) == ((cubed x + constantA * x + constantB) `rem` primeOrder)]
        GCP primeOrder constantA constantB <$> Vector.replicateM (elements wholeCurve)
    shrink (GCP order constantA constantB points) = do
        let orderLimit = order - 1
        let wholeCurve = [(x, y) | x <- [0, 1 .. orderLimit], y <- [0, 1 .. orderLimit], (squared y `rem` order) == ((cubed x + constantA * x + constantB) `rem` order)]
        GCP order constantA constantB <$> Vector.mapM (go wholeCurve) points
      where
        go :: [(Int, Int)] -> (Int, Int) -> [(Int, Int)]
        go wholeCurve (oldX, oldY) = filter (\(x, y) -> x < oldX || ((x == oldX) && y < oldY)) wholeCurve

-- Read-only pattern synonym to ensure only we can ever make a GenCurvePoints
pattern GenCurvePoints ::
    forall (n :: Natural).
    Int -> Int -> Int -> Vector n (Int, Int) -> GenCurvePoints n
pattern GenCurvePoints order constantA constantB points <- GCP order constantA constantB points

{-# COMPLETE GenCurvePoints #-}

-- Helpers

primes :: [Int]
primes = [11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

squared :: Int -> Int
squared x = x * x

cubed :: Int -> Int
cubed x = x * x * x
