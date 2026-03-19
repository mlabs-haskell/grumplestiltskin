{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE PatternSynonyms #-}

module GenD2 (
    GenD2Elements (GenD2Elements),
    GenD2NZElements (GenD2NZElements),
) where

import Control.Monad (guard)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.Maybe (fromJust)
import Data.Vector.Sized (Vector)
import Data.Vector.Sized qualified as Vector
import GHC.TypeNats (KnownNat)
import Grumplestiltskin.Degree2 (D2Element (D2Element), mkD2Element)
import Numeric.Natural (Natural)
import Test.QuickCheck (
    Arbitrary (arbitrary, shrink),
    Gen,
    chooseInt,
    elements,
 )

data GenD2Elements (n :: Natural) = GenD2Elements' Natural Natural (Vector n D2Element)
    deriving stock (Eq)

instance Show (GenD2Elements n) where
    show (GenD2Elements' order irred els) =
        "Extension of GF(" <> show order <> "), u^2 = " <> show irred <> ", elements: " <> show els

instance (KnownNat n) => Arbitrary (GenD2Elements n) where
    arbitrary = do
        order <- elements . IntSet.toList $ primes
        let order' :: Natural = fromIntegral order
        irred <- elements . IntSet.toList . fromJust . IntMap.lookup order $ irreducibles
        els <- Vector.replicateM (mkD2 order)
        pure . GenD2Elements' order' (fromIntegral irred) $ els
    shrink (GenD2Elements' order irred els) = do
        let order' :: Int = fromIntegral order
        let irred' :: Int = fromIntegral irred
        irred'' <- maybe [] (IntSet.toList . fst . IntSet.split irred') (IntMap.lookup order' irreducibles)
        GenD2Elements' order (fromIntegral irred'') <$> Vector.mapM (shrinkD2 order) els

pattern GenD2Elements :: Natural -> Natural -> Vector n D2Element -> GenD2Elements n
pattern GenD2Elements order irred els <- GenD2Elements' order irred els

{-# COMPLETE GenD2Elements #-}

-- First is the number of zeroable elements, second is the number of nonzero
-- ones
data GenD2NZElements (n :: Natural) (m :: Natural) = GNZE Natural Natural (Vector n D2Element) (Vector m D2Element)
    deriving stock (Eq)

instance Show (GenD2NZElements n m) where
    show (GNZE order irred xs ys) =
        "Extension of GF(" <> show order <> "), u^2 = " <> show irred <> ", elements: " <> show (xs Vector.++ ys)

instance (KnownNat n, KnownNat m) => Arbitrary (GenD2NZElements n m) where
    arbitrary = do
        order <- elements . IntSet.toList $ primes
        let order' :: Natural = fromIntegral order
        irred <- elements . IntSet.toList . fromJust . IntMap.lookup order $ irreducibles
        xs <- Vector.replicateM (mkD2 order)
        ys <- Vector.replicateM (mkNZD2 order)
        pure . GNZE order' (fromIntegral irred) xs $ ys
    shrink (GNZE order irred xs ys) = do
        let order' :: Int = fromIntegral order
        let irred' :: Int = fromIntegral irred
        irred'' <- maybe [] (IntSet.toList . fst . IntSet.split irred') (IntMap.lookup order' irreducibles)
        GNZE order (fromIntegral irred'') <$> Vector.mapM (shrinkD2 order) xs <*> Vector.mapM (shrinkNZD2 order) ys

pattern GenD2NZElements :: Natural -> Natural -> Vector n D2Element -> Vector m D2Element -> GenD2NZElements n m
pattern GenD2NZElements order irred xs ys <- GNZE order irred xs ys

{-# COMPLETE GenD2NZElements #-}

-- Helpers

-- Start at 11 because that's the first non-trivial case
primes :: IntSet
primes = [11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

irreducibles :: IntMap IntSet
irreducibles = IntMap.fromSet go primes
  where
    go :: Int -> IntSet
    go p =
        let options = IntSet.fromRange (2, p - 1)
            squares = IntSet.map (\x -> mod (x * x) p) options
         in IntSet.difference options squares

mkD2 :: Int -> Gen D2Element
mkD2 order = do
    x <- chooseInt (0, order - 1)
    y <- chooseInt (0, order - 1)
    pure . mkD2Element (fromIntegral x) (fromIntegral y) . fromIntegral $ order

mkNZD2 :: Int -> Gen D2Element
mkNZD2 order = do
    x <- chooseInt (0, order - 1)
    y <- case x of
        0 -> chooseInt (1, order - 1)
        _ -> chooseInt (0, order - 1)
    pure . mkD2Element (fromIntegral x) (fromIntegral y) . fromIntegral $ order

shrinkD2 :: Natural -> D2Element -> [D2Element]
shrinkD2 order (D2Element x y) = mkD2Element <$> shrink x <*> shrink y <*> pure order

shrinkNZD2 :: Natural -> D2Element -> [D2Element]
shrinkNZD2 order (D2Element x y) = do
    x' <- shrink x
    y' <- shrink y
    guard (x' > 0 || y' > 0)
    pure . mkD2Element x' y' $ order
