{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}

module GenCurve (
    GF11Elem2 (GF11Elem2),
    GenCurvePoints (GenCurvePoints),
    GenOnCurve (GenOnCurve),
    GenOffCurve (GenOffCurve),
) where

import Control.Category ((.))
import Control.Monad (guard)
import Data.Bifunctor (Bifunctor (bimap))
import Data.Euclidean (
    Euclidean (degree, quot, quotRem, rem),
    Field,
    GcdDomain,
    gcdExt,
 )
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet (HashSet)
import Data.HashSet qualified as HashSet
import Data.Hashable (Hashable)
import Data.Kind (Type)
import Data.Semiring (
    Ring (negate),
    Semiring (fromNatural, one, plus, times, zero),
    (*),
    (+),
    (-),
 )
import Data.Vector.Sized (Vector)
import Data.Vector.Sized qualified as Vector
import GHC.TypeNats (KnownNat)
import Numeric.Natural (Natural)
import Test.QuickCheck (
    Arbitrary (arbitrary, shrink),
    Gen,
    chooseInt,
    elements,
    liftArbitrary2,
 )
import Prelude (
    Bool,
    Eq ((/=), (==)),
    Int,
    Integral,
    Show (show),
    const,
    filter,
    mod,
    not,
    pure,
    ($),
    (&&),
    (<),
    (<$>),
    (<>),
    (>=),
    (||),
 )
import Prelude qualified as P

{- | Generates a point guaranteed to be on `y^2 = x^3 + (9 + 1u)x + (4 + 8u)`,
with field order 11 and where `u^2 = 2`.
-}
newtype GenOnCurve = GOC (GF11Elem2, GF11Elem2)
    deriving (Eq) via (GF11Elem2, GF11Elem2)

instance Show GenOnCurve where
    show (GOC (x, y)) = "x: " <> show x <> ", y: " <> show y

instance Arbitrary GenOnCurve where
    arbitrary = GOC <$> elements ecOnCurve

pattern GenOnCurve :: GF11Elem2 -> GF11Elem2 -> GenOnCurve
pattern GenOnCurve x y <- GOC (x, y)

{-# COMPLETE GenOnCurve #-}

{- | Generates a point guaranteed _not_ to be on `y^2 = x^3 + (9 + 1u)x + (4 +
8u)`, with field order 11 and where `u^2 = 2`.
-}
newtype GenOffCurve = GOC' (GF11Elem2, GF11Elem2)
    deriving (Eq) via (GF11Elem2, GF11Elem2)

instance Show GenOffCurve where
    show (GOC' (x, y)) = "x: " <> show x <> ", y: " <> show y

instance Arbitrary GenOffCurve where
    arbitrary = GOC' <$> elements ecOffCurve

pattern GenOffCurve :: GF11Elem2 -> GF11Elem2 -> GenOffCurve
pattern GenOffCurve x y <- GOC' (x, y)

{-# COMPLETE GenOffCurve #-}

{-
The type parameter is how many points you want

The reason we do it this way is twofold:

\* Generating a random curve is fairly involved, as we also have to generate
  all of its points to select (at least) one; and
\* We generally don't want to generate points on _different_ curves in the
  same generator.
-}
data GenCurvePoints (n :: Natural) = GCP GF11Elem2 GF11Elem2 (Vector n (GF11Elem2, GF11Elem2))

instance Show (GenCurvePoints n) where
    show (GenCurvePoints constantA constantB points) =
        "y^2 = x^3 + "
            <> show constantA
            <> "x + "
            <> show constantB
            <> " (mod 11)\nPoints:\n"
            <> show points

-- Shrinks to 'simpler' points on the original curve. While shrinking some other
-- way is definitely possible (such as curve constant reduction), this is
-- probably not worth it, as our curve constants never get particularly large
-- anyway, and doing so would be significantly more taxing, as we would have to
-- check square-freeness as well.
instance (KnownNat n) => Arbitrary (GenCurvePoints n) where
    arbitrary = do
        (constantA, allBs) <- elements (HashMap.toList nonSingularMap)
        constantB <- elements (HashSet.toList allBs)
        let wholeCurve = filter (onCurve constantA constantB) allEC
        GCP constantA constantB <$> Vector.replicateM (elements wholeCurve)
    shrink (GCP constantA constantB points) = do
        let wholeCurve = filter (onCurve constantA constantB) allEC
        GCP constantA constantB <$> Vector.mapM (go wholeCurve) points
      where
        go :: [(GF11Elem2, GF11Elem2)] -> (GF11Elem2, GF11Elem2) -> [(GF11Elem2, GF11Elem2)]
        go wholeCurve (GF11E2 (oldR1, oldI1), GF11E2 (oldR2, oldI2)) =
            filter
                ( \(GF11E2 (r1, i1), GF11E2 (r2, i2)) ->
                    r1 < oldR1
                        || ((r1 == oldR1) && i1 < oldI1)
                        || ((r1 == oldR1) && (i1 == oldI1) && r2 < oldR2)
                        || ((r1 == oldR1) && (i1 == oldI1) && (r2 == oldR2) && i2 < oldI2)
                )
                wholeCurve

-- Read-only pattern synonym to ensure only we can ever make a GenCurvePoints
pattern GenCurvePoints ::
    forall (n :: Natural).
    GF11Elem2 -> GF11Elem2 -> Vector n (GF11Elem2, GF11Elem2) -> GenCurvePoints n
pattern GenCurvePoints constantA constantB points <- GCP constantA constantB points

{-# COMPLETE GenCurvePoints #-}

-- Irreducible is 2
newtype GF11Elem2 = GF11E2 (Int, Int)
    deriving (Eq, Hashable) via (Int, Int)

instance Show GF11Elem2 where
    show (GF11E2 (r, i)) = "(" <> show r <> "+" <> show i <> "u)"

instance Semiring GF11Elem2 where
    plus (GF11E2 (r1, i1)) (GF11E2 (r2, i2)) = GF11E2 . reduce $ (r1 + r2, i1 + i2)
    times (GF11E2 (r1, i1)) (GF11E2 (r2, i2)) =
        let r1r2 = r1 * r2
            r1i2 = r1 * i2
            i1r2 = i1 * r2
            i1i2 = i1 * i2
         in GF11E2 . reduce $ (r1r2 + 2 * i1i2, r1i2 + i1r2)
    zero = GF11E2 (0, 0)
    one = GF11E2 (1, 0)
    fromNatural n = GF11E2 (P.fromIntegral $ n `mod` 11, 0)

instance Ring GF11Elem2 where
    negate (GF11E2 (r, i)) = GF11E2 . reduce $ (negate r, negate i)

instance GcdDomain GF11Elem2

instance Euclidean GF11Elem2 where
    quot (GF11E2 (u, v)) = \case
        GF11E2 (0, 0) -> P.error "GF11Elem2 quot: Division by zero"
        GF11E2 (x, y) ->
            let recipExpr = (x * x) - (2 * y * y)
                (g, recipr') = gcdExt recipExpr 11
                recipr = case g of
                    1 -> recipr'
                    -- Means it's negative, as 0 is not possible
                    (-1) -> negate recipr'
                    -- This should not happen
                    _ -> P.error "GF11Elem2 quot: recipr is not 1 or -1"
                ux = u * x
                yv = y * v
                xv = x * v
                uy = u * y
             in GF11E2 . reduce $ ((ux - (2 * yv)) * recipr, (xv - uy) * recipr)
    rem _ = \case
        GF11E2 (0, 0) -> P.error "GF11Elem2 rem: Division by zero"
        _ -> zero
    quotRem x y =
        let !q = quot x y
         in (q, zero)
    degree = const zero

instance Field GF11Elem2

instance Arbitrary GF11Elem2 where
    arbitrary = GF11E2 <$> liftArbitrary2 choose11 choose11
    shrink (GF11E2 (r, i)) = do
        r' <- shrink r
        i' <- shrink i
        guard (r' >= 0)
        guard (i' >= 0)
        pure . GF11E2 $ (r', i')

pattern GF11Elem2 :: Natural -> Natural -> GF11Elem2
pattern GF11Elem2 r i <- (unpack -> (r, i))

{-# COMPLETE GF11Elem2 #-}

-- Helpers

allElems :: [GF11Elem2]
allElems = [GF11E2 (r, i) | r <- [0, 1 .. 10], i <- [0, 1 .. 10]]

allEC :: [(GF11Elem2, GF11Elem2)]
allEC = [(x, y) | x <- allElems, y <- allElems]

choose11 :: Gen Int
choose11 = chooseInt (0, 10)

unpack :: GF11Elem2 -> (Natural, Natural)
unpack (GF11E2 p) = bimap P.fromIntegral P.fromIntegral p

reduce ::
    forall (f :: Type -> Type -> Type) (a :: Type).
    (Bifunctor f, Integral a) => f a a -> f a a
reduce = bimap (`mod` 11) (`mod` 11)

square :: forall (a :: Type). (Semiring a) => a -> a
square x = x * x

cube :: forall (a :: Type). (Semiring a) => a -> a
cube x = x * x * x

isNonSingular :: GF11Elem2 -> GF11Elem2 -> Bool
isNonSingular curveA curveB = scale (cube curveA) 4 + scale (square curveB) 27 /= zero

onCurve :: GF11Elem2 -> GF11Elem2 -> (GF11Elem2, GF11Elem2) -> Bool
onCurve curveA curveB (x, y) = square y == (cube x + (curveA * x) + curveB)

scale :: GF11Elem2 -> Int -> GF11Elem2
scale (GF11E2 (x, y)) n = GF11E2 . reduce $ (x * n, y * n)

-- Easier to precompute all pairs of non-singular EC curve constants than hoping
-- we luck into them
nonSingularMap :: HashMap GF11Elem2 (HashSet GF11Elem2)
nonSingularMap = HashMap.fromList . P.fmap go $ allElems
  where
    go :: GF11Elem2 -> (GF11Elem2, HashSet GF11Elem2)
    go k = (k, HashSet.fromList . filter (isNonSingular k) $ allElems)

ecOnCurve :: [(GF11Elem2, GF11Elem2)]
ecOnCurve = filter (onCurve (GF11E2 (9, 1)) (GF11E2 (4, 8))) allEC

ecOffCurve :: [(GF11Elem2, GF11Elem2)]
ecOffCurve = filter (not . onCurve (GF11E2 (9, 1)) (GF11E2 (4, 8))) allEC
