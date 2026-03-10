module Main (main) where

import Data.Bifunctor (bimap)
import Data.Proxy (Proxy (Proxy))
import Data.Vector.Sized qualified as Vector
import GHC.IO.Encoding (setLocaleEncoding, utf8)
import GenCurve (
    GF11Elem2 (GF11Elem2),
    GenCurvePoints (GenCurvePoints),
 )
import Grumplestiltskin.Degree2 (
    D2Element,
    PD2Element,
    mkD2Element,
 )
import Grumplestiltskin.EllipticCurve2 (
    PEC2Intermediate,
    PEC2Point,
    pec2Double,
    pec2FromElems,
    pec2FromIntermediate,
    pec2ToIntermediate,
 )
import Plutarch.Prelude (
    PInteger,
    PPositive,
    S,
    Term,
    pconstant,
    plam,
    plet,
    plift,
    (#),
    (#+),
 )
import Plutarch.Test.Utils (precompileTerm)
import Plutarch.Unsafe (punsafeCoerce)
import Test.QuickCheck (
    Property,
    arbitrary,
    counterexample,
    forAllShrinkShow,
    shrink,
    (===),
 )
import Test.Tasty (adjustOption, defaultMain, testGroup)
import Test.Tasty.QuickCheck (QuickCheckTests, testProperty)

main :: IO ()
main = do
    -- Pre-emptively avoid locale encoding issues
    setLocaleEncoding utf8
    defaultMain . testGroup "EC over second-degree finite field extensions" $
        [ adjustOption moreTests $
            testGroup
                "Properties"
                [ testProperty "#+ associates" propAssocAdd
                , testProperty "pec2Double x = x #+ x" propDoubleAdd
                ]
        ]
  where
    -- Note (Koz, 05/03/2025): By default, QuickCheck only runs 100 tests, which
    -- is far too few to be useful. Thus, we increase the count.
    moreTests :: QuickCheckTests -> QuickCheckTests
    moreTests = max 1_000

-- Properties

propDoubleAdd :: Property
propDoubleAdd = forAllShrinkShow (arbitrary @(GenCurvePoints 1)) shrink show $
    \(GenCurvePoints constantA _ points) ->
        let points' = Vector.map (bimap toD2 toD2) points
            (xR, xI) = Vector.index' points' (Proxy @0)
            constantA' = toD2 constantA
            lhs = plift (precompileTerm (plam goLHS) # pconstant xR # pconstant xI # pconstant constantA')
            rhs = plift (precompileTerm (plam goRHS) # pconstant xR # pconstant xI # pconstant constantA')
         in counterexample ("pecDouble x: " <> show lhs)
                . counterexample ("x #+ x: " <> show rhs)
                $ lhs === rhs
  where
    goLHS ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PEC2Point
    goLHS xR xI constantA = plet (pec2ToIntermediate $ pec2FromElems xR xI) $ \x ->
        toPEC2 constantA (pec2Double x)
    goRHS ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PEC2Point
    goRHS xR xI constantA = plet (pec2ToIntermediate $ pec2FromElems xR xI) $ \x ->
        toPEC2 constantA (x #+ x)

propAssocAdd :: Property
propAssocAdd = forAllShrinkShow (arbitrary @(GenCurvePoints 3)) shrink show $
    \(GenCurvePoints constantA _ points) ->
        let points' = Vector.map (bimap toD2 toD2) points
            (xR, xI) = Vector.index' points' (Proxy @0)
            (yR, yI) = Vector.index' points' (Proxy @1)
            (zR, zI) = Vector.index' points' (Proxy @2)
            constantA' = toD2 constantA
            lhs =
                plift
                    ( precompileTerm (plam goLHS)
                        # pconstant xR
                        # pconstant xI
                        # pconstant yR
                        # pconstant yI
                        # pconstant zR
                        # pconstant zI
                        # pconstant constantA'
                    )
            rhs =
                plift
                    ( precompileTerm (plam goRHS)
                        # pconstant xR
                        # pconstant xI
                        # pconstant yR
                        # pconstant yI
                        # pconstant zR
                        # pconstant zI
                        # pconstant constantA'
                    )
         in counterexample ("x + (y + z): " <> show lhs)
                . counterexample ("(x + y) + z: " <> show rhs)
                $ lhs === rhs
  where
    goLHS ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PEC2Point
    goLHS xR xI yR yI zR zI constantA = plet (pec2ToIntermediate $ pec2FromElems xR xI) $ \x ->
        plet (pec2ToIntermediate $ pec2FromElems yR yI) $ \y ->
            plet (pec2ToIntermediate $ pec2FromElems zR zI) $ \z ->
                toPEC2 constantA (x #+ (y #+ z))
    goRHS ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PEC2Point
    goRHS xR xI yR yI zR zI constantA = plet (pec2ToIntermediate $ pec2FromElems xR xI) $ \x ->
        plet (pec2ToIntermediate $ pec2FromElems yR yI) $ \y ->
            plet (pec2ToIntermediate $ pec2FromElems zR zI) $ \z ->
                toPEC2 constantA ((x #+ y) #+ z)

-- Helpers

toD2 :: GF11Elem2 -> D2Element
toD2 (GF11Elem2 r i) = mkD2Element (fromIntegral r) (fromIntegral i) 11

toPEC2 :: forall (s :: S). Term s PD2Element -> Term s PEC2Intermediate -> Term s PEC2Point
toPEC2 = pec2FromIntermediate pfieldMod prSquared

pfieldMod :: forall (s :: S). Term s PPositive
pfieldMod = punsafeCoerce @_ @PInteger 11

prSquared :: forall (s :: S). Term s PPositive
prSquared = punsafeCoerce @_ @PInteger 2
