module Main (main) where

import Data.Bifunctor (bimap)
import Data.Proxy (Proxy (Proxy))
import Data.Vector.Sized qualified as Vector
import GHC.IO.Encoding (setLocaleEncoding, utf8)
import GenCurve (
    GF11Elem2 (GF11Elem2),
    GenCurvePoints (GenCurvePoints),
    GenOffCurve (GenOffCurve),
    GenOnCurve (GenOnCurve),
 )
import Grumplestiltskin.Degree2.AffinePoint (
    PEC2Point,
    pec2FromElems,
    pec2OnCurve,
 )
import Grumplestiltskin.Degree2.Element (
    D2Element,
    PD2Element,
    mkD2Element,
    pd2Zero,
 )
import Grumplestiltskin.Degree2.EllipticCurveDD qualified as DD
import Grumplestiltskin.Degree2.EllipticCurveII qualified as II
import Numeric.Natural (Natural)
import Plutarch.Evaluate (evalTerm')
import Plutarch.Internal.Term (Config (NoTracing))
import Plutarch.Prelude (
    PBool,
    PInteger,
    PNatural,
    PPositive,
    S,
    Term,
    pcon,
    pconstant,
    phoistAcyclic,
    plam,
    plet,
    plift,
    pmod,
    pnegate,
    pnot,
    pscaleInteger,
    pscaleNatural,
    pscalePositive,
    pupcast,
    pzero,
    (#),
    (#+),
    (#-),
    (:-->),
 )
import Plutarch.Test.Golden (goldenEval, plutarchGolden)
import Plutarch.Test.Utils (precompileTerm)
import Plutarch.Unsafe (punsafeCoerce)
import Test.QuickCheck (
    Property,
    arbitrary,
    counterexample,
    forAll,
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
                "Case 1: properties (II)"
                [ testProperty "#+ associates" propAssocAddII
                , testProperty "x #+ pzero = pzero #+ x = x" propZeroAddII
                , testProperty "pec2Double x = x #+ x" propDoubleAddII
                , testProperty "x #- x = pzero" propInvAddII
                ]
        , adjustOption moreTests $
            testGroup
                "Case 2: properties (DD)"
                [ testProperty "pec2Add associates" propAssocAddDD
                , testProperty "pec2Add x PEC2InfinityI = pec2Add PEC2InfinityI x = x" propZeroAddDD
                , testProperty "pec2Double x = pec2Add x x" propDoubleAddDD
                , testProperty "pec2Add x (pec2Negate x) = PEC2InfinityI" propInvAddDD
                ]
        , adjustOption lotsMoreTests $
            testGroup
                "Case 3: whole curve"
                [ testProperty "pecOnCurve when on" propOnCurve
                , testProperty "pecOnCurve when off" propOffCurve
                ]
        , plutarchGolden
            "Case 4: goldens"
            "extension-ec"
            [ goldenEval "pec2OnCurve" (pec2OnCurve pblsOrder validRSquared validCurveA validCurveB blsC1')
            , goldenEval "#+ (II)" (evalCurve # (blsC1 #+ blsC2))
            , -- Blows budget
              -- , goldenEval "pec2Add (DD)" (evalCurve' # DD.pec2Add pblsOrder validRSquared validCurveA blsC1Direct blsC2Direct)
              goldenEval "pscalePositive (II)" (pscalePositive blsC1 (punsafeCoerce @_ @PInteger 70))
            , goldenEval "pnegate (II)" (pnegate # blsC1)
            , goldenEval "pscaleNatural (II)" (pscaleNatural blsC1 (punsafeCoerce @_ @PInteger 70))
            , goldenEval "pscaleInteger positive (II)" (pscaleInteger blsC1 70)
            , goldenEval "pscaleInteger negative (II)" (pscaleInteger blsC1 (-70))
            ]
        ]
  where
    -- Note (Koz, 05/03/2025): By default, QuickCheck only runs 100 tests, which
    -- is far too few to be useful. Thus, we increase the count.
    moreTests :: QuickCheckTests -> QuickCheckTests
    moreTests = max 1_000
    lotsMoreTests :: QuickCheckTests -> QuickCheckTests
    lotsMoreTests = max 10_000
    evalCurve :: forall (s :: S). Term s (II.PEC2Intermediate :--> PEC2Point)
    evalCurve = phoistAcyclic $ plam $ II.pec2FromIntermediate pblsOrder validRSquared validCurveA

{-
    evalCurve' :: forall (s :: S). Term s (DD.PEC2Intermediate :--> PEC2Point)
    evalCurve' = phoistAcyclic $ plam $ DD.pec2FromIntermediate pblsOrder
-}

-- Properties

propOnCurve :: Property
propOnCurve = forAll arbitrary $ \(GenOnCurve x y) ->
    let xR = toD2 x
        xI = toD2 y
     in plift (precompileTerm (plam go) # pconstant xR # pconstant xI)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PBool
    go x y =
        let z = pec2FromElems x y
         in pec2OnCurve onCurveOrder onCurveIrred onCurveA onCurveB z

propOffCurve :: Property
propOffCurve = forAll arbitrary $ \(GenOffCurve x y) ->
    let xR = toD2 x
        xI = toD2 y
     in plift (precompileTerm (plam go) # pconstant xR # pconstant xI)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PBool
    go x y =
        let z = pec2FromElems x y
         in pnot # pec2OnCurve onCurveOrder onCurveIrred onCurveA onCurveB z

propInvAddII :: Property
propInvAddII = forAllShrinkShow (arbitrary @(GenCurvePoints 1)) shrink show $
    \(GenCurvePoints constantA _ points) ->
        let points' = Vector.map (bimap toD2 toD2) points
            (xR, xI) = Vector.index' points' (Proxy @0)
            constantA' = toD2 constantA
            lhs = plift (precompileTerm (plam goLHS) # pconstant xR # pconstant xI # pconstant constantA')
            rhs = plift (precompileTerm (plam goRHS) # pconstant constantA')
         in counterexample ("x #- x: " <> show lhs) $
                lhs === rhs
  where
    goLHS ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PEC2Point
    goLHS xR xI constantA = plet (II.pec2ToIntermediate $ pec2FromElems xR xI) $ \x ->
        toPEC2 constantA (x #- x)
    goRHS ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PEC2Point
    goRHS constantA = toPEC2 constantA pzero

propInvAddDD :: Property
propInvAddDD = forAllShrinkShow (arbitrary @(GenCurvePoints 1)) shrink show $
    \(GenCurvePoints constantA _ points) ->
        let points' = Vector.map (bimap toD2 toD2) points
            (xR, xI) = Vector.index' points' (Proxy @0)
            constantA' = toD2 constantA
            lhs = plift (precompileTerm (plam goLHS) # pconstant xR # pconstant xI # pconstant constantA')
            rhs = plift (toPEC2' pec2Zero)
         in counterexample ("x #- x: " <> show lhs) $
                lhs === rhs
  where
    goLHS ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PEC2Point
    goLHS xR xI constantA = plet (DD.pec2ToIntermediate $ pec2FromElems xR xI) $ \x ->
        toPEC2' (DD.pec2Add pfieldMod prSquared constantA x (DD.pec2Negate x))

propZeroAddII :: Property
propZeroAddII = forAllShrinkShow (arbitrary @(GenCurvePoints 1)) shrink show $
    \(GenCurvePoints constantA _ points) ->
        let points' = Vector.map (bimap toD2 toD2) points
            (xR, xI) = Vector.index' points' (Proxy @0)
            constantA' = toD2 constantA
            lhs = plift (precompileTerm (plam goLHS) # pconstant xR # pconstant xI # pconstant constantA')
            rhs = plift (precompileTerm (plam goRHS) # pconstant xR # pconstant xI # pconstant constantA')
         in counterexample ("x #+ pzero: " <> show lhs)
                . counterexample ("pzero #+ x: " <> show rhs)
                . counterexample ("x: " <> show (Vector.index' points' (Proxy @0)))
                $ lhs === rhs
  where
    goLHS ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PEC2Point
    goLHS xR xI constantA = plet (II.pec2ToIntermediate $ pec2FromElems xR xI) $ \x ->
        toPEC2 constantA (x #+ pzero)
    goRHS ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PEC2Point
    goRHS xR xI constantA = plet (II.pec2ToIntermediate $ pec2FromElems xR xI) $ \x ->
        toPEC2 constantA (pzero #+ x)

propZeroAddDD :: Property
propZeroAddDD = forAllShrinkShow (arbitrary @(GenCurvePoints 1)) shrink show $
    \(GenCurvePoints constantA _ points) ->
        let points' = Vector.map (bimap toD2 toD2) points
            (xR, xI) = Vector.index' points' (Proxy @0)
            constantA' = toD2 constantA
            lhs = plift (precompileTerm (plam goLHS) # pconstant xR # pconstant xI # pconstant constantA')
            rhs = plift (precompileTerm (plam goRHS) # pconstant xR # pconstant xI # pconstant constantA')
         in counterexample ("x #+ pzero: " <> show lhs)
                . counterexample ("pzero #+ x: " <> show rhs)
                . counterexample ("x: " <> show (Vector.index' points' (Proxy @0)))
                $ lhs === rhs
  where
    goLHS ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PEC2Point
    goLHS xR xI constantA = plet (DD.pec2ToIntermediate $ pec2FromElems xR xI) $ \x ->
        toPEC2' (DD.pec2Add pfieldMod prSquared constantA x pec2Zero)
    goRHS ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PEC2Point
    goRHS xR xI constantA = plet (DD.pec2ToIntermediate $ pec2FromElems xR xI) $ \x ->
        toPEC2' (DD.pec2Add pfieldMod prSquared constantA pec2Zero x)

propDoubleAddII :: Property
propDoubleAddII = forAllShrinkShow (arbitrary @(GenCurvePoints 1)) shrink show $
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
    goLHS xR xI constantA = plet (II.pec2ToIntermediate $ pec2FromElems xR xI) $ \x ->
        toPEC2 constantA (II.pec2Double x)
    goRHS ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PEC2Point
    goRHS xR xI constantA = plet (II.pec2ToIntermediate $ pec2FromElems xR xI) $ \x ->
        toPEC2 constantA (x #+ x)

propDoubleAddDD :: Property
propDoubleAddDD = forAllShrinkShow (arbitrary @(GenCurvePoints 1)) shrink show $
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
    goLHS xR xI constantA = plet (DD.pec2ToIntermediate $ pec2FromElems xR xI) $ \x ->
        toPEC2' (DD.pec2Double pfieldMod prSquared constantA x)
    goRHS ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PEC2Point
    goRHS xR xI constantA = plet (DD.pec2ToIntermediate $ pec2FromElems xR xI) $ \x ->
        toPEC2' (DD.pec2Add pfieldMod prSquared constantA x x)

propAssocAddII :: Property
propAssocAddII = forAllShrinkShow (arbitrary @(GenCurvePoints 3)) shrink show $
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
    goLHS xR xI yR yI zR zI constantA = plet (II.pec2ToIntermediate $ pec2FromElems xR xI) $ \x ->
        plet (II.pec2ToIntermediate $ pec2FromElems yR yI) $ \y ->
            plet (II.pec2ToIntermediate $ pec2FromElems zR zI) $ \z ->
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
    goRHS xR xI yR yI zR zI constantA = plet (II.pec2ToIntermediate $ pec2FromElems xR xI) $ \x ->
        plet (II.pec2ToIntermediate $ pec2FromElems yR yI) $ \y ->
            plet (II.pec2ToIntermediate $ pec2FromElems zR zI) $ \z ->
                toPEC2 constantA ((x #+ y) #+ z)

propAssocAddDD :: Property
propAssocAddDD = forAllShrinkShow (arbitrary @(GenCurvePoints 3)) shrink show $
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
    goLHS xR xI yR yI zR zI constantA = plet (DD.pec2ToIntermediate $ pec2FromElems xR xI) $ \x ->
        plet (DD.pec2ToIntermediate $ pec2FromElems yR yI) $ \y ->
            plet (DD.pec2ToIntermediate $ pec2FromElems zR zI) $ \z ->
                toPEC2' (DD.pec2Add pfieldMod prSquared constantA x (DD.pec2Add pfieldMod prSquared constantA y z))
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
    goRHS xR xI yR yI zR zI constantA = plet (DD.pec2ToIntermediate $ pec2FromElems xR xI) $ \x ->
        plet (DD.pec2ToIntermediate $ pec2FromElems yR yI) $ \y ->
            plet (DD.pec2ToIntermediate $ pec2FromElems zR zI) $ \z ->
                toPEC2' (DD.pec2Add pfieldMod prSquared constantA (DD.pec2Add pfieldMod prSquared constantA x y) z)

-- Helpers

pec2Zero :: forall (s :: S). Term s DD.PEC2Intermediate
pec2Zero = pcon DD.PEC2InfinityI

toD2 :: GF11Elem2 -> D2Element
toD2 (GF11Elem2 r i) = mkD2Element (fromIntegral r) (fromIntegral i) 11

toPEC2 :: forall (s :: S). Term s PD2Element -> Term s II.PEC2Intermediate -> Term s PEC2Point
toPEC2 = II.pec2FromIntermediate pfieldMod prSquared

toPEC2' :: forall (s :: S). Term s DD.PEC2Intermediate -> Term s PEC2Point
toPEC2' = DD.pec2FromIntermediate pfieldMod

pfieldMod :: forall (s :: S). Term s PPositive
pfieldMod = punsafeCoerce @_ @PInteger 11

prSquared :: forall (s :: S). Term s PPositive
prSquared = punsafeCoerce @_ @PInteger 2

-- BLS12-381 2nd degree extension order
bls2Order :: Natural
bls2Order = 16019282247729705411943748644318972617695120099330552659862384536985976748491357143400656079302193429974954385540174732940659106207100323726025938325193045129788127168347624263893040187112659960846674086295148469572963088890738917

pblsOrder :: forall (s :: S). Term s PPositive
pblsOrder = punsafeCoerce . pconstant @PNatural $ bls2Order

validX1 :: Natural
validX1 = 0x24aa2b2_f08f0a91_26080527_2dc51051_c6e47ad4_fa403b02_b4510b64_7ae3d177_0bac0326_a805bbef_d48056c8_c121bdb8

validX2 :: Natural
validX2 = 0xce5d527_727d6e11_8cc9cdc6_da2e351a_adfd9baa_8cbdd3a7_6d429a69_5160d12c_923ac9cc_3baca289_e1935486_08b82801

validY1 :: Natural
validY1 = 0x13e02b60_52719f60_7dacd3a0_88274f65_596bd0d0_9920b61a_b5da61bb_dc7f5049_334cf112_13945d57_e5ac7d05_5d042b7e

validY2 :: Natural
validY2 = 0x606c4a0_2ea734cc_32acd2b0_2bc28b99_cb3e287e_85a763af_267492ab_572e99ab_3f370d27_5cec1da1_aaa9075f_f05f79be

validRSquared :: forall (s :: S). Term s PPositive
validRSquared = evalTerm' NoTracing (punsafeCoerce $ pmod # (-1) # pupcast (pconstant @PNatural bls2Order))

blsC1' :: forall (s :: S). Term s PEC2Point
blsC1' = evalTerm' NoTracing (pec2FromElems (pconstant . mkBLS validX1 $ validY1) (pconstant . mkBLS validX2 $ validY2))

blsC1 :: forall (s :: S). Term s II.PEC2Intermediate
blsC1 = evalTerm' NoTracing (II.pec2ToIntermediate blsC1')

{-
blsC1Direct :: forall (s :: S). Term s DD.PEC2Intermediate
blsC1Direct = evalTerm' NoTracing (DD.pec2ToIntermediate blsC1')

blsC2Direct :: forall (s :: S). Term s DD.PEC2Intermediate
blsC2Direct = evalTerm' NoTracing (DD.pec2Scale pblsOrder validRSquared validCurveA blsC1Direct 3)
-}

blsC2 :: forall (s :: S). Term s II.PEC2Intermediate
blsC2 = evalTerm' NoTracing (pscaleInteger blsC1 3)

mkBLS :: Natural -> Natural -> D2Element
mkBLS x y = mkD2Element x y bls2Order

validCurveA :: forall (s :: S). Term s PD2Element
validCurveA = pd2Zero

validCurveB :: forall (s :: S). Term s PD2Element
validCurveB = evalTerm' NoTracing (pconstant . mkBLS 4 $ 4)

onCurveA :: forall (s :: S). Term s PD2Element
onCurveA = pconstant . mkD2Element 9 1 $ 11

onCurveB :: forall (s :: S). Term s PD2Element
onCurveB = pconstant . mkD2Element 4 8 $ 11

onCurveOrder :: forall (s :: S). Term s PPositive
onCurveOrder = punsafeCoerce (pconstant @PInteger 11)

onCurveIrred :: forall (s :: S). Term s PPositive
onCurveIrred = punsafeCoerce (pconstant @PInteger 2)
