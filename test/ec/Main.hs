{-# LANGUAGE ImpredicativeTypes #-}

module Main (main) where

import Data.Functor.WithIndex (imap)
import Data.Proxy (Proxy (Proxy))
import Data.Vector.Unboxed.Sized qualified as Vector
import GHC.IO.Encoding (setLocaleEncoding, utf8)
import GenCurve (GenCurvePoints (GenCurvePoints))
import Grumplestiltskin.EllipticCurve (
    PECIntermediatePoint (PECIntermediateInfinity, PECIntermediatePoint),
    PECPoint (PECInfinity),
    PECPointData,
    pecAdd,
    pecDouble,
    pecInvert,
    pecScale,
    ptoPoint,
 )
import Plutarch.Evaluate (evalTerm')
import Plutarch.Internal.Term (Config (NoTracing), Term, punsafeCoerce)
import Plutarch.Prelude (
    PAsData,
    PBool,
    PData,
    PInteger,
    PPositive,
    S,
    pcon,
    pconstant,
    pfix,
    pif,
    plam,
    plet,
    plift,
    ptryFrom,
    (#),
    (#*),
    (#+),
    (#==),
    (:-->),
 )
import Plutarch.Test.Golden (goldenEval, plutarchGolden)
import Plutarch.Test.Unit (testEvalEqual)
import Plutarch.Test.Utils (precompileTerm)
import PlutusCore.Data qualified as Plutus
import Test.QuickCheck (Property, arbitrary, forAllShrinkShow, shrink)
import Test.Tasty (TestTree, adjustOption, defaultMain, testGroup)
import Test.Tasty.QuickCheck (QuickCheckMaxSize, QuickCheckTests, testProperty)
import Unsafe.Coerce (unsafeCoerce)

main :: IO ()
main = do
    -- Pre-emptively avoid locale encoding issues
    setLocaleEncoding utf8
    defaultMain . testGroup "Elliptic curve tests" $
        [ testGroup
            "Case 1: y^2 = x^3 + 3 (mod 11), generator (4, 10)"
            . imap mkTestCase
            $ expectedPoints
        , adjustOption moreTests $
            testGroup
                "Case 2: properties"
                [ testProperty "pecAdd associates" propAssocAdd
                , testProperty "pecAdd commutes" propCommAdd
                , testProperty "p - p = point at infinity" propAdditionOfNegatedPoint
                , testProperty "point at infinity is an identity for pecAdd" propIdentityAdd
                , testProperty "pecDouble x = pecAdd x x" propDoubleAdd
                , testProperty "pecScale p 0 = point at infinity" propScaleZero
                , testProperty "pecScale p 1 = p" propScaleOne
                , testProperty "pecScale p -1 = invPoint p" propScaleNegOne
                , adjustOption (smallerTests 2) $ testProperty "pecAdd (pecScale p n) (pecScale p m) = pecScale p (n + m)" propScaleAdd
                , adjustOption (smallerTests 4) $ testProperty "pecScale (pecScale p n) m = pecScale p (n * m)" propScaleMul
                ]
        , plutarchGolden
            "Case 3: goldens over y^2 = x^3 + 49x^2 + 7 (mod 2^127 - 1)"
            "ec"
            [ goldenEval "pecAdd" (pecAdd curveModulus curveA pointX pointY)
            , goldenEval "pecScale" (pecScale curveModulus curveA 10 point)
            , goldenEval "pecInvert" (pecInvert pointX)
            , goldenEval "pecDouble" (pecDouble curveModulus curveA pointX)
            , goldenEval "ptoPoint" (ptoPoint curveModulus pointX)
            , goldenEval "ptryFrom" (ptryFrom @(PAsData PECPointData) pointAsData fst)
            ]
        ]
  where
    mkTestCase :: Int -> (forall (s :: S). Term s PECIntermediatePoint) -> TestTree
    mkTestCase i p =
        testEvalEqual
            ("Point after " <> show i <> " successors")
            (nsucc $ fromIntegral i)
            (ptoPoint fieldModulus p)
    -- Note (Koz, 17/12/2025): The additive and multiplicative properties of scaling end
    -- up creating huge cases that take forever to run. Thus, we have to limit the
    -- size of the `n` and `m` we use to keep this under control.
    smallerTests :: QuickCheckMaxSize -> QuickCheckMaxSize -> QuickCheckMaxSize
    smallerTests factor = (`quot` factor)
    -- Note (Koz, 17/12/2025): By default, QuickCheck only runs 100 tests, which
    -- is far too few to be useful. Thus, we increase the count.
    moreTests :: QuickCheckTests -> QuickCheckTests
    moreTests = max 1000
    point :: forall (s :: S). Term s PECIntermediatePoint
    point = createPoint 337 6621
    pointX :: forall (s :: S). Term s PECIntermediatePoint
    pointX = evalTerm' NoTracing (pecScale curveModulus curveA (-5) point)
    pointY :: forall (s :: S). Term s PECIntermediatePoint
    pointY = evalTerm' NoTracing (pecScale curveModulus curveA 13 point)
    curveModulus :: forall (s :: S). Term s PPositive
    curveModulus = punsafeCoerce @_ @PInteger 170141183460469231731687303715884105727
    curveA :: forall (s :: S). Term s PInteger
    curveA = 49
    pointAsData :: forall (s :: S). Term s PData
    pointAsData =
        pconstant
            ( Plutus.Constr
                1
                [ Plutus.I 170141183460469231731687303715884105727
                , Plutus.I 49
                , Plutus.I 7
                , Plutus.I 337
                , Plutus.I 6621
                ]
            )

-- Properties

propAssocAdd :: Property
propAssocAdd = forAllShrinkShow (arbitrary @(GenCurvePoints 3)) shrink show $ \(GenCurvePoints order constantA _ points) ->
    let (x1, y1) = Vector.index' points (Proxy @0)
        (x2, y2) = Vector.index' points (Proxy @1)
        (x3, y3) = Vector.index' points (Proxy @2)
     in plift
            ( precompileTerm (plam go)
                # pconstant (fromIntegral x1)
                # pconstant (fromIntegral y1)
                # pconstant (fromIntegral x2)
                # pconstant (fromIntegral y2)
                # pconstant (fromIntegral x3)
                # pconstant (fromIntegral y3)
                # pconstant (fromIntegral order)
                # pconstant (fromIntegral constantA)
            )
  where
    go ::
        forall (s :: S).
        Term s PInteger ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PBool
    go x1 y1 x2 y2 x3 y3 order constantA = plet (createPoint x1 y1) $ \p1 ->
        plet (createPoint x2 y2) $ \p2 ->
            plet (createPoint x3 y3) $ \p3 ->
                let order' = punsafeCoerce order
                 in ptoPoint order' (pecAdd order' constantA p1 (pecAdd order' constantA p2 p3))
                        #== ptoPoint order' (pecAdd order' constantA (pecAdd order' constantA p1 p2) p3)

propAdditionOfNegatedPoint :: Property
propAdditionOfNegatedPoint = forAllShrinkShow (arbitrary @(GenCurvePoints 1)) shrink show $ \(GenCurvePoints order constantA _ points) ->
    let (x1, y1) = Vector.index' points (Proxy @0)
     in plift
            ( precompileTerm (plam go)
                # pconstant (fromIntegral x1)
                # pconstant (fromIntegral y1)
                # pconstant (fromIntegral order)
                # pconstant (fromIntegral constantA)
            )
  where
    go ::
        forall (s :: S).
        Term s PInteger ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PBool
    go x1 y1 order constantA = plet (createPoint x1 y1) $ \p1 ->
        let order' = punsafeCoerce order
         in ptoPoint order' (pecAdd order' constantA p1 (pecInvert p1))
                #== pcon PECInfinity

propCommAdd :: Property
propCommAdd = forAllShrinkShow (arbitrary @(GenCurvePoints 2)) shrink show $ \(GenCurvePoints order constantA _ points) ->
    let (x1, y1) = Vector.index' points (Proxy @0)
        (x2, y2) = Vector.index' points (Proxy @1)
     in plift
            ( precompileTerm (plam go)
                # pconstant (fromIntegral x1)
                # pconstant (fromIntegral y1)
                # pconstant (fromIntegral x2)
                # pconstant (fromIntegral y2)
                # pconstant (fromIntegral order)
                # pconstant (fromIntegral constantA)
            )
  where
    go ::
        forall (s :: S).
        Term s PInteger ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PBool
    go x1 y1 x2 y2 order constantA = plet (createPoint x1 y1) $ \p1 ->
        plet (createPoint x2 y2) $ \p2 ->
            let order' = punsafeCoerce order
             in ptoPoint order' (pecAdd order' constantA p1 p2)
                    #== ptoPoint order' (pecAdd order' constantA p2 p1)

propDoubleAdd :: Property
propDoubleAdd = forAllShrinkShow (arbitrary @(GenCurvePoints 1)) shrink show $ \(GenCurvePoints order constantA _ points) ->
    let (x, y) = Vector.index' points (Proxy @0)
     in plift
            ( precompileTerm (plam go)
                # pconstant (fromIntegral x)
                # pconstant (fromIntegral y)
                # pconstant (fromIntegral order)
                # pconstant (fromIntegral constantA)
            )
  where
    go ::
        forall (s :: S).
        Term s PInteger ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PBool
    go x y order constantA = plet (createPoint x y) $ \p ->
        let order' = punsafeCoerce order
         in ptoPoint order' (pecDouble order' constantA p)
                #== ptoPoint order' (pecAdd order' constantA p p)

propIdentityAdd :: Property
propIdentityAdd = forAllShrinkShow (arbitrary @(GenCurvePoints 1)) shrink show $ \(GenCurvePoints order constantA _ points) ->
    let (x, y) = Vector.index' points (Proxy @0)
     in plift
            ( precompileTerm (plam go)
                # pconstant (fromIntegral x)
                # pconstant (fromIntegral y)
                # pconstant (fromIntegral order)
                # pconstant (fromIntegral constantA)
            )
  where
    go ::
        forall (s :: S).
        Term s PInteger ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PBool
    go x y order constantA = plet (createPoint x y) $ \p ->
        let order' = punsafeCoerce order
         in ptoPoint order' (pecAdd order' constantA p (pcon PECIntermediateInfinity))
                #== ptoPoint order' p

propScaleZero :: Property
propScaleZero = forAllShrinkShow (arbitrary @(GenCurvePoints 1)) shrink show $ \(GenCurvePoints order constantA _ points) ->
    let (x, y) = Vector.index' points (Proxy @0)
     in plift
            ( precompileTerm (plam go)
                # pconstant (fromIntegral x)
                # pconstant (fromIntegral y)
                # pconstant (fromIntegral order)
                # pconstant (fromIntegral constantA)
            )
  where
    go ::
        forall (s :: S).
        Term s PInteger ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PBool
    go x y order constantA = plet (createPoint x y) $ \p ->
        let order' = punsafeCoerce order
         in ptoPoint order' (pecScale order' constantA 0 p)
                #== pcon PECInfinity

propScaleOne :: Property
propScaleOne = forAllShrinkShow (arbitrary @(GenCurvePoints 1)) shrink show $ \(GenCurvePoints order constantA _ points) ->
    let (x, y) = Vector.index' points (Proxy @0)
     in plift
            ( precompileTerm (plam go)
                # pconstant (fromIntegral x)
                # pconstant (fromIntegral y)
                # pconstant (fromIntegral order)
                # pconstant (fromIntegral constantA)
            )
  where
    go ::
        forall (s :: S).
        Term s PInteger ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PBool
    go x y order constantA = plet (createPoint x y) $ \p ->
        let order' = punsafeCoerce order
         in ptoPoint order' (pecScale order' constantA 1 p)
                #== ptoPoint order' p

propScaleNegOne :: Property
propScaleNegOne = forAllShrinkShow (arbitrary @(GenCurvePoints 1)) shrink show $ \(GenCurvePoints order constantA _ points) ->
    let (x, y) = Vector.index' points (Proxy @0)
     in plift
            ( precompileTerm (plam go)
                # pconstant (fromIntegral x)
                # pconstant (fromIntegral y)
                # pconstant (fromIntegral order)
                # pconstant (fromIntegral constantA)
            )
  where
    go ::
        forall (s :: S).
        Term s PInteger ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PBool
    go x y order constantA = plet (createPoint x y) $ \p ->
        let order' = punsafeCoerce order
         in ptoPoint order' (pecScale order' constantA (-1) p)
                #== ptoPoint order' (pecInvert p)

propScaleAdd :: Property
propScaleAdd = forAllShrinkShow (arbitrary @(GenCurvePoints 1, Integer, Integer)) shrink show $
    \(GenCurvePoints order constantA _ points, n, m) ->
        let (x, y) = Vector.index' points (Proxy @0)
         in plift
                ( precompileTerm (plam go)
                    # pconstant (fromIntegral x)
                    # pconstant (fromIntegral y)
                    # pconstant (fromIntegral order)
                    # pconstant (fromIntegral constantA)
                    # pconstant n
                    # pconstant m
                )
  where
    go ::
        forall (s :: S).
        Term s PInteger ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PBool
    go x y order constantA n m = plet (createPoint x y) $ \p ->
        let order' = punsafeCoerce order
         in ptoPoint order' (pecAdd order' constantA (pecScale order' constantA n p) (pecScale order' constantA m p))
                #== ptoPoint order' (pecScale order' constantA (n #+ m) p)

propScaleMul :: Property
propScaleMul = forAllShrinkShow (arbitrary @(GenCurvePoints 1, Integer, Integer)) shrink show $
    \(GenCurvePoints order constantA _ points, n, m) ->
        let (x, y) = Vector.index' points (Proxy @0)
         in plift
                ( precompileTerm (plam go)
                    # pconstant (fromIntegral x)
                    # pconstant (fromIntegral y)
                    # pconstant (fromIntegral order)
                    # pconstant (fromIntegral constantA)
                    # pconstant n
                    # pconstant m
                )
  where
    go ::
        forall (s :: S).
        Term s PInteger ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PBool
    go x y order constantA n m = plet (createPoint x y) $ \p ->
        let order' = punsafeCoerce order
         in ptoPoint order' (pecScale order' constantA m (pecScale order' constantA n p))
                #== ptoPoint order' (pecScale order' constantA (n #* m) p)

-- Helpers

expectedPoints :: [forall (s :: S). Term s PECIntermediatePoint]
expectedPoints =
    [ generatorPoint
    , createPoint 7 7
    , createPoint 1 9
    , createPoint 0 6
    , createPoint 8 8
    , createPoint 2 0
    , createPoint 8 3
    , createPoint 0 5
    , createPoint 1 2
    , createPoint 7 4
    , createPoint 4 1
    , pcon PECIntermediateInfinity
    , generatorPoint
    ]

generatorPoint :: forall (s :: S). Term s PECIntermediatePoint
generatorPoint = createPoint 4 10

fieldModulus :: forall (s :: S). Term s PPositive
fieldModulus = punsafeCoerce @_ @PInteger 11

nsucc :: forall (s :: S). Integer -> Term s PECPoint
nsucc i = go # pconstant i
  where
    go :: forall (s' :: S). Term s' (PInteger :--> PECPoint)
    go =
        precompileTerm
            ( plam $ \steps ->
                ptoPoint fieldModulus (pfix (\self -> plam $ \acc remaining -> pif (remaining #== 0) acc (self # pecAdd fieldModulus 0 acc generatorPoint # (remaining - 1))) # generatorPoint # steps)
            )

createPoint :: Term s PInteger -> Term s PInteger -> Term s PECIntermediatePoint
createPoint x y = pcon $ PECIntermediatePoint (unsafeCoerce x) (unsafeCoerce y)
