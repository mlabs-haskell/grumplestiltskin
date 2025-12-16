{-# LANGUAGE ImpredicativeTypes #-}

module Main (main) where

import Data.Functor.WithIndex (imap)
import Data.Proxy (Proxy (Proxy))
import Data.Vector.Unboxed.Sized qualified as Vector
import GHC.IO.Encoding (setLocaleEncoding, utf8)
import GenCurve (GenCurvePoints (GenCurvePoints))
import Grumplestiltskin.EllipticCurve (PECIntermediatePoint (PECIntermediateInfinity, PECIntermediatePoint), PECPoint (PECInfinity), invPoint, paddPoints, ppointDouble, ptoPoint)
import Plutarch.Internal.Term (Term, punsafeCoerce)
import Plutarch.Prelude (
    PBool,
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
    (#),
    (#==),
    (:-->),
 )
import Plutarch.Test.Unit (testEvalEqual)
import Plutarch.Test.Utils (precompileTerm)
import Test.QuickCheck (Property, arbitrary, forAllShrinkShow, shrink)
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.QuickCheck (testProperty)
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
        , testGroup
            "Case 2: properties"
            [ testProperty "paddPoints associates" propAssocAdd
            , testProperty "paddPoints commutes" propCommAdd
            , testProperty "P - P = point at infinity" propAdditionOfNegatedPoint
            , testProperty "ppointDouble x = paddPoints x x" propDoubleAdd
            ]
        ]
  where
    mkTestCase :: Int -> (forall (s :: S). Term s PECIntermediatePoint) -> TestTree
    mkTestCase i p =
        testEvalEqual
            ("Point after " <> show i <> " successors")
            (nsucc $ fromIntegral i)
            (ptoPoint fieldModulus p)

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
                 in ptoPoint order' (paddPoints order' constantA p1 (paddPoints order' constantA p2 p3))
                        #== ptoPoint order' (paddPoints order' constantA (paddPoints order' constantA p1 p2) p3)

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
         in ptoPoint order' (paddPoints order' constantA p1 (invPoint p1))
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
             in ptoPoint order' (paddPoints order' constantA p1 p2)
                    #== ptoPoint order' (paddPoints order' constantA p2 p1)

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
         in ptoPoint order' (ppointDouble order' constantA p)
                #== ptoPoint order' (paddPoints order' constantA p p)

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
                ptoPoint fieldModulus (pfix (\self -> plam $ \acc remaining -> pif (remaining #== 0) acc (self # paddPoints fieldModulus 0 acc generatorPoint # (remaining - 1))) # generatorPoint # steps)
            )

createPoint :: Term s PInteger -> Term s PInteger -> Term s PECIntermediatePoint
createPoint x y = pcon $ PECIntermediatePoint (unsafeCoerce x) (unsafeCoerce y)
