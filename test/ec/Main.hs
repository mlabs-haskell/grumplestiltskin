{-# LANGUAGE ImpredicativeTypes #-}

module Main (main) where

import Data.Functor.WithIndex (imap)
import GHC.IO.Encoding (setLocaleEncoding, utf8)
import Grumplestiltskin.EllipticCurve (
    PECIntermediatePoint (PECIntermediateInfinity, PECIntermediatePoint),
    PECPoint,
    paddPoints,
    ptoPoint,
 )
import Plutarch.Builtin.Integer (PInteger)
import Plutarch.Internal.Term (Term, punsafeCoerce)
import Plutarch.Prelude (
    PPositive,
    S,
    pcon,
    pconstant,
    pfix,
    pif,
    plam,
    (#),
    (#==),
    (:-->),
 )
import Plutarch.Test.Unit (testEvalEqual)
import Plutarch.Test.Utils (precompileTerm)
import Test.QuickCheck.Instances.Natural ()
import Test.Tasty (TestTree, defaultMain, testGroup)
import Unsafe.Coerce (unsafeCoerce)

main :: IO ()
main = do
    -- Pre-emptively avoid locale encoding issues
    setLocaleEncoding utf8
    defaultMain . testGroup "Elliptic curve tests" $
        [ testGroup
            "Case 1: y^2 = x^2 + 3 (mod 11), generator (4, 10)"
            . imap mkTestCase
            $ expectedPoints
        ]
  where
    mkTestCase :: Int -> (forall (s :: S). Term s PECIntermediatePoint) -> TestTree
    mkTestCase i p =
        testEvalEqual
            ("Point after " <> show i <> " successors")
            (nsucc $ fromIntegral i)
            (ptoPoint fieldModulus p)

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
