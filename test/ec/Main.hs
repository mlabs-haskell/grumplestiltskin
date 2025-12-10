{-# OPTIONS_GHC -Wno-unused-imports #-}

module Main (main, showPoint) where

import GHC.IO.Encoding (setLocaleEncoding, utf8)
import Grumplestiltskin.EllipticCurve (PECIntermediatePoint (PECIntermediateInfinity, PECIntermediatePoint), PECPoint (PECInfinity, PECPoint), pAddPoints, pToPoint)
import Plutarch.Builtin.Integer (PInteger)
import Plutarch.Internal.Term (Term, punsafeCoerce)
import Plutarch.Pair (PPair (PPair))
import Plutarch.Prelude (PPositive, PString, pcon, pconstant, plift, pmap, pmatch, pshow, (#&&), (#==))
import Plutarch.Test.Utils (precompileTerm)
import Test.QuickCheck.Instances.Natural ()
import Test.Tasty (adjustOption, defaultMain, testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)
import Test.Tasty.QuickCheck (QuickCheckTests)
import Unsafe.Coerce (unsafeCoerce)

main :: IO ()
main = do
    -- Pre-emptively avoid locale encoding issues
    setLocaleEncoding utf8
    defaultMain . adjustOption moreTests . testGroup "Elliptic curve tests" $
        [ testGroup
            "Case 1: y^2 = x^2 + 3 (mod 11)"
            [ testCase
                "Generate all points with generator point (4, 10)"
                ( assertEqual
                    "Unexpected points"
                    True
                    ( plift $
                        precompileTerm $
                            foldl (\acc (actual, expected) -> acc #&& (actual #== expected)) (pconstant True) $
                                let generatorPoint = createPoint 4 10
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
                                 in zip
                                        (case1AdditionTest generatorPoint (length expectedPoints))
                                        ( map
                                            (pToPoint (mkPPositive 11))
                                            expectedPoints
                                        )
                    )
                )
            ]
        ]
  where
    moreTests :: QuickCheckTests -> QuickCheckTests
    moreTests = max 1_000

-- | For debugging purposes
showPoint :: Term s PECPoint -> Term s PString
showPoint p =
    pmatch
        p
        ( \case
            PECInfinity -> "Inf"
            (PECPoint x y) -> pshow @(PPair PInteger PInteger) $ pcon $ PPair (unsafeCoerce x) (unsafeCoerce y)
        )

createPoint :: Term s PInteger -> Term s PInteger -> Term s PECIntermediatePoint
createPoint x y = pcon $ PECIntermediatePoint (unsafeCoerce x) (unsafeCoerce y)

mkPPositive :: Term s PInteger -> Term s PPositive
mkPPositive = punsafeCoerce

{- | y^2 = x^2 + 3 (mod 11)

Using the generator point, generate `n` points.
-}
case1AdditionTest :: Term s PECIntermediatePoint -> Int -> [Term s PECPoint]
case1AdditionTest generator n =
    take n $
        map (pToPoint fieldModulus) $
            iterate (\prevPoint -> pAddPoints fieldModulus 0 prevPoint generator) generator
  where
    fieldModulus = mkPPositive 11
