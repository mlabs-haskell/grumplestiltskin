module Main (main) where

import GHC.IO.Encoding (setLocaleEncoding, utf8)
import Grumplestiltskin.EllipticCurve (PECIntermediatePoint (PECIntermediatePoint), PECPoint, pAddPoints, pToPoint)
import Grumplestiltskin.Galois (PGFElement)
import Plutarch.Builtin.Integer (PInteger)
import Plutarch.Internal.Term (Term, punsafeCoerce)
import Plutarch.Pair (PPair (PPair))
import Plutarch.Prelude (PPositive, PString, pcon, plift, pmatch, pshow, pupcast)
import Plutarch.Test.Utils (precompileTerm)
import Test.QuickCheck.Instances.Natural ()
import Test.Tasty (adjustOption, defaultMain, testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)
import Test.Tasty.QuickCheck (QuickCheckTests)
import Unsafe.Coerce (unsafeCoerce)

showPoint :: Term s PECPoint -> Term s PString
showPoint p =
    pshow @(PPair PInteger PInteger) $
        pmatch
            (pupcast p)
            (\(PPair (x :: Term s PGFElement) (y :: Term s PGFElement)) -> pcon $ PPair (unsafeCoerce x) (unsafeCoerce y))

createPoint :: Term s PInteger -> Term s PInteger -> Term s PECIntermediatePoint
createPoint x y = pcon $ PECIntermediatePoint $ pcon $ PPair (unsafeCoerce x) (unsafeCoerce y)

main :: IO ()
main = do
    -- Pre-emptively avoid locale encoding issues
    setLocaleEncoding utf8
    defaultMain . adjustOption moreTests . testGroup "Elliptic curve tests" $
        [ testCase
            "PGFIntermediate"
            ( assertEqual
                "Problem"
                ( plift $
                    precompileTerm $
                        showPoint $
                            pToPoint pointAddTest fieldModulus
                )
                ""
            )
            -- ( assertBool "Expected correct point" $
            --     plift $
            --         precompileTerm $
            --             pToPoint pointAddTest fieldModulus #== pToPoint (createPoint 7 7) fieldModulus
            -- )
        ]
  where
    moreTests :: QuickCheckTests -> QuickCheckTests
    moreTests = max 1_000

    generatorPoint = createPoint 4 10

    fieldModulus :: Term s PPositive
    fieldModulus = punsafeCoerce (11 :: Term s PInteger)

    pointAddTest = pAddPoints fieldModulus generatorPoint generatorPoint
