module Grumplestiltskin.Prover (runTest) where

import Cardano.Crypto.EllipticCurve.BLS12_381
import Data.Poly
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Debug.Trace (trace, traceM)
import Grumplestiltskin.Verify
import Plutarch.Builtin.BLS (PBuiltinBLS12_381_G1_Element, PBuiltinBLS12_381_G2_Element (PBuiltinBLS12_381_G2_Element), pbls12_381_G1_uncompress, pbls12_381_G2_uncompress)
import Plutarch.Internal.Term (Config (NoTracing))
import Plutarch.Prelude (PBool, PInteger, S, Term, pconstant, (#))
import Plutarch.Test.Unit (TermResult (Evaluated, FailedToCompile, FailedToEvaluate), evalTermResult)
import Test.QuickCheck
import Test.Tasty (defaultMain)
import Test.Tasty.QuickCheck (testProperty)

-- the size limit for a generated polynomial. We might as well hard-code it since
-- it shouldn't ever need to change.
maxPoly :: Int
maxPoly = 20

-- inclusive
between :: (Ord a) => a -> a -> a -> Bool
between lo hi x = x >= lo && x <= hi

instance Arbitrary (Poly Vector Integer) where
    arbitrary = do
        -- i swear there's a better way to do this, I just can't find it now -_-
        len <- chooseInt (5, maxPoly)
        toPoly . Vector.fromList <$> vectorOf len (arbitrary @Integer `suchThat` (/= 0))

{- Prover needs to construct:
  - P(tau) | G_1
  - P(r)
  - Q(tau) | G_1

-}

data TrustedSetup
    = TrustedSetup
    { tauScaledG1 :: Vector (Point Curve1)
    , tauScaledG2 :: Point Curve2
    , g2 :: Point Curve2
    }

instance Arbitrary TrustedSetup where
    arbitrary = do
        let g1 = blsGenerator @Curve1
            g2 = blsGenerator @Curve2
        tau <- arbitrary @Integer `suchThat` (\x -> x < (-1) || x > 1)
        let taus = Vector.fromList $ map (\e -> blsMult g1 (tau ^ e)) [0 .. 20]
        pure $ TrustedSetup taus (blsMult g2 tau) g2

-- This returns a commitment to P
commitToP :: TrustedSetup -> Poly Vector Integer -> Point Curve1
commitToP (TrustedSetup taus tauXG2 g2) poly =
    trace msg $
        Vector.foldr1 blsAddOrDouble $
            Vector.zipWith (\cX tauX -> blsMult tauX cX) coefficients taus
  where
    msg =
        "\nCommit to P:\n P: "
            <> show (unPoly poly)
            <> "\n Tau Len: "
            <> show (Vector.length taus)
    coefficients = unPoly poly

commitToQ :: TrustedSetup -> Poly Vector Integer -> Integer -> Point Curve1 -> Point Curve1
commitToQ (TrustedSetup taus tauXG2 g2) poly r pTau =
    trace msg $
        blsAddOrDouble pTau (blsNeg $ blsMult g1 e_r)
  where
    msg =
        "Commit to Q:\n P: "
            <> show (unPoly poly)
            <> "\n Tau Len: "
            <> show (Vector.length taus)
    g1 = Vector.head taus
    e_r = eval poly r

liftPoint1 :: forall (s :: S). Point Curve1 -> Term s PBuiltinBLS12_381_G1_Element
liftPoint1 p = pbls12_381_G1_uncompress # pconstant (blsCompress p)

liftPoint2 :: forall (s :: S). Point Curve2 -> Term s PBuiltinBLS12_381_G2_Element
liftPoint2 p = pbls12_381_G2_uncompress # pconstant (blsCompress p)

runTest = defaultMain verifyTest

verifyTest = testProperty "verification" testVerify

testVerify :: Property
testVerify = forAllBlind @Bool (arbitrary @(TrustedSetup, Poly Vector Integer, Integer)) $
    \(setup@(TrustedSetup taus tauXG2 g2), poly, r) -> do
        trace ("verify: tau len: " <> show (Vector.length taus)) $
            let pTau = commitToP setup poly
                qTau = commitToQ setup poly r pTau
                -- lifted, for the plutarch verifier
                g1' :: forall s. Term s PBuiltinBLS12_381_G1_Element
                g1' = liftPoint1 $ Vector.head taus
                tauXG2' :: forall s. Term s PBuiltinBLS12_381_G2_Element
                tauXG2' = liftPoint2 tauXG2
                g2' :: forall s. Term s PBuiltinBLS12_381_G2_Element
                g2' = liftPoint2 g2
                pTau' :: forall s. Term s PBuiltinBLS12_381_G1_Element
                pTau' = liftPoint1 pTau
                r' :: forall (s :: S). Term s PInteger
                r' = pconstant r
                pR' :: forall (s :: S). Term s PInteger
                pR' = pconstant $ eval poly r
                qTau' :: forall (s :: S). Term s PBuiltinBLS12_381_G1_Element
                qTau' = liftPoint1 qTau
                verified :: forall (s :: S). Term s PBool
                verified = verify # g1' # tauXG2' # g2' # pTau' # r' # pR' # qTau'
             in case evalTermResult NoTracing verified of
                    FailedToCompile txt -> trace ("Failed to compile: " <> T.unpack txt) $ False
                    FailedToEvaluate err logs -> trace ("Failed to evaluate: " <> show err) $ False
                    Evaluated a b ->
                        -- TODO: better way to do this?
                        a == "program 1.1.0 True"
