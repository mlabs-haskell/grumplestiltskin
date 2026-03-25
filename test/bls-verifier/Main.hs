module Main (main) where

import Cardano.Crypto.EllipticCurve.BLS12_381 (
    Curve1,
    Curve2,
    Point,
    blsAddOrDouble,
    blsGenerator,
    blsMult,
    blsNeg,
 )
import Control.Monad (guard)
import Data.Poly (Poly, eval, toPoly, unPoly)
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import GHC.IO.Encoding (setLocaleEncoding, utf8)
import Grumplestiltskin.Verify (verify)
import Plutarch.Builtin.BLS (
    PBuiltinBLS12_381_G1_Element,
    PBuiltinBLS12_381_G2_Element,
 )
import Plutarch.Prelude (
    PBool,
    PInteger,
    S,
    Term,
    pconstant,
    plam,
    plift,
    (#),
 )
import Plutarch.Test.Utils (precompileTerm)
import PlutusCore.Crypto.BLS12_381.G1 qualified as G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as G2
import Test.QuickCheck (
    Arbitrary (arbitrary, shrink),
    NonZero (NonZero),
    Positive (Positive),
    Property,
    counterexample,
    forAllShrink,
    getNonZero,
    liftShrink,
 )
import Test.QuickCheck.Instances ()
import Test.Tasty (adjustOption, defaultMain, testGroup)
import Test.Tasty.QuickCheck (QuickCheckTests, testProperty)

main :: IO ()
main = do
    -- Pre-emptively avoid locale encoding issues
    setLocaleEncoding utf8
    defaultMain . adjustOption moreTests . testGroup "Tests" $
        [ testProperty "prover accepts valid commitments" propValid
        ]
  where
    moreTests :: QuickCheckTests -> QuickCheckTests
    moreTests = max 1_000

-- Properties

propValid :: Property
propValid = forAllShrink arbitrary shrink $ \(Tau tau, r, Polynomial p) ->
    let asVector = unPoly p
        len = Vector.length asVector
        trustedSetupTaus = Vector.generate len (\e -> blsMult g1 (tau ^ e))
        pCommitment@(G1.Element pCommitment') = G1.Element . Vector.foldl1' blsAddOrDouble . Vector.zipWith blsMult trustedSetupTaus $ asVector
        pAtR = eval p r
        qCommitment = G1.Element . blsAddOrDouble pCommitment' . blsNeg . blsMult g1 $ pAtR
        tauScaleG2 = G2.Element $ blsMult g2 tau
     in counterexample ("Commitment to P: " <> show pCommitment)
            . counterexample ("Commitment to Q: " <> show pCommitment)
            $ plift
                ( precompileTerm (plam go)
                    # pconstant pCommitment
                    # pconstant qCommitment
                    # pconstant pAtR
                    # pconstant tauScaleG2
                    # pconstant r
                )
  where
    go ::
        forall (s :: S).
        Term s PBuiltinBLS12_381_G1_Element ->
        Term s PBuiltinBLS12_381_G1_Element ->
        Term s PInteger ->
        Term s PBuiltinBLS12_381_G2_Element ->
        Term s PInteger ->
        Term s PBool
    go pCommitment qCommitment pAtR tauScaleG2 r =
        verify # pG1 # tauScaleG2 # pG2 # pCommitment # r # pAtR # qCommitment

-- Helpers

g1 :: Point Curve1
g1 = blsGenerator @Curve1

pG1 :: forall (s :: S). Term s PBuiltinBLS12_381_G1_Element
pG1 = pconstant . G1.Element $ g1

g2 :: Point Curve2
g2 = blsGenerator @Curve2

pG2 :: forall (s :: S). Term s PBuiltinBLS12_381_G2_Element
pG2 = pconstant . G2.Element $ g2

newtype Tau = Tau Integer
    deriving (Eq) via Integer
    deriving stock (Show)

instance Arbitrary Tau where
    arbitrary =
        Tau <$> do
            Positive i <- arbitrary
            coin <- arbitrary
            pure $
                if coin
                    then i + 1
                    else negate (i + 1)
    shrink (Tau i) =
        Tau <$> do
            i' <- shrink i
            guard (i' /= 0)
            guard (i' /= (-1))
            guard (i' /= 1)
            pure i'

newtype Polynomial = Polynomial (Poly Vector Integer)
    deriving (Eq) via (Poly Vector Integer)

instance Show Polynomial where
    show (Polynomial p) = Vector.ifoldl' go "" . unPoly $ p
      where
        go :: String -> Int -> Integer -> String
        go acc ix c = show c <> "x^" <> show ix <> " + " <> acc

instance Arbitrary Polynomial where
    arbitrary =
        Polynomial . toPoly <$> do
            Positive len <- arbitrary
            Vector.replicateM len (getNonZero <$> arbitrary)
    shrink (Polynomial p) =
        Polynomial . toPoly <$> do
            let asVector = unPoly p
            shrunk <- liftShrink (fmap getNonZero . shrink . NonZero) asVector
            guard (Vector.length shrunk > 0)
            pure shrunk
