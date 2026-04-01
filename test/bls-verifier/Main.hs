{-# LANGUAGE PatternSynonyms #-}

module Main (main) where

import Cardano.Crypto.EllipticCurve.BLS12_381 (
    BLS,
    Curve1,
    Curve2,
    Point,
    blsAddOrDouble,
    blsGenerator,
    blsMult,
 )
import Control.Monad (guard)
import Data.Euclidean qualified as Euclid
import Data.Maybe (fromJust)
import Data.Poly (Poly, eval, monomial, toPoly, unPoly, pattern X)
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
import Test.Tasty.QuickCheck (QuickCheckTests, suchThat, testProperty)

main :: IO ()
main = do
    -- Pre-emptively avoid locale encoding issues
    setLocaleEncoding utf8
    defaultMain . adjustOption moreTests . testGroup "Tests" $
        [ testProperty "prover accepts valid commitments" propValid
        ]
  where
    -- TODO: Lower this after constraints on P/R values known
    --       (lots of cases help with determining those constraints)
    moreTests :: QuickCheckTests -> QuickCheckTests
    moreTests = max 10_000

-- Properties
propValid :: Property
propValid = forAllShrink arbitrary shrink $ \(Tau tau, R r, Polynomial p) ->
    let asVector = unPoly p
        len = Vector.length asVector
        trustedSetupTaus = Vector.generate len (\e -> blsMult g1 (tau ^ e))
        pCommitment = commit p trustedSetupTaus
        pAtR = eval p r
        qX = fromJust $ (p - constPoly pAtR) `Euclid.divide` (X - constPoly r)
        qCommitment = commit qX trustedSetupTaus
        tauScaleG2 = G2.Element $ blsMult g2 tau
     in counterexample ("P(x) = " <> show (Polynomial p) <> ",  " <> show (unPoly p))
            . counterexample ("r = " <> show r)
            . counterexample ("P(r) = " <> show (Polynomial (constPoly pAtR)) <> ",  " <> show (unPoly (constPoly pAtR)))
            . counterexample ("Commitment to P: " <> show pCommitment)
            . counterexample ("Q(x) numerator: " <> show (Polynomial (p - monomial 1 pAtR)))
            . counterexample ("Q(x) denominator: " <> show (Polynomial (toPoly (Vector.fromList [1, negate r]))))
            . counterexample ("Q(x) = " <> show qX <> ",  " <> show (unPoly qX))
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

-- easier to read than 'blsMult'
(#*) :: (BLS curve) => Point curve -> Integer -> Point curve
a #* b = blsMult a b

-- easier to read than 'blsAddOrDouble'
(#+) :: (BLS curve) => Point curve -> Point curve -> Point curve
a #+ b = blsAddOrDouble a b

-- Helper for constructing commitments. Takes a polynomial and a vector of curve points and
-- calculates the sum of scaling each curve point by the coefficient of the polynomial.
commit :: Poly Vector Integer -> Vector (Point Curve1) -> G1.Element
commit poly taus = G1.Element . Vector.foldl1' (#+) . Vector.zipWith (#*) taus $ unPoly poly

-- "lifts" an Integer into a constant polynomial
-- e.g. `constPoly 5 = 5x^0`
constPoly :: Integer -> Poly Vector Integer
constPoly i = toPoly (Vector.fromList [i])

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
                    then i + 100
                    else negate (i + 100)
    shrink (Tau i) =
        Tau <$> do
            i' <- shrink i
            guard (abs i' > 100)
            pure i'

newtype R = R Integer
    deriving (Eq) via Integer
    deriving stock (Show)

-- If I'm right, R can actually be anything at all, but there are some (sensible) restrictions on P
instance Arbitrary R where
    arbitrary = R <$> arbitrary

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
            Vector.replicateM (len + 1) (arbitrary @Integer `suchThat` (/= 0))

    -- Vector.replicateM (len) (arbitrary @Integer `suchThat` (\x -> x < (-1) || x > 1))
    shrink (Polynomial p) =
        Polynomial . toPoly <$> do
            let asVector = unPoly p
            shrunk <- liftShrink (fmap getNonZero . shrink . NonZero) asVector
            guard (Vector.length shrunk > 0)
            pure shrunk
