module Main (main) where

import Control.Monad (guard)
import GHC.IO.Encoding (setLocaleEncoding, utf8)
import Grumplestiltskin.Galois (
    PGFElement,
    PGFElementData,
    pgfExp,
    pgfFromElem,
    pgfOne,
    pgfRecip,
    pgfToData,
    pgfToElem,
    pgfZero,
 )
import Numeric.Natural (Natural)
import Plutarch.Prelude (
    PAsData,
    PBool,
    PInteger,
    PNatural,
    PPositive,
    S,
    Term,
    pconstant,
    pdata,
    pforgetData,
    plam,
    plift,
    pnegate,
    ppowNatural,
    ppowPositive,
    ptryFrom,
    pupcast,
    tcont,
    unTermCont,
    (#),
    (#*),
    (#+),
    (#-),
    (#==),
 )
import Plutarch.Test.Utils (precompileTerm)
import Plutarch.Unsafe (punsafeCoerce)
import Test.QuickCheck (
    Gen,
    Property,
    arbitrary,
    chooseInt,
    forAll,
    forAllShrink,
    shrink,
 )
import Test.QuickCheck.Instances.Natural ()
import Test.Tasty (adjustOption, defaultMain, testGroup)
import Test.Tasty.QuickCheck (QuickCheckTests, testProperty)

main :: IO ()
main = do
    -- Pre-emptively avoid locale encoding issues
    setLocaleEncoding utf8
    defaultMain . adjustOption moreTests . testGroup "Tests" $
        [ testGroup
            "PGFIntermediate"
            [ testProperty "#+ commutes" propCommAdd
            , testProperty "#+ associates" propAssocAdd
            , testProperty "zero element is an identity for #+" propZeroAdd
            , testProperty "pnegate produces an additive inverse" propNegate
            , testProperty "#* commutes" propCommMul
            , testProperty "#* associates" propAssocMul
            , testProperty "one element is an identity for #*" propOneMul
            , testProperty "pgfRecip produces a reciprocal" propRecip
            , testProperty "distributivity of #+ over #*" propDistribute
            , testProperty "pgfExp equivalent to ppowPositive" propExpPos
            , testProperty "pgfExp equivalent to ppowNatural" propExpNat
            , testProperty "x ^ n * x ^ -n = 1 for nonzero x" propExpRing
            ]
        , testGroup
            "Encoding for PGFElementData"
            [ testProperty "PTryFrom" propPTF
            ]
        ]
  where
    moreTests :: QuickCheckTests -> QuickCheckTests
    moreTests = max 1_000

-- Properties

propPTF :: Property
propPTF = forAll arbitrary $ \x ->
    plift (precompileTerm (plam go) # pconstant x)
  where
    go :: forall (s :: S). Term s PGFElement -> Term s PBool
    go t =
        let asData = pforgetData . pdata . pgfToData t $ pbase
            lhs = unTermCont $ do
                (x, _) <- tcont (ptryFrom @(PAsData PGFElementData) asData)
                pure . pforgetData $ x
         in lhs #== asData

propCommAdd :: Property
propCommAdd = forAll arbitrary $ \(x, y) ->
    plift (precompileTerm (plam go) # pconstant x # pconstant y)
  where
    go :: forall (s :: S). Term s PGFElement -> Term s PGFElement -> Term s PBool
    go t1 t2 =
        let lhs = pgfFromElem t1 #+ pgfFromElem t2
            rhs = pgfFromElem t2 #+ pgfFromElem t1
         in pgfToElem lhs pbase #== pgfToElem rhs pbase

propAssocAdd :: Property
propAssocAdd = forAll arbitrary $ \(x, y, z) ->
    plift (precompileTerm (plam go) # pconstant x # pconstant y # pconstant z)
  where
    go ::
        forall (s :: S).
        Term s PGFElement ->
        Term s PGFElement ->
        Term s PGFElement ->
        Term s PBool
    go t1 t2 t3 =
        let lhs = pgfFromElem t1 #+ (pgfFromElem t2 #+ pgfFromElem t3)
            rhs = (pgfFromElem t1 #+ pgfFromElem t2) #+ pgfFromElem t3
         in pgfToElem lhs pbase #== pgfToElem rhs pbase

propZeroAdd :: Property
propZeroAdd = forAll arbitrary $ \x ->
    plift (precompileTerm (plam go) # pconstant x)
  where
    go :: forall (s :: S). Term s PGFElement -> Term s PBool
    go t =
        let lhs = pgfFromElem t #+ pgfFromElem pgfZero
         in pgfToElem lhs pbase #== t

propNegate :: Property
propNegate = forAll arbitrary $ \x ->
    plift (precompileTerm (plam go) # pconstant x)
  where
    go ::
        forall (s :: S).
        Term s PGFElement ->
        Term s PBool
    go t = pgfToElem (pgfFromElem t #- pgfFromElem t) pbase #== pgfZero

propCommMul :: Property
propCommMul = forAll arbitrary $ \(x, y) ->
    plift (precompileTerm (plam go) # pconstant x # pconstant y)
  where
    go ::
        forall (s :: S).
        Term s PGFElement ->
        Term s PGFElement ->
        Term s PBool
    go t1 t2 =
        let lhs = pgfFromElem t1 #* pgfFromElem t2
            rhs = pgfFromElem t2 #* pgfFromElem t1
         in pgfToElem lhs pbase #== pgfToElem rhs pbase

propAssocMul :: Property
propAssocMul = forAll arbitrary $ \(x, y, z) ->
    plift (precompileTerm (plam go) # pconstant x # pconstant y # pconstant z)
  where
    go ::
        forall (s :: S).
        Term s PGFElement ->
        Term s PGFElement ->
        Term s PGFElement ->
        Term s PBool
    go t1 t2 t3 =
        let lhs = pgfFromElem t1 #* (pgfFromElem t2 #* pgfFromElem t3)
            rhs = (pgfFromElem t1 #* pgfFromElem t2) #* pgfFromElem t3
         in pgfToElem lhs pbase #== pgfToElem rhs pbase

propOneMul :: Property
propOneMul = forAll arbitrary $ \x ->
    plift (precompileTerm (plam go) # pconstant x)
  where
    go :: forall (s :: S). Term s PGFElement -> Term s PBool
    go t =
        let lhs = pgfFromElem t #* pgfFromElem pgfOne
         in pgfToElem lhs pbase #== t

-- Note (Koz, 14/08/2025): To ensure that we don't accidentally generate
-- nonsensical values for reciprocals, we generate a Natural in a given range,
-- then promote it.
propRecip :: Property
propRecip = forAllShrink gen shr $ \n ->
    plift (precompileTerm (plam go) # pconstant n)
  where
    gen :: Gen Natural
    gen = fromIntegral <$> chooseInt (1, 96)
    shr :: Natural -> [Natural]
    shr n = do
        n' <- shrink n
        guard (n' >= 1)
        pure n'
    go :: forall (s :: S). Term s PNatural -> Term s PBool
    go t =
        let t' = pgfFromElem $ punsafeCoerce t
         in pgfToElem (t' #* pgfFromElem (pgfRecip # t' # pbase)) pbase #== pgfOne

propDistribute :: Property
propDistribute = forAll arbitrary $ \(x, y, z) ->
    plift (precompileTerm (plam go) # pconstant x # pconstant y # pconstant z)
  where
    go ::
        forall (s :: S).
        Term s PGFElement ->
        Term s PGFElement ->
        Term s PGFElement ->
        Term s PBool
    go t1 t2 t3 =
        let lhs = pgfFromElem t1 #* (pgfFromElem t2 #+ pgfFromElem t3)
            rhs = (pgfFromElem t1 #* pgfFromElem t2) #+ (pgfFromElem t1 #* pgfFromElem t3)
         in pgfToElem lhs pbase #== pgfToElem rhs pbase

propExpPos :: Property
propExpPos = forAll arbitrary $ \(x, p) ->
    plift (precompileTerm (plam go) # pconstant x # pconstant p)
  where
    go ::
        forall (s :: S).
        Term s PGFElement ->
        Term s PPositive ->
        Term s PBool
    go tBase tExp =
        let lhs = ppowPositive (pgfFromElem tBase) tExp
            rhs = pgfExp # pgfFromElem tBase # pupcast tExp # pbase
         in pgfToElem lhs pbase #== rhs

propExpNat :: Property
propExpNat = forAll arbitrary $ \(x, n) ->
    plift (precompileTerm (plam go) # pconstant x # pconstant n)
  where
    go ::
        forall (s :: S).
        Term s PGFElement ->
        Term s PNatural ->
        Term s PBool
    go tBase tExp =
        let lhs = ppowNatural (pgfFromElem tBase) tExp
            rhs = pgfExp # pgfFromElem tBase # pupcast tExp # pbase
         in pgfToElem lhs pbase #== rhs

-- Note (Koz, 14/08/2025): To ensure that we don't generate the zero element, we
-- generate a Natural in the right range, then promote it.
propExpRing :: Property
propExpRing = forAllShrink gen shr $ \(n, i) ->
    plift (precompileTerm (plam go) # pconstant n # pconstant i)
  where
    gen :: Gen (Natural, Integer)
    gen = ((,) . fromIntegral <$> chooseInt (1, 96)) <*> arbitrary
    shr :: (Natural, Integer) -> [(Natural, Integer)]
    shr (n, i) = do
        n' <- shrink n
        i' <- shrink i
        guard (n' >= 1)
        pure (n', i')
    go ::
        forall (s :: S).
        Term s PNatural ->
        Term s PInteger ->
        Term s PBool
    go n tExp =
        let tBase = punsafeCoerce n
            exp1 = pgfFromElem (pgfExp # pgfFromElem tBase # tExp # pbase)
            exp2 = pgfFromElem (pgfExp # pgfFromElem tBase # (pnegate # tExp) # pbase)
         in pgfToElem (exp1 #* exp2) pbase #== pgfOne

-- Helpers

pbase :: forall (s :: S). Term s PPositive
pbase = punsafeCoerce (97 :: Term s PInteger)
