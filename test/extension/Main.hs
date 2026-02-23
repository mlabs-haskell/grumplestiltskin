module Main (main) where

import Control.Monad (guard)
import GHC.IO.Encoding (setLocaleEncoding, utf8)
import Grumplestiltskin.Degree2 (
    D2Element,
    PD2Element,
    PD2Intermediate,
    fromD2Element,
    mkD2Element,
    pd2Divide,
    pd2FromElem,
    pd2I,
    pd2One,
    pd2Square,
    pd2ToElem,
    pd2Zero,
 )
import Numeric.Natural (Natural)
import Plutarch.Evaluate (evalTerm')
import Plutarch.Internal.Term (Config (NoTracing))
import Plutarch.Prelude (
    PBool,
    PInteger,
    PPositive,
    S,
    Term,
    pconstant,
    plam,
    plift,
    pnegate,
    pone,
    pscaleInteger,
    pscaleNatural,
    pscalePositive,
    pzero,
    (#),
    (#*),
    (#+),
    (#-),
    (#==),
 )
import Plutarch.Test.Golden (goldenEval, plutarchGolden)
import Plutarch.Test.Unit (testEval)
import Plutarch.Test.Utils (precompileTerm)
import Plutarch.Unsafe (punsafeCoerce)
import Test.QuickCheck (
    Arbitrary (arbitrary, shrink),
    NonNegative (NonNegative),
    Positive (Positive),
    Property,
    chooseInt,
    forAll,
 )
import Test.Tasty (adjustOption, defaultMain, testGroup)
import Test.Tasty.QuickCheck (QuickCheckTests, testProperty)

main :: IO ()
main = do
    -- Pre-emptively avoid locale encoding issues
    setLocaleEncoding utf8
    defaultMain . adjustOption moreTests . testGroup "Tests" $
        [ testGroup
            "PD2Intermediate"
            [ testProperty "#+ commutes" propCommAdd
            , testProperty "#+ associates" propAssocAdd
            , testProperty "zero element is an identity for #+" propZeroAdd
            , testProperty "pnegate produces an additive inverse" propNegate
            , testProperty "#* commutes" propCommMul
            , testProperty "#* associates" propAssocMul
            , testProperty "one element is an identity for #*" propOneMul
            , testProperty "distributivity of #+ over #*" propDistribute
            , testProperty "pd2Square x = x #* x" propSquare
            , testEval "pd2Square pd2I = -1" iAssertion
            , testProperty "pd2Divide x pd2One = x" propOneDivide
            , testProperty "pscalePositive x n #+ pscalePositive x m = pscalePositive x (n #+ m)" propScalePosAdd
            , testProperty "pscalePositive x pone = x" propScalePosOne
            , testProperty "pscalePositive (pscalePositive x n) m = pscalePositive x (n #* m)" propScalePosMul
            , testProperty "pscalePositive x n = pscaleNatural x (pupcast n)" propScalePosNatAgree
            , testProperty "pscaleNatural x pzero = pzero" propScaleNatZero
            , testProperty "pscaleNatural x n = pscaleInteger x (pupcast n)" propScaleNatIntAgree
            --          testProperty "pd2Divide is an inverse for nonzero elements" propDivideInv
            ]
        , plutarchGolden
            "Goldens"
            "extension"
            [ goldenEval "pd2Zero" pd2Zero
            , goldenEval "pd2One" pd2One
            , goldenEval "pd2I" pd2I
            , goldenEval "plus" (psampleInt #+ psampleIntSquared)
            , goldenEval "pscalePositive" (pscalePositive psampleInt (punsafeCoerce @_ @PInteger 700))
            , goldenEval "pscaleNatural" (pscalePositive psampleInt (punsafeCoerce @_ @PInteger 700))
            , goldenEval "pscaleInteger positive" (pscaleInteger psampleInt 700)
            , goldenEval "pd2Square" (pd2Square psampleInt)
            ]
        ]
  where
    moreTests :: QuickCheckTests -> QuickCheckTests
    moreTests = max 100_000
    iAssertion :: forall (s :: S). Term s PBool
    iAssertion =
        pd2ToElem (pd2Square (pd2FromElem pd2I)) pbase
            #== pd2ToElem (pnegate # pd2FromElem pd2One) pbase

-- Properties

propScaleNatIntAgree :: Property
propScaleNatIntAgree = forAll arbitrary $ \(x, NonNegative n) ->
    plift (precompileTerm (plam go) # pconstant x # pconstant n)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PInteger ->
        Term s PBool
    go x n =
        let asIntermediate = pd2FromElem x
            nNat = punsafeCoerce n
            lhs = pscaleNatural asIntermediate nNat
            rhs = pscaleInteger asIntermediate n
         in pd2ToElem lhs pbase #== pd2ToElem rhs pbase

propScaleNatZero :: Property
propScaleNatZero = forAll arbitrary $ \x ->
    plift (precompileTerm (plam go) # pconstant x)
  where
    go :: forall (s :: S). Term s PD2Element -> Term s PBool
    go x =
        let asIntermediate = pd2FromElem x
            lhs = pscaleNatural asIntermediate pzero
         in pd2ToElem lhs pbase #== pd2Zero

propScalePosNatAgree :: Property
propScalePosNatAgree = forAll arbitrary $ \(x, Positive n) ->
    plift (precompileTerm (plam go) # pconstant x # pconstant n)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PInteger ->
        Term s PBool
    go x n =
        let asIntermediate = pd2FromElem x
            nPos = punsafeCoerce n
            nNat = punsafeCoerce n
            lhs = pscalePositive asIntermediate nPos
            rhs = pscaleNatural asIntermediate nNat
         in pd2ToElem lhs pbase #== pd2ToElem rhs pbase

propScalePosAdd :: Property
propScalePosAdd = forAll arbitrary $ \(x, Positive n, Positive m) ->
    plift (precompileTerm (plam go) # pconstant x # pconstant n # pconstant m)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PBool
    go x n m =
        let asIntermediate = pd2FromElem x
            n' = punsafeCoerce n
            m' = punsafeCoerce m
            lhs = pscalePositive asIntermediate n' #+ pscalePositive asIntermediate m'
            rhs = pscalePositive asIntermediate (n' #+ m')
         in pd2ToElem lhs pbase #== pd2ToElem rhs pbase

propScalePosOne :: Property
propScalePosOne = forAll arbitrary $ \x ->
    plift (precompileTerm (plam go) # pconstant x)
  where
    go :: forall (s :: S). Term s PD2Element -> Term s PBool
    go x =
        let asIntermediate = pd2FromElem x
            lhs = pscalePositive asIntermediate pone
         in pd2ToElem lhs pbase #== x

propScalePosMul :: Property
propScalePosMul = forAll arbitrary $ \(x, n, m) ->
    plift (precompileTerm (plam go) # pconstant x # pconstant n # pconstant m)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PBool
    go x n m =
        let asIntermediate = pd2FromElem x
            n' = punsafeCoerce n
            m' = punsafeCoerce m
            lhs = pscalePositive (pscalePositive asIntermediate n') m'
            rhs = pscalePositive asIntermediate (n' #* m')
         in pd2ToElem lhs pbase #== pd2ToElem rhs pbase

propOneDivide :: Property
propOneDivide = forAll arbitrary $ \x ->
    plift (precompileTerm (plam go) # pconstant x)
  where
    go :: forall (s :: S). Term s PD2Element -> Term s PBool
    go t =
        let asIntermediate = pd2FromElem t
            lhs = pd2Divide asIntermediate pone pbase
         in pd2ToElem lhs pbase #== t

{-
propDivideInv :: Property
propDivideInv = forAll arbitrary $ \(x, NZD2E y) ->
  plift (precompileTerm (plam go) # pconstant x # pconstant y)
  where
    go :: forall (s :: S) . Term s PD2Element -> Term s PD2Element -> Term s PBool
    go t1 t2 = let t1AsI = pd2FromElem t1
                   t2AsI = pd2FromElem t2
                   lhs = pd2Divide t1AsI t2AsI pbase
                   rhs = t1AsI #* pd2Divide pone t2AsI pbase
                 in pd2ToElem lhs pbase #== pd2ToElem rhs pbase
-}

propSquare :: Property
propSquare = forAll arbitrary $ \x ->
    plift (precompileTerm (plam go) # pconstant x)
  where
    go :: forall (s :: S). Term s PD2Element -> Term s PBool
    go t =
        let asIntermediate = pd2FromElem t
            lhs = pd2Square asIntermediate
            rhs = asIntermediate #* asIntermediate
         in pd2ToElem lhs pbase #== pd2ToElem rhs pbase

propCommAdd :: Property
propCommAdd = forAll arbitrary $ \(x, y) ->
    plift (precompileTerm (plam go) # pconstant x # pconstant y)
  where
    go :: forall (s :: S). Term s PD2Element -> Term s PD2Element -> Term s PBool
    go t1 t2 =
        let lhs = pd2FromElem t1 #+ pd2FromElem t2
            rhs = pd2FromElem t2 #+ pd2FromElem t1
         in pd2ToElem lhs pbase #== pd2ToElem rhs pbase

propAssocAdd :: Property
propAssocAdd = forAll arbitrary $ \(x, y, z) ->
    plift (precompileTerm (plam go) # pconstant x # pconstant y # pconstant z)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PBool
    go t1 t2 t3 =
        let lhs = pd2FromElem t1 #+ (pd2FromElem t2 #+ pd2FromElem t3)
            rhs = (pd2FromElem t1 #+ pd2FromElem t2) #+ pd2FromElem t3
         in pd2ToElem lhs pbase #== pd2ToElem rhs pbase

propZeroAdd :: Property
propZeroAdd = forAll arbitrary $ \x ->
    plift (precompileTerm (plam go) # pconstant x)
  where
    go :: forall (s :: S). Term s PD2Element -> Term s PBool
    go t =
        let lhs = pd2FromElem t #+ pzero
         in pd2ToElem lhs pbase #== t

propNegate :: Property
propNegate = forAll arbitrary $ \x ->
    plift (precompileTerm (plam go) # pconstant x)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PBool
    go t = pd2ToElem (pd2FromElem t #- pd2FromElem t) pbase #== pd2Zero

propCommMul :: Property
propCommMul = forAll arbitrary $ \(x, y) ->
    plift (precompileTerm (plam go) # pconstant x # pconstant y)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PBool
    go t1 t2 =
        let lhs = pd2FromElem t1 #* pd2FromElem t2
            rhs = pd2FromElem t2 #* pd2FromElem t1
         in pd2ToElem lhs pbase #== pd2ToElem rhs pbase

propAssocMul :: Property
propAssocMul = forAll arbitrary $ \(x, y, z) ->
    plift (precompileTerm (plam go) # pconstant x # pconstant y # pconstant z)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PBool
    go t1 t2 t3 =
        let lhs = pd2FromElem t1 #* (pd2FromElem t2 #* pd2FromElem t3)
            rhs = (pd2FromElem t1 #* pd2FromElem t2) #* pd2FromElem t3
         in pd2ToElem lhs pbase #== pd2ToElem rhs pbase

propOneMul :: Property
propOneMul = forAll arbitrary $ \x ->
    plift (precompileTerm (plam go) # pconstant x)
  where
    go :: forall (s :: S). Term s PD2Element -> Term s PBool
    go t =
        let lhs = pd2FromElem t #* pone
         in pd2ToElem lhs pbase #== t

propDistribute :: Property
propDistribute = forAll arbitrary $ \(x, y, z) ->
    plift (precompileTerm (plam go) # pconstant x # pconstant y # pconstant z)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PBool
    go t1 t2 t3 =
        let lhs = pd2FromElem t1 #* (pd2FromElem t2 #+ pd2FromElem t3)
            rhs = (pd2FromElem t1 #* pd2FromElem t2) #+ (pd2FromElem t1 #* pd2FromElem t3)
         in pd2ToElem lhs pbase #== pd2ToElem rhs pbase

-- Helpers

-- Needed for division properties, as we can't divide by zero
newtype NonZeroD2E = NZD2E D2Element
    deriving (Eq) via D2Element
    deriving stock (Show)

instance Arbitrary NonZeroD2E where
    arbitrary =
        NZD2E <$> do
            r <- fromIntegral <$> chooseInt (0, 96)
            i <- fromIntegral <$> if r == 0 then chooseInt (1, 96) else chooseInt (0, 96)
            pure $ mkD2Element r i 97
    shrink (NZD2E x) = do
        let (r, i) = fromD2Element x
        r' <- shrink r
        i' <- shrink i
        guard (r' > 0 || i' > 0)
        pure . NZD2E $ mkD2Element r' i' 97

pbase :: forall (s :: S). Term s PPositive
pbase = punsafeCoerce (97 :: Term s PInteger)

-- BLS12-381 G1 field order
const381 :: Natural
const381 = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787

{-
p381 :: forall (s :: S) . Term s PPositive
p381 = punsafeCoerce @_ @PInteger 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787
-}

-- 2^390
huge1 :: Natural
huge1 = 2521728396569246669585858566409191283525103313309788586748690777871726193375821479130513040312634601011624191379636224

{-
phuge1 :: forall (s :: S) . Term s PNatural
phuge1 = punsafeCoerce @_ @PInteger 2521728396569246669585858566409191283525103313309788586748690777871726193375821479130513040312634601011624191379636224
-}

-- 2^392
huge2 :: Natural
huge2 = 10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896

{-
phuge2 :: forall (s :: S) . Term s PNatural
phuge2 = punsafeCoerce @_ @PInteger 10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896
-}

psample :: forall (s :: S). Term s PD2Element
psample = pconstant $ mkD2Element huge1 huge2 const381

psampleInt :: forall (s :: S). Term s PD2Intermediate
psampleInt = evalTerm' NoTracing (pd2FromElem psample)

psampleIntSquared :: forall (s :: S). Term s PD2Intermediate
psampleIntSquared = evalTerm' NoTracing (pd2Square psampleInt)
