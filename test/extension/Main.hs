module Main (main) where

import Data.Proxy (Proxy (Proxy))
import Data.Vector.Sized qualified as Vector
import GHC.IO.Encoding (setLocaleEncoding, utf8)
import GenD2 (
    GenD2Elements (GenD2Elements),
    GenD2NZElements (GenD2NZElements),
 )
import Grumplestiltskin.Degree2.Element (
    PD2Element,
    mkD2Element,
    pd2One,
    pd2Zero,
 )
import Grumplestiltskin.Degree2.Galois (
    PD2Intermediate,
    pd2Divide,
    pd2FromElem,
    pd2Pow,
    pd2Square,
    pd2ToElem,
 )
import Grumplestiltskin.Degree2.GaloisDirect qualified as Direct
import Numeric.Natural (Natural)
import Plutarch.Builtin.Integer (pexpModInteger)
import Plutarch.Evaluate (evalTerm')
import Plutarch.Internal.Term (Config (NoTracing))
import Plutarch.Prelude (
    PBool,
    PInteger,
    PNatural,
    PPositive,
    S,
    Term,
    pconstant,
    plam,
    plet,
    plift,
    pnegate,
    pone,
    ppowNatural,
    ppowPositive,
    pscaleInteger,
    pscaleNatural,
    pscalePositive,
    pzero,
    (#),
    (#&&),
    (#*),
    (#+),
    (#-),
    (#==),
 )
import Plutarch.Test.Golden (goldenEval, plutarchGolden)
import Plutarch.Test.Utils (precompileTerm)
import Plutarch.Unsafe (punsafeCoerce)
import Test.QuickCheck (
    Arbitrary (arbitrary),
    NonNegative (NonNegative),
    Positive (Positive),
    Property,
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
            "PD2Intermediate (indirect)"
            [ testProperty "#+ commutes" propCommAdd
            , testProperty "#+ associates" propAssocAdd
            , testProperty "zero element is an identity for #+" propZeroAdd
            , testProperty "pnegate produces an additive inverse" propNegate
            , testProperty "#* commutes" propCommMul
            , testProperty "#* associates" propAssocMul
            , testProperty "one element is an identity for #*" propOneMul
            , testProperty "distributivity of #+ over #*" propDistribute
            , testProperty "pd2Square x = x #* x" propSquare
            , testProperty "pd2Divide x pd2One = x" propOneDivide
            , testProperty "pscalePositive x n #+ pscalePositive x m = pscalePositive x (n #+ m)" propScalePosAdd
            , testProperty "pscalePositive x pone = x" propScalePosOne
            , testProperty "pscalePositive (pscalePositive x n) m = pscalePositive x (n #* m)" propScalePosMul
            , testProperty "pscalePositive x n = pscaleNatural x (pupcast n)" propScalePosNatAgree
            , testProperty "pscaleNatural x pzero = pzero" propScaleNatZero
            , testProperty "pscaleNatural x n = pscaleInteger x (pupcast n)" propScaleNatIntAgree
            , testProperty "pd2Divide x x = pone" propDivideSelf
            , testProperty "pd2Divide x pzero = pzero" propDivideZero
            , testProperty "pd2Divide x pone = x" propDivideOne
            , testProperty "pd2Divide (x #* y) y = (pd2Divide x y) #* y = x" propDivideInv
            , testProperty "ppowPositive x n #* ppowPositive x m = ppowPositive x (n #+ m)" propPowPosAdd
            , testProperty "ppowPositive (ppowPositive x n) m = ppowPositive x (n #* m)" propPowPosMul
            , testProperty "ppowPositive x 1 = x" propPowPosOne
            , testProperty "ppowNatural x n = pd2Pow x (pupcast n)" propPowNatIntAgree
            ]
        , testGroup
            "PD2Intermediate (direct)"
            [ testProperty "#+ commutes" propCommAdd'
            , testProperty "#+ associates" propAssocAdd'
            , testProperty "zero element is an identity for #+" propZeroAdd'
            , testProperty "pnegate produces an additive inverse" propNegate'
            , testProperty "pd2Times commutes" propCommMul'
            , testProperty "pd2Times associates" propAssocMul'
            , testProperty "one element is an identity for pd2Times" propOneMul'
            , testProperty "distributivity of #+ over pd2Times" propDistribute'
            , testProperty "pd2Square x = pd2Times x x" propSquare'
            , testProperty "pd2Divide x pd2OneI = x" propOneDivide'
            , testProperty "pscalePositive x n #+ pscalePositive x m = pscalePositive x (n #+ m)" propScalePosAdd'
            , testProperty "pscalePositive x pone = x" propScalePosOne'
            , testProperty "pscalePositive (pscalePositive x n) m = pscalePositive x (n #* m)" propScalePosMul'
            , testProperty "pd2Divide x x = pd2OneI" propDivideSelf'
            , testProperty "pd2Divide x pzero = pzero" propDivideZero'
            , testProperty "pd2Divide x pone = x" propDivideOne'
            , testProperty "pd2Divide (x #* y) y = (pd2Divide x y) #* y = x" propDivideInv'
            , testProperty "pd2Times (pd2Pow x n) (pd2Pow x m) = pd2Pow x (n #+ m)" propPowAdd
            , testProperty "pd2Pow (pd2Pow x n) m = pd2Pow x (n #* m)" propPowTimes
            , testProperty "pd2Pow x pzero = pd2OneI" propPowZero
            , testProperty "pd2Pow x pone = x" propPowOne
            , testProperty "pd2Pow x (pnegate n) = pd2Divide pd2OneI (pd2Pow x n)" propPowInv
            ]
        , plutarchGolden
            "Goldens"
            "extension"
            [ goldenEval "pd2Zero" pd2Zero
            , goldenEval "pd2One" pd2One
            , goldenEval "plus, indirect" (indirectResolve $ psampleInt #+ psampleIntSquared)
            , goldenEval "plus, direct" (directResolve $ psampleInt' #+ psampleIntSquared')
            , goldenEval "pscalePositive, indirect" (indirectResolve $ pscalePositive psampleInt (punsafeCoerce @_ @PInteger 700))
            , goldenEval "pscalePositive, direct" (directResolve $ pscalePositive psampleInt' (punsafeCoerce @_ @PInteger 700))
            , goldenEval "pscaleNatural, indirect" (indirectResolve $ pscaleNatural psampleInt (punsafeCoerce @_ @PInteger 700))
            , goldenEval "pscaleNatural, direct" (directResolve $ pscaleNatural psampleInt' (punsafeCoerce @_ @PInteger 700))
            , goldenEval "pscaleInteger positive, indirect" (indirectResolve $ pscaleInteger psampleInt 700)
            , goldenEval "pscaleInteger positive, direct" (directResolve $ pscaleInteger psampleInt' 700)
            , goldenEval "pscaleInteger negative, indirect" (indirectResolve $ pscaleInteger psampleInt (-700))
            , goldenEval "pscaleInteger negative, direct" (directResolve $ pscaleInteger psampleInt' (-700))
            , goldenEval "ppowPositive, indirect" (indirectResolve $ ppowPositive psampleInt (punsafeCoerce @_ @PInteger 70))
            , goldenEval "ppowPositive, direct" (directResolve $ Direct.pd2Pow pconst381 (punsafeCoerce psampleIrred) psampleInt' 70)
            , goldenEval "ppowNatural, indirect" (indirectResolve $ ppowNatural psampleInt (punsafeCoerce @_ @PInteger 70))
            , goldenEval "ppowNatural, direct" (directResolve $ Direct.pd2Pow pconst381 (punsafeCoerce psampleIrred) psampleInt' 70)
            , goldenEval "pd2Pow positive, indirect" (indirectResolve $ pd2Pow psampleInt 70)
            , goldenEval "pd2Pow positive, direct" (directResolve $ Direct.pd2Pow pconst381 (punsafeCoerce psampleIrred) psampleInt' 70)
            , goldenEval "pd2Pow negative, indirect" (indirectResolve $ pd2Pow psampleInt (-70))
            , goldenEval "pd2Pow negative, direct" (directResolve $ Direct.pd2Pow pconst381 (punsafeCoerce psampleIrred) psampleInt' (-70))
            , goldenEval "pd2Square, indirect" (indirectResolve $ pd2Square psampleInt)
            , goldenEval "pd2Square, direct" (directResolve $ Direct.pd2Square (punsafeCoerce psampleIrred) psampleInt')
            , goldenEval "pd2Divide, indirect" (indirectResolve $ pd2Divide psampleInt psampleInt2)
            , goldenEval "pd2Divide, direct" (directResolve $ Direct.pd2Divide pconst381 (punsafeCoerce psampleIrred) psampleInt' psampleInt2')
            ]
        ]
  where
    moreTests :: QuickCheckTests -> QuickCheckTests
    moreTests = max 100_000
    indirectResolve :: forall (s :: S). Term s PD2Intermediate -> Term s PD2Element
    indirectResolve = pd2ToElem psampleIrred pconst381
    directResolve :: forall (s :: S). Term s Direct.PD2Intermediate -> Term s PD2Element
    directResolve = Direct.pd2ToElem pconst381

-- Properties

propPowAdd :: Property
propPowAdd = forAll (arbitrary @(GenD2NZElements 0 1, _, _)) $ \(GenD2NZElements order irred _ els, n, m) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order # pconstant irred # pconstant n # pconstant m)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PBool
    go x order irred n m =
        let asIntermediate = Direct.pd2FromElem x
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
            lhs = Direct.pd2Times irred' (Direct.pd2Pow order' irred' asIntermediate n) (Direct.pd2Pow order' irred' asIntermediate m)
            rhs = Direct.pd2Pow order' irred' asIntermediate (n #+ m)
         in Direct.pd2ToElem order' lhs #== Direct.pd2ToElem order' rhs

propPowTimes :: Property
propPowTimes = forAll (arbitrary @(GenD2NZElements 0 1, _, _)) $ \(GenD2NZElements order irred _ els, n, m) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order # pconstant irred # pconstant n # pconstant m)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PBool
    go x order irred n m =
        let asIntermediate = Direct.pd2FromElem x
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
            lhs = Direct.pd2Pow order' irred' (Direct.pd2Pow order' irred' asIntermediate n) m
            rhs = Direct.pd2Pow order' irred' asIntermediate (n #* m)
         in Direct.pd2ToElem order' lhs #== Direct.pd2ToElem order' rhs

propPowZero :: Property
propPowZero = forAll (arbitrary @(GenD2Elements 1)) $ \(GenD2Elements order irred els) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order # pconstant irred)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PBool
    go x order irred =
        let asIntermediate = Direct.pd2FromElem x
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
            lhs = Direct.pd2Pow order' irred' asIntermediate pzero
         in Direct.pd2ToElem order' lhs #== pd2One

propPowOne :: Property
propPowOne = forAll (arbitrary @(GenD2Elements 1)) $ \(GenD2Elements order irred els) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order # pconstant irred)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PBool
    go x order irred =
        let asIntermediate = Direct.pd2FromElem x
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
            lhs = Direct.pd2Pow order' irred' asIntermediate pone
         in Direct.pd2ToElem order' lhs #== x

propPowInv :: Property
propPowInv = forAll (arbitrary @(GenD2NZElements 0 1, _)) $ \(GenD2NZElements order irred _ els, n) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order # pconstant irred # pconstant n)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PInteger ->
        Term s PBool
    go x order irred n =
        let asIntermediate = Direct.pd2FromElem x
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
            lhs = Direct.pd2Pow order' irred' asIntermediate (pnegate # n)
            rhs = Direct.pd2Divide order' irred' Direct.pd2OneI (Direct.pd2Pow order' irred' asIntermediate n)
         in Direct.pd2ToElem order' lhs #== Direct.pd2ToElem order' rhs

propDivideSelf :: Property
propDivideSelf = forAll (arbitrary @(GenD2NZElements 0 1)) $ \(GenD2NZElements order irred _ els) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order # pconstant irred)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PBool
    go t order irred =
        let asIntermediate = pd2FromElem t
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
            lhs = pd2Divide asIntermediate asIntermediate
         in pd2ToElem irred' order' lhs #== pd2One

propDivideSelf' :: Property
propDivideSelf' = forAll (arbitrary @(GenD2NZElements 0 1)) $ \(GenD2NZElements order irred _ els) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order # pconstant irred)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PBool
    go t order irred =
        let asIntermediate = Direct.pd2FromElem t
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
            lhs = Direct.pd2Divide order' irred' asIntermediate asIntermediate
         in Direct.pd2ToElem order' lhs #== pd2One

propDivideZero :: Property
propDivideZero = forAll (arbitrary @(GenD2NZElements 0 1)) $ \(GenD2NZElements order irred _ els) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order # pconstant irred)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PBool
    go t order irred =
        let asIntermediate = pd2FromElem t
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
            lhs = pd2Divide pzero asIntermediate
         in pd2ToElem irred' order' lhs #== pd2Zero

propDivideZero' :: Property
propDivideZero' = forAll (arbitrary @(GenD2NZElements 0 1)) $ \(GenD2NZElements order irred _ els) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order # pconstant irred)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PBool
    go t order irred =
        let asIntermediate = Direct.pd2FromElem t
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
            lhs = Direct.pd2Divide order' irred' pzero asIntermediate
         in Direct.pd2ToElem order' lhs #== pd2Zero

propDivideOne :: Property
propDivideOne = forAll (arbitrary @(GenD2NZElements 0 1)) $ \(GenD2NZElements order irred _ els) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order # pconstant irred)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PBool
    go t order irred =
        let asIntermediate = pd2FromElem t
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
            lhs = pd2Divide asIntermediate pone
         in pd2ToElem irred' order' lhs #== t

propDivideOne' :: Property
propDivideOne' = forAll (arbitrary @(GenD2NZElements 0 1)) $ \(GenD2NZElements order irred _ els) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order # pconstant irred)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PBool
    go t order irred =
        let asIntermediate = Direct.pd2FromElem t
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
            lhs = Direct.pd2Divide order' irred' asIntermediate Direct.pd2OneI
         in Direct.pd2ToElem order' lhs #== t

propDivideInv :: Property
propDivideInv = forAll (arbitrary @(GenD2NZElements 1 1)) $ \(GenD2NZElements order irred zs nzs) ->
    let x = Vector.index' zs (Proxy @0)
        y = Vector.index' nzs (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant y # pconstant order # pconstant irred)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PBool
    go x y order irred =
        let x' = pd2FromElem x
            y' = pd2FromElem y
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
            lhs = pd2Divide (x' #* y') y'
            rhs = pd2Divide x' y' #* y'
         in plet (pd2ToElem irred' order' lhs) $ \lhs' ->
                plet (pd2ToElem irred' order' rhs) $ \rhs' ->
                    (lhs' #== x) #&& (rhs' #== x)

propDivideInv' :: Property
propDivideInv' = forAll (arbitrary @(GenD2NZElements 1 1)) $ \(GenD2NZElements order irred zs nzs) ->
    let x = Vector.index' zs (Proxy @0)
        y = Vector.index' nzs (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant y # pconstant order # pconstant irred)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PBool
    go x y order irred =
        let x' = Direct.pd2FromElem x
            y' = Direct.pd2FromElem y
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
            lhs = Direct.pd2Divide order' irred' (Direct.pd2Times irred' x' y') y'
            rhs = Direct.pd2Times irred' (Direct.pd2Divide order' irred' x' y') y'
         in plet (Direct.pd2ToElem order' lhs) $ \lhs' ->
                plet (Direct.pd2ToElem order' rhs) $ \rhs' ->
                    (lhs' #== x) #&& (rhs' #== x)

propPowNatIntAgree :: Property
propPowNatIntAgree = forAll (arbitrary @(GenD2Elements 1, _)) $ \(GenD2Elements order irred els, NonNegative n) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order # pconstant irred # pconstant n)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PInteger ->
        Term s PBool
    go t order irred n =
        let asIntermediate = pd2FromElem t
            asNat = punsafeCoerce n
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
            lhs = ppowNatural asIntermediate asNat
            rhs = pd2Pow asIntermediate n
         in pd2ToElem irred' order' lhs #== pd2ToElem irred' order' rhs

propPowPosAdd :: Property
propPowPosAdd = forAll (arbitrary @(GenD2Elements 1, _, _)) $ \(GenD2Elements order irred els, Positive n, Positive m) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order # pconstant irred # pconstant n # pconstant m)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PBool
    go t order irred n m =
        let asIntermediate = pd2FromElem t
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
            n' = punsafeCoerce n
            m' = punsafeCoerce m
            lhs = ppowPositive asIntermediate n' #* ppowPositive asIntermediate m'
            rhs = ppowPositive asIntermediate (n' #+ m')
         in pd2ToElem irred' order' lhs #== pd2ToElem irred' order' rhs

propPowPosMul :: Property
propPowPosMul = forAll (arbitrary @(GenD2Elements 1, _, _)) $ \(GenD2Elements order irred els, Positive n, Positive m) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order # pconstant irred # pconstant n # pconstant m)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PBool
    go t order irred n m =
        let asIntermediate = pd2FromElem t
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
            n' = punsafeCoerce n
            m' = punsafeCoerce m
            lhs = ppowPositive (ppowPositive asIntermediate n') m'
            rhs = ppowPositive asIntermediate (n' #* m')
         in pd2ToElem irred' order' lhs #== pd2ToElem irred' order' rhs

propPowPosOne :: Property
propPowPosOne = forAll (arbitrary @(GenD2Elements 1)) $ \(GenD2Elements order irred els) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order # pconstant irred)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PBool
    go t order irred =
        let asIntermediate = pd2FromElem t
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
            lhs = ppowPositive asIntermediate pone
         in pd2ToElem irred' order' lhs #== t

propScaleNatIntAgree :: Property
propScaleNatIntAgree = forAll (arbitrary @(GenD2Elements 1, _)) $ \(GenD2Elements order irred els, NonNegative n) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order # pconstant irred # pconstant n)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PInteger ->
        Term s PBool
    go x order irred n =
        let asIntermediate = pd2FromElem x
            nNat = punsafeCoerce n
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
            lhs = pscaleNatural asIntermediate nNat
            rhs = pscaleInteger asIntermediate n
         in pd2ToElem irred' order' lhs #== pd2ToElem irred' order' rhs

propScaleNatZero :: Property
propScaleNatZero = forAll (arbitrary @(GenD2Elements 1)) $ \(GenD2Elements order irred els) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order # pconstant irred)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PBool
    go x order irred =
        let asIntermediate = pd2FromElem x
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
            lhs = pscaleNatural asIntermediate pzero
         in pd2ToElem irred' order' lhs #== pd2Zero

propScalePosNatAgree :: Property
propScalePosNatAgree = forAll (arbitrary @(GenD2Elements 1, _)) $ \(GenD2Elements order irred els, Positive n) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order # pconstant irred # pconstant n)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PInteger ->
        Term s PBool
    go x order irred n =
        let asIntermediate = pd2FromElem x
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
            nPos = punsafeCoerce n
            nNat = punsafeCoerce n
            lhs = pscalePositive asIntermediate nPos
            rhs = pscaleNatural asIntermediate nNat
         in pd2ToElem irred' order' lhs #== pd2ToElem irred' order' rhs

propScalePosAdd :: Property
propScalePosAdd = forAll (arbitrary @(GenD2Elements 1, _, _)) $ \(GenD2Elements order irred els, Positive n, Positive m) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order # pconstant irred # pconstant n # pconstant m)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PBool
    go x order irred n m =
        let asIntermediate = pd2FromElem x
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
            n' = punsafeCoerce n
            m' = punsafeCoerce m
            lhs = pscalePositive asIntermediate n' #+ pscalePositive asIntermediate m'
            rhs = pscalePositive asIntermediate (n' #+ m')
         in pd2ToElem irred' order' lhs #== pd2ToElem irred' order' rhs

propScalePosAdd' :: Property
propScalePosAdd' = forAll (arbitrary @(GenD2Elements 1, _, _)) $ \(GenD2Elements order _ els, Positive n, Positive m) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order # pconstant n # pconstant m)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PBool
    go x order n m =
        let asIntermediate = Direct.pd2FromElem x
            order' = punsafeCoerce order
            n' = punsafeCoerce n
            m' = punsafeCoerce m
            lhs = pscalePositive asIntermediate n' #+ pscalePositive asIntermediate m'
            rhs = pscalePositive asIntermediate (n' #+ m')
         in Direct.pd2ToElem order' lhs #== Direct.pd2ToElem order' rhs

propScalePosOne :: Property
propScalePosOne = forAll (arbitrary @(GenD2Elements 1)) $ \(GenD2Elements order irred els) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order # pconstant irred)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PBool
    go x order irred =
        let asIntermediate = pd2FromElem x
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
            lhs = pscalePositive asIntermediate pone
         in pd2ToElem irred' order' lhs #== x

propScalePosOne' :: Property
propScalePosOne' = forAll (arbitrary @(GenD2Elements 1)) $ \(GenD2Elements order _ els) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PBool
    go x order =
        let asIntermediate = Direct.pd2FromElem x
            order' = punsafeCoerce order
            lhs = pscalePositive asIntermediate pone
         in Direct.pd2ToElem order' lhs #== x

propScalePosMul :: Property
propScalePosMul = forAll (arbitrary @(GenD2Elements 1, _, _)) $ \(GenD2Elements order irred els, n, m) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order # pconstant irred # pconstant n # pconstant m)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PBool
    go x order irred n m =
        let asIntermediate = pd2FromElem x
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
            n' = punsafeCoerce n
            m' = punsafeCoerce m
            lhs = pscalePositive (pscalePositive asIntermediate n') m'
            rhs = pscalePositive asIntermediate (n' #* m')
         in pd2ToElem irred' order' lhs #== pd2ToElem irred' order' rhs

propScalePosMul' :: Property
propScalePosMul' = forAll (arbitrary @(GenD2Elements 1, _, _)) $ \(GenD2Elements order _ els, n, m) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order # pconstant n # pconstant m)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PInteger ->
        Term s PInteger ->
        Term s PBool
    go x order n m =
        let asIntermediate = Direct.pd2FromElem x
            order' = punsafeCoerce order
            n' = punsafeCoerce n
            m' = punsafeCoerce m
            lhs = pscalePositive (pscalePositive asIntermediate n') m'
            rhs = pscalePositive asIntermediate (n' #* m')
         in Direct.pd2ToElem order' lhs #== Direct.pd2ToElem order' rhs

propOneDivide :: Property
propOneDivide = forAll (arbitrary @(GenD2Elements 1)) $ \(GenD2Elements order irred els) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order # pconstant irred)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PBool
    go t order irred =
        let asIntermediate = pd2FromElem t
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
            lhs = pd2Divide asIntermediate pone
         in pd2ToElem irred' order' lhs #== t

propOneDivide' :: Property
propOneDivide' = forAll (arbitrary @(GenD2Elements 1)) $ \(GenD2Elements order irred els) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order # pconstant irred)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PBool
    go t order irred =
        let asIntermediate = Direct.pd2FromElem t
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
            lhs = Direct.pd2Divide order' irred' asIntermediate Direct.pd2OneI
         in Direct.pd2ToElem order' lhs #== t

propSquare :: Property
propSquare = forAll (arbitrary @(GenD2Elements 1)) $ \(GenD2Elements order irred els) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order # pconstant irred)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PBool
    go t order irred =
        let asIntermediate = pd2FromElem t
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
            lhs = pd2Square asIntermediate
            rhs = asIntermediate #* asIntermediate
         in pd2ToElem irred' order' lhs #== pd2ToElem irred' order' rhs

propSquare' :: Property
propSquare' = forAll (arbitrary @(GenD2Elements 1)) $ \(GenD2Elements order irred els) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order # pconstant irred)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PBool
    go t order irred =
        let asIntermediate = Direct.pd2FromElem t
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
            lhs = Direct.pd2Square irred' asIntermediate
            rhs = Direct.pd2Times irred' asIntermediate asIntermediate
         in Direct.pd2ToElem order' lhs #== Direct.pd2ToElem order' rhs

propCommAdd :: Property
propCommAdd = forAll (arbitrary @(GenD2Elements 2)) $ \(GenD2Elements order irred els) ->
    let x = Vector.index' els (Proxy @0)
        y = Vector.index' els (Proxy @1)
     in plift (precompileTerm (plam go) # pconstant x # pconstant y # pconstant order # pconstant irred)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PBool
    go t1 t2 order irred =
        let lhs = pd2FromElem t1 #+ pd2FromElem t2
            rhs = pd2FromElem t2 #+ pd2FromElem t1
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
         in pd2ToElem irred' order' lhs #== pd2ToElem irred' order' rhs

propCommAdd' :: Property
propCommAdd' = forAll (arbitrary @(GenD2Elements 2)) $ \(GenD2Elements order _ els) ->
    let x = Vector.index' els (Proxy @0)
        y = Vector.index' els (Proxy @1)
     in plift (precompileTerm (plam go) # pconstant x # pconstant y # pconstant order)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PNatural ->
        Term s PBool
    go t1 t2 order =
        let lhs = Direct.pd2FromElem t1 #+ Direct.pd2FromElem t2
            rhs = Direct.pd2FromElem t2 #+ Direct.pd2FromElem t1
            order' = punsafeCoerce order
         in Direct.pd2ToElem order' lhs #== Direct.pd2ToElem order' rhs

propAssocAdd :: Property
propAssocAdd = forAll (arbitrary @(GenD2Elements 3)) $ \(GenD2Elements order irred els) ->
    let x = Vector.index' els (Proxy @0)
        y = Vector.index' els (Proxy @1)
        z = Vector.index' els (Proxy @2)
     in plift (precompileTerm (plam go) # pconstant x # pconstant y # pconstant z # pconstant order # pconstant irred)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PBool
    go t1 t2 t3 order irred =
        let lhs = pd2FromElem t1 #+ (pd2FromElem t2 #+ pd2FromElem t3)
            rhs = (pd2FromElem t1 #+ pd2FromElem t2) #+ pd2FromElem t3
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
         in pd2ToElem irred' order' lhs #== pd2ToElem irred' order' rhs

propAssocAdd' :: Property
propAssocAdd' = forAll (arbitrary @(GenD2Elements 3)) $ \(GenD2Elements order _ els) ->
    let x = Vector.index' els (Proxy @0)
        y = Vector.index' els (Proxy @1)
        z = Vector.index' els (Proxy @2)
     in plift (precompileTerm (plam go) # pconstant x # pconstant y # pconstant z # pconstant order)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PNatural ->
        Term s PBool
    go t1 t2 t3 order =
        let lhs = Direct.pd2FromElem t1 #+ (Direct.pd2FromElem t2 #+ Direct.pd2FromElem t3)
            rhs = (Direct.pd2FromElem t1 #+ Direct.pd2FromElem t2) #+ Direct.pd2FromElem t3
            order' = punsafeCoerce order
         in Direct.pd2ToElem order' lhs #== Direct.pd2ToElem order' rhs

propZeroAdd :: Property
propZeroAdd = forAll (arbitrary @(GenD2Elements 1)) $ \(GenD2Elements order irred els) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order # pconstant irred)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PBool
    go t order irred =
        let lhs = pd2FromElem t #+ pzero
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
         in pd2ToElem irred' order' lhs #== t

propZeroAdd' :: Property
propZeroAdd' = forAll (arbitrary @(GenD2Elements 1)) $ \(GenD2Elements order _ els) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PBool
    go t order =
        let lhs = Direct.pd2FromElem t #+ pzero
            order' = punsafeCoerce order
         in Direct.pd2ToElem order' lhs #== t

propNegate :: Property
propNegate = forAll (arbitrary @(GenD2Elements 1)) $ \(GenD2Elements order irred els) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order # pconstant irred)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PBool
    go t order irred = pd2ToElem (punsafeCoerce irred) (punsafeCoerce order) (pd2FromElem t #- pd2FromElem t) #== pd2Zero

propNegate' :: Property
propNegate' = forAll (arbitrary @(GenD2Elements 1)) $ \(GenD2Elements order _ els) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PBool
    go t order = Direct.pd2ToElem (punsafeCoerce order) (Direct.pd2FromElem t #- Direct.pd2FromElem t) #== pd2Zero

propCommMul :: Property
propCommMul = forAll (arbitrary @(GenD2Elements 2)) $ \(GenD2Elements order irred els) ->
    let x = Vector.index' els (Proxy @0)
        y = Vector.index' els (Proxy @1)
     in plift (precompileTerm (plam go) # pconstant x # pconstant y # pconstant order # pconstant irred)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PBool
    go t1 t2 order irred =
        let lhs = pd2FromElem t1 #* pd2FromElem t2
            rhs = pd2FromElem t2 #* pd2FromElem t1
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
         in pd2ToElem irred' order' lhs #== pd2ToElem irred' order' rhs

propCommMul' :: Property
propCommMul' = forAll (arbitrary @(GenD2Elements 2)) $ \(GenD2Elements order irred els) ->
    let x = Vector.index' els (Proxy @0)
        y = Vector.index' els (Proxy @1)
     in plift (precompileTerm (plam go) # pconstant x # pconstant y # pconstant order # pconstant irred)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PBool
    go t1 t2 order irred =
        let irred' = punsafeCoerce irred
            lhs = Direct.pd2Times irred' (Direct.pd2FromElem t1) (Direct.pd2FromElem t2)
            rhs = Direct.pd2Times irred' (Direct.pd2FromElem t2) (Direct.pd2FromElem t1)
            order' = punsafeCoerce order
         in Direct.pd2ToElem order' lhs #== Direct.pd2ToElem order' rhs

propAssocMul :: Property
propAssocMul = forAll (arbitrary @(GenD2Elements 3)) $ \(GenD2Elements order irred els) ->
    let x = Vector.index' els (Proxy @0)
        y = Vector.index' els (Proxy @1)
        z = Vector.index' els (Proxy @2)
     in plift (precompileTerm (plam go) # pconstant x # pconstant y # pconstant z # pconstant order # pconstant irred)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PBool
    go t1 t2 t3 order irred =
        let lhs = pd2FromElem t1 #* (pd2FromElem t2 #* pd2FromElem t3)
            rhs = (pd2FromElem t1 #* pd2FromElem t2) #* pd2FromElem t3
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
         in pd2ToElem irred' order' lhs #== pd2ToElem irred' order' rhs

propAssocMul' :: Property
propAssocMul' = forAll (arbitrary @(GenD2Elements 3)) $ \(GenD2Elements order irred els) ->
    let x = Vector.index' els (Proxy @0)
        y = Vector.index' els (Proxy @1)
        z = Vector.index' els (Proxy @2)
     in plift (precompileTerm (plam go) # pconstant x # pconstant y # pconstant z # pconstant order # pconstant irred)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PBool
    go t1 t2 t3 order irred =
        let irred' = punsafeCoerce irred
            t1' = Direct.pd2FromElem t1
            t2' = Direct.pd2FromElem t2
            t3' = Direct.pd2FromElem t3
            lhs = Direct.pd2Times irred' t1' (Direct.pd2Times irred' t2' t3')
            rhs = Direct.pd2Times irred' (Direct.pd2Times irred' t1' t2') t3'
            order' = punsafeCoerce order
         in Direct.pd2ToElem order' lhs #== Direct.pd2ToElem order' rhs

propOneMul :: Property
propOneMul = forAll (arbitrary @(GenD2Elements 1)) $ \(GenD2Elements order irred els) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order # pconstant irred)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PBool
    go t order irred =
        let lhs = pd2FromElem t #* pone
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
         in pd2ToElem irred' order' lhs #== t

propOneMul' :: Property
propOneMul' = forAll (arbitrary @(GenD2Elements 1)) $ \(GenD2Elements order irred els) ->
    let x = Vector.index' els (Proxy @0)
     in plift (precompileTerm (plam go) # pconstant x # pconstant order # pconstant irred)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PBool
    go t order irred =
        let irred' = punsafeCoerce irred
            lhs = Direct.pd2Times irred' (Direct.pd2FromElem t) Direct.pd2OneI
            order' = punsafeCoerce order
         in Direct.pd2ToElem order' lhs #== t

propDistribute :: Property
propDistribute = forAll (arbitrary @(GenD2Elements 3)) $ \(GenD2Elements order irred els) ->
    let x = Vector.index' els (Proxy @0)
        y = Vector.index' els (Proxy @1)
        z = Vector.index' els (Proxy @2)
     in plift (precompileTerm (plam go) # pconstant x # pconstant y # pconstant z # pconstant order # pconstant irred)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PBool
    go t1 t2 t3 order irred =
        let lhs = pd2FromElem t1 #* (pd2FromElem t2 #+ pd2FromElem t3)
            rhs = (pd2FromElem t1 #* pd2FromElem t2) #+ (pd2FromElem t1 #* pd2FromElem t3)
            order' = punsafeCoerce order
            irred' = punsafeCoerce irred
         in pd2ToElem irred' order' lhs #== pd2ToElem irred' order' rhs

propDistribute' :: Property
propDistribute' = forAll (arbitrary @(GenD2Elements 3)) $ \(GenD2Elements order irred els) ->
    let x = Vector.index' els (Proxy @0)
        y = Vector.index' els (Proxy @1)
        z = Vector.index' els (Proxy @2)
     in plift (precompileTerm (plam go) # pconstant x # pconstant y # pconstant z # pconstant order # pconstant irred)
  where
    go ::
        forall (s :: S).
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PD2Element ->
        Term s PNatural ->
        Term s PNatural ->
        Term s PBool
    go t1 t2 t3 order irred =
        let irred' = punsafeCoerce irred
            t1' = Direct.pd2FromElem t1
            t2' = Direct.pd2FromElem t2
            t3' = Direct.pd2FromElem t3
            lhs = Direct.pd2Times irred' t1' (t2' #+ t3')
            rhs = Direct.pd2Times irred' t1' t2' #+ Direct.pd2Times irred' t1' t3'
            order' = punsafeCoerce order
         in Direct.pd2ToElem order' lhs #== Direct.pd2ToElem order' rhs

-- Helpers

-- BLS12-381 G1 field order
const381 :: Natural
const381 = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787

pconst381 :: forall (s :: S). Term s PPositive
pconst381 = punsafeCoerce $ pconstant @PNatural const381

-- 2^390
huge1 :: Natural
huge1 = 2521728396569246669585858566409191283525103313309788586748690777871726193375821479130513040312634601011624191379636224

-- 2^392
huge2 :: Natural
huge2 = 10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896

-- -1 reduced modulo
psampleIrred :: forall (s :: S). Term s PNatural
psampleIrred = evalTerm' NoTracing (punsafeCoerce $ pexpModInteger # (-1) # (-1) # punsafeCoerce (pconstant @PNatural const381))

psample :: forall (s :: S). Term s PD2Element
psample = pconstant $ mkD2Element huge1 huge2 const381

psampleInt :: forall (s :: S). Term s PD2Intermediate
psampleInt = evalTerm' NoTracing (pd2FromElem psample)

psampleInt' :: forall (s :: S). Term s Direct.PD2Intermediate
psampleInt' = evalTerm' NoTracing (Direct.pd2FromElem psample)

psampleInt2 :: forall (s :: S). Term s PD2Intermediate
psampleInt2 = evalTerm' NoTracing (psampleInt #+ psampleInt)

psampleInt2' :: forall (s :: S). Term s Direct.PD2Intermediate
psampleInt2' = evalTerm' NoTracing (psampleInt' #+ psampleInt')

psampleIntSquared :: forall (s :: S). Term s PD2Intermediate
psampleIntSquared = evalTerm' NoTracing (pd2Square psampleInt)

psampleIntSquared' :: forall (s :: S). Term s Direct.PD2Intermediate
psampleIntSquared' = evalTerm' NoTracing (Direct.pd2Square (punsafeCoerce psampleIrred) psampleInt')
