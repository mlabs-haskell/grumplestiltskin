{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
-- Note (Koz, 19/08/2025): Needed until we add some PTryFrom instances to
-- Plutarch.
{-# OPTIONS_GHC -Wno-orphans #-}

-- | @since 1.0.0
module Grumplestiltskin.Galois (
    -- * Types

    -- ** Haskell
    GFElement,

    -- ** Plutarch

    -- *** @Data@ encoded
    PGFElementData,

    -- *** SOP encoded
    PGFElement,
    PGFIntermediate,

    -- * Functions

    -- ** Element introduction
    naturalToGFElement,
    pgfZero,
    pgfOne,

    -- ** Representation change
    pgfFromData,
    pgfToData,

    -- ** Operations
    pgfRecip,
    pgfExp,

    -- ** Element to intermediate
    pgfFromElem,

    -- ** Finalizing computations
    pgfToElem,
) where

import Data.Coerce (coerce)
import GHC.Generics (Generic)
import Generics.SOP qualified as SOP
import Numeric.Natural (Natural)
import Plutarch.Builtin.Integer (pexpModInteger)
import Plutarch.Internal.Lift (
    LiftError (OtherLiftError),
    getPLifted,
    mkPLifted,
 )
import Plutarch.Prelude (
    DeriveNewtypePlutusType (DeriveNewtypePlutusType),
    PAdditiveGroup (pnegate, pscaleInteger, (#-)),
    PAdditiveMonoid (pscaleNatural, pzero),
    PAdditiveSemigroup (pscalePositive),
    PAsData,
    PData,
    PEq,
    PInteger,
    PIsData,
    PLiftable (
        AsHaskell,
        PlutusRepr,
        haskToRepr,
        plutToRepr,
        reprToHask,
        reprToPlut
    ),
    PLifted,
    PMultiplicativeMonoid (pone),
    PMultiplicativeSemigroup ((#*)),
    PNatural,
    POrd,
    PPositive,
    PTryFrom (ptryFrom'),
    PlutusType,
    S,
    Term,
    pasInt,
    pasList,
    pcon,
    pconstant,
    pdata,
    perror,
    pfromData,
    pheadBuiltin,
    phoistAcyclic,
    pif,
    plam,
    plet,
    pmatch,
    pmod,
    ptailBuiltin,
    ptraceInfo,
    ptryFrom,
    ptryNatural,
    pupcast,
    runTermCont,
    tcont,
    (#),
    (#$),
    (#<),
    (:-->),
 )
import Plutarch.Repr.Data (DeriveAsDataRec (DeriveAsDataRec))
import Plutarch.Unsafe (punsafeCoerce)
import Test.QuickCheck (
    Arbitrary (arbitrary, shrink),
    chooseInt,
 )
import Test.QuickCheck.Instances.Natural ()

{- | @Data@-encoded element of a Galois field, together with the order of its
field. This type is designed primarily as an exchange format (such as for use
in datums): to do any work, we recommend converting to 'PGFElement' using
'pgfFromData'.

@since 1.0.0
-}
data PGFElementData (s :: S)
    = PGFElementData
        (Term s (PAsData PNatural))
        (Term s (PAsData PPositive))
    deriving stock
        ( -- | @since 1.0.0
          Generic
        )
    deriving anyclass
        ( -- | @since 1.0.0
          SOP.Generic
        , -- | @since 1.0.0
          PIsData
        )

-- | @since 1.0.0
deriving via (DeriveAsDataRec PGFElementData) instance PlutusType PGFElementData

{- | This instance does (some) validation. Specifically, it will check whether
the 'PNatural' field is strictly less than the 'PPositive' field.

@since 1.0.0
-}
instance PTryFrom PData (PAsData PGFElementData) where
    ptryFrom' opq = runTermCont $ do
        ell <- tcont $ plet (pasList # opq)
        (x, _) <- tcont $ ptryFrom (pheadBuiltin # ell)
        (b, _) <- tcont $ ptryFrom (pheadBuiltin #$ ptailBuiltin # ell)
        res <- tcont $ \k ->
            pif
                (pupcast (pfromData x) #< pupcast @PInteger (pfromData b))
                (k . pdata . pcon . PGFElementData x $ b)
                (ptraceInfo "PTryFrom PGFElementData: unsuitable element for given field order" perror)
        pure (res, ())

{- | Convert a @Data@-represented Galois field element to its SOP-represented
equivalent.

= Note

We \'forget\' the order of the field in this process.
-}
pgfFromData :: forall (s :: S). Term s PGFElementData -> Term s PGFElement
pgfFromData t = pmatch t $ \case
    PGFElementData x _ -> pcon . PGFElement . pfromData $ x

{- | Given a SOP-encoded Galois field element, together with its field order,
construct its @Data@-encoded equivalent.

= Note

This conversion does not check that the field order is prime, nor that the
SOP-encoded element is suitable for a field of that order.
-}
pgfToData :: forall (s :: S). Term s PGFElement -> Term s PPositive -> Term s PGFElementData
pgfToData x b = pmatch x $ \case
    PGFElement x' -> pcon . PGFElementData (pdata x') . pdata $ b

{- | An intermediate computation over some finite field. This type exists for
efficiency: thus, you want to do all your calculations in 'PGFIntermediate',
then convert to 'PGFElement' at the end.

@since 1.0.0
-}
newtype PGFIntermediate (s :: S) = PGFIntermediate (Term s PInteger)
    deriving stock
        ( -- | @since 1.0.0
          Generic
        )
    deriving anyclass
        ( -- | @since 1.0.0
          SOP.Generic
        )
    deriving
        ( -- | @since 1.0.0
          PlutusType
        )
        via (DeriveNewtypePlutusType PGFIntermediate)

-- | @since 1.0.0
instance PAdditiveSemigroup PGFIntermediate where
    pscalePositive x p = x #* punsafeCoerce p

-- | @since 1.0.0
instance PAdditiveMonoid PGFIntermediate where
    pzero = pcon . PGFIntermediate $ pzero
    pscaleNatural x n = x #* punsafeCoerce n

-- | @since 1.0.0
instance PAdditiveGroup PGFIntermediate where
    pnegate = punsafeCoerce (pnegate @PInteger)
    x #- y = pcon . PGFIntermediate $ pupcast x #- pupcast y
    pscaleInteger x i = x #* punsafeCoerce i

{- | = Note

Avoid using 'ppowPositive' with 'PGFIntermediate', as this is quite
inefficient. Use 'pgfExp' instead.

@since 1.0.0
-}
instance PMultiplicativeSemigroup PGFIntermediate

{- | = Note

Avoid using 'ppowNatural' with 'PGFIntermediate', as this is quite
inefficient. Use 'pgfExp' instead.

@since 1.0.0
-}
instance PMultiplicativeMonoid PGFIntermediate where
    pone = pcon . PGFIntermediate $ pone

-- | @since 1.0.0
newtype GFElement = GFElement Natural
    deriving
        ( -- | @since 1.0.0
          Eq
        , -- | @since 1.0.0
          Ord
        )
        via Natural
    deriving stock
        ( -- | @since 1.0.0
          Show
        )

{- | This generates elements of the field @GF(97)@. While a somewhat arbitrary
choice, this value is both prime, and within the default QuickCheck size of
100, hence the choice.

@since 1.0.0
-}
instance Arbitrary GFElement where
    arbitrary = GFElement . fromIntegral <$> chooseInt (0, 96)
    shrink (GFElement i) = GFElement <$> shrink i

{- | Smart constructor for `GFElement`: given a value and a modulus, construct
the 'GFElement' representing that value in the field of order equal to the
modulus. The modulus should be prime, but this is not checked.

= Note

If given a zero modulus, this will error.

@since 1.0.0
-}
naturalToGFElement :: Natural -> Natural -> GFElement
naturalToGFElement i b = GFElement $ i `mod` fromIntegral b

{- | An element in some Galois field. The order of the field in question is
implicit for reasons of efficiency.

@since 1.0.0
-}
newtype PGFElement (s :: S) = PGFElement (Term s PNatural)
    deriving stock
        ( -- | @since 1.0.0
          Generic
        )
    deriving anyclass
        ( -- | @since 1.0.0
          SOP.Generic
        )
    deriving
        ( -- | @since 1.0.0
          PlutusType
        )
        via (DeriveNewtypePlutusType PGFElement)

-- | @since 1.0.0
instance PEq PGFElement

-- | @since 1.0.0
instance POrd PGFElement

-- | @since 1.0.0
instance PLiftable PGFElement where
    type AsHaskell PGFElement = GFElement
    type PlutusRepr PGFElement = Integer
    haskToRepr = fromIntegral . coerce @_ @Natural
    reprToHask e =
        if e < 0
            then Left . OtherLiftError $ "Negative Integer is not a valid GFElement"
            else Right . GFElement . fromIntegral $ e
    reprToPlut = mkPLifted . pcon . PGFElement . pconstant . fromIntegral
    plutToRepr t = case plutToRepr (go . getPLifted $ t) of
        Left err -> Left err
        Right res -> Right . fromIntegral $ res
      where
        go :: forall (s :: S). Term s PGFElement -> PLifted s PNatural
        go = mkPLifted . pupcast

{- | Compute the reciprocal of a finite field element, given an order. The
function assumes the 'PPositive' argument is prime, and may fail otherwise.

Reciprocal is the modular multiplicative inverse. I.e., the modular
multiplicative inverse for @a mod b@ is and integer @x@ such that @(a * x) mod b = 1@.

@since 1.0.0
-}
pgfRecip :: Term s (PGFIntermediate :--> PPositive :--> PGFElement)
pgfRecip = phoistAcyclic $ plam $ \x b ->
    pcon . PGFElement . punsafeCoerce $ pexpModInteger # pupcast @PInteger x # (-1) # pupcast b

{- | @'pgfExp' # x # e # b@ computes @x@ to the power of @e@, assuming we are in
a field of order @b@. The function assumes the 'PPositive' argument is prime, and
may fail otherwise.

@since 1.0.0
-}
pgfExp :: Term s (PGFIntermediate :--> PInteger :--> PPositive :--> PGFElement)
pgfExp = punsafeCoerce pexpModInteger

{- | Convert a 'PGFIntermediate' into a valid element of the finite field of
order specified by the 'PPositive' argument. Said argument should be prime,
though 'pgfToElem' doesn't require it.

@since 1.0.0
-}
pgfToElem :: forall (s :: S). Term s PGFIntermediate -> Term s PPositive -> Term s PGFElement
pgfToElem x b = pcon . PGFElement . punsafeCoerce $ pmod # pupcast x # pupcast b

{- | Transform an element of a finite field into an intermediate representation,
suitable for faster computation. This operation involves only @newtype@
rewrapping, and is thus effectively free.

@since 1.0.0
-}
pgfFromElem :: forall (s :: S). Term s PGFElement -> Term s PGFIntermediate
pgfFromElem = punsafeCoerce

{- | The zero element (the additive identity), which exists in every Galois
field.

@since 1.0.0
-}
pgfZero :: forall (s :: S). Term s PGFElement
pgfZero = pconstant . GFElement $ 0

{- | The one element (the multiplicative identity), which exists in every Galois
field.

@since 1.0.0
-}
pgfOne :: forall (s :: S). Term s PGFElement
pgfOne = pconstant . GFElement $ 1

-- Orphans

instance PTryFrom PData (PAsData PNatural) where
    ptryFrom' opq = runTermCont $ do
        i <- tcont $ plet (pasInt # opq)
        pure (pdata $ ptryNatural # i, ())
