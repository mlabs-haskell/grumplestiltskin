{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

-- | @since 1.0.0
module Grumplestiltskin.Galois (
    -- * Types
    PGFElement,
    PGFIntermediate,

    -- * Functions

    -- ** Element introduction
    pgfFromPInteger,
    pgfFromInteger,

    -- ** Operations
    pgfRecip,
    pgfExp,

    -- ** Element to intermediate
    pgfFromElem,

    -- ** Finalizing computations
    pgfToElem,
) where

import GHC.Generics (Generic)
import Generics.SOP qualified as SOP
import Numeric.Natural (Natural)
import Plutarch.Builtin.Integer (pexpModInteger)
import Plutarch.Prelude (
    DeriveNewtypePlutusType (DeriveNewtypePlutusType),
    PAdditiveGroup (pnegate, pscaleInteger, (#-)),
    PAdditiveMonoid (pscaleNatural, pzero),
    PAdditiveSemigroup (pscalePositive),
    PEq,
    PInteger,
    PMultiplicativeMonoid (pone),
    PMultiplicativeSemigroup ((#*)),
    PNatural,
    POrd,
    PlutusType,
    S,
    Term,
    pcon,
    pconstant,
    phoistAcyclic,
    plam,
    pmod,
    pupcast,
    (#),
    (:-->),
 )
import Plutarch.Unsafe (punsafeCoerce)

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

{- | An element in some Galois field. The order of the field in question is
implicit for reasons of efficiency.

@since 1.0.0
-}
newtype PGFElement (s :: S) = PGFElement (Term s PInteger)
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

{- | Compute the reciprocal of a finite field element, given an order. The
function assumes the 'PNatural' is prime, and may fail otherwise.

@since 1.0.0
-}
pgfRecip :: Term s (PGFIntermediate :--> PNatural :--> PGFElement)
pgfRecip = phoistAcyclic $ plam $ \x b -> pcon . PGFElement $ pexpModInteger # pupcast x # (-1) # pupcast b

{- | @'pgfExp' # x # e # b@ computes @x@ to the power of @e@, assuming we are in
a field of order @b@. The function assumes 'PNatural' is prime, and may fail
otherwise.

@since 1.0.0
-}
pgfExp :: Term s (PGFIntermediate :--> PInteger :--> PNatural :--> PGFElement)
pgfExp = punsafeCoerce pexpModInteger

{- | Convert a 'PGFIntermediate' into a valid element of the finite field of
order specified by the 'PNatural' argument. Said argument should be prime,
though 'pgfToElem' doesn't require it.

@since 1.0.0
-}
pgfToElem :: forall (s :: S). Term s PGFIntermediate -> Term s PNatural -> Term s PGFElement
pgfToElem x b = pcon . PGFElement $ pmod # pupcast x # pupcast b

{- | Transform an element of a finite field into an intermediate representation,
suitable for faster computation. This operation involves only @newtype@
rewrapping, and is thus effectively free.

@since 1.0.0
-}
pgfFromElem :: forall (s :: S). Term s PGFElement -> Term s PGFIntermediate
pgfFromElem = punsafeCoerce

{- | Transform a 'PInteger' into its equivalent element in a finite field of
order given by the 'PNatural' argument. This argument should be prime,
although 'pgfFromPInteger' doesn't require it.

@since 1.0.0
-}
pgfFromPInteger :: forall (s :: S). Term s PInteger -> Term s PNatural -> Term s PGFElement
pgfFromPInteger i b = pcon . PGFElement $ pmod # i # pupcast b

{- | Transform an 'Integer' into its equivalent element in a finite field of
order given by the 'Natural' argument. This is much cheaper, as both the
order and element are given as constants (as far as onchain is concerned).

The 'Natural' argument should be prime, although 'pgfFromInteger' does not
require it.

@since 1.0.0
-}
pgfFromInteger :: forall (s :: S). Integer -> Natural -> Term s PGFElement
pgfFromInteger i n = pcon . PGFElement . pconstant $ i `mod` fromIntegral n
