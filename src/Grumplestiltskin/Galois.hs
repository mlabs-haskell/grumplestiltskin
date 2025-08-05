{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Grumplestiltskin.Galois (
    -- * Types
    PGFElement,
    PGFIntermediate,

    -- * Functions
    pgRecip,
    pgExp,
    pgToElem,
    pgFromElem,
) where

import GHC.Generics (Generic)
import Generics.SOP qualified as SOP
import Plutarch.Builtin.Integer (pexpModInteger)
import Plutarch.Prelude (
    DeriveNewtypePlutusType (DeriveNewtypePlutusType),
    PAdditiveGroup (pnegate, (#-)),
    PAdditiveMonoid (pzero),
    PAdditiveSemigroup,
    PInteger,
    PMultiplicativeMonoid (pone),
    PMultiplicativeSemigroup,
    PNatural,
    PlutusType,
    S,
    Term,
    pcon,
    phoistAcyclic,
    plam,
    pmod,
    pupcast,
    (#),
    (:-->),
 )
import Plutarch.Unsafe (punsafeCoerce)

newtype PGFIntermediate (s :: S) = PGFIntermediate (Term s PInteger)
    deriving stock (Generic)
    deriving anyclass (SOP.Generic)
    deriving (PlutusType) via (DeriveNewtypePlutusType PGFIntermediate)

instance PAdditiveSemigroup PGFIntermediate

instance PAdditiveMonoid PGFIntermediate where
    pzero = pcon . PGFIntermediate $ pzero

instance PAdditiveGroup PGFIntermediate where
    pnegate = punsafeCoerce (pnegate @PInteger)
    x #- y = pcon . PGFIntermediate $ pupcast x #- pupcast y

instance PMultiplicativeSemigroup PGFIntermediate

instance PMultiplicativeMonoid PGFIntermediate where
    pone = pcon . PGFIntermediate $ pone

newtype PGFElement (s :: S) = PGFElement (Term s PInteger)
    deriving stock (Generic)
    deriving anyclass (SOP.Generic)
    deriving (PlutusType) via (DeriveNewtypePlutusType PGFElement)

pgRecip :: Term s (PGFIntermediate :--> PNatural :--> PGFElement)
pgRecip = phoistAcyclic $ plam $ \x b -> pcon . PGFElement $ pexpModInteger # pupcast x # (-1) # pupcast b

pgExp :: Term s (PGFIntermediate :--> PInteger :--> PNatural :--> PGFElement)
pgExp = punsafeCoerce pexpModInteger

pgToElem :: forall (s :: S). Term s PGFIntermediate -> Term s PNatural -> Term s PGFElement
pgToElem x b = pcon . PGFElement $ pmod # pupcast x # pupcast b

pgFromElem :: forall (s :: S). Term s PGFElement -> Term s PGFIntermediate
pgFromElem = punsafeCoerce
