{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}

module Grumplestiltskin.Degree2.Element (
    D2Element (D2Element),
    PD2Element (PD2Element),
    mkD2Element,
    mkSubD2Element,
    pd2Zero,
    pd2One,
    fromD2Element,
    pd2FromPoint,
    pd2ToPoint,
) where

import Data.Kind (Type)
import GHC.Generics (Generic)
import Generics.SOP qualified as SOP
import Numeric.Natural (Natural)
import Plutarch.Internal.Lift (
    LiftError (OtherLiftError),
    PLiftedClosed,
    getPLiftedClosed,
    mkPLifted,
    mkPLiftedClosed,
    pliftedFromClosed,
    pliftedToClosed,
 )
import Plutarch.Internal.PlutusType (PlutusType)
import Plutarch.Prelude (
    DeriveAsSOPStruct (DeriveAsSOPStruct),
    PEq,
    PLiftable (
        AsHaskell,
        PlutusRepr,
        haskToRepr,
        plutToRepr,
        reprToHask,
        reprToPlut
    ),
    PNatural,
    PShow,
    S,
    Term,
    pcon,
    pconstant,
    phoistAcyclic,
    plam,
    pmatch,
    pmod,
    pupcast,
    (#),
    (:-->),
 )
import Plutarch.Unsafe (punsafeCoerce)

{- | Haskell-level representation of an element of a second-degree extension of
some finite field. The field order is implicit, but the assumption is that
both the \'real\' and \'imaginary\' parts of the element are already in
reduced form.

@since wip
-}
data D2Element = D2E Natural Natural
    deriving stock
        ( -- | @since wip
          Eq
        )

-- | @since wip
instance Show D2Element where
    show (D2Element x y) = "(" <> show x <> " + " <> show y <> "u)"

-- | @since wip
pattern D2Element :: Natural -> Natural -> D2Element
pattern D2Element x y <- D2E x y

{-# COMPLETE D2Element #-}

{- | Given a \'real part\', an \'imaginary part\' and a field modulus, construct
the corresponding 'D2Element' in the field extension corresponding to that
modulus. The modulus should be prime, but this is not checked.

= Note

If given a zero modulus, this will error.

@since wip
-}
mkD2Element :: Natural -> Natural -> Natural -> D2Element
mkD2Element r i b = D2E (r `mod` b) (i `mod` b)

{- | As 'mkD2Element', but with the \'imaginary part\' always zero.

@since wip
-}
mkSubD2Element :: Natural -> Natural -> D2Element
mkSubD2Element r b = D2E (r `mod` b) 0

{- | Convert a 'D2Element' into its \'real\' and \'imaginary\' components, as
'Natural's.

@since wip
-}
fromD2Element :: D2Element -> (Natural, Natural)
fromD2Element (D2Element r i) = (r, i)

{- | Plutarch-level representation of an element of a second-degree extension of
some finite field. The field order is implicit, but the assumption is that
both the \'real\' and \'imaginary\' parts of the element are already in
reduced form.

@since wip
-}
data PD2Element (s :: S) = PD2Element (Term s PNatural) (Term s PNatural)
    deriving stock
        ( -- | @since wip
          Generic
        )
    deriving anyclass
        ( -- | @since wip
          SOP.Generic
        , -- | @since wip
          PEq
        , -- | @since wip
          PShow
        )
    deriving
        ( -- | @since wip
          PlutusType
        )
        via (DeriveAsSOPStruct PD2Element)

-- | @since wip
instance PLiftable PD2Element where
    type AsHaskell PD2Element = D2Element
    type PlutusRepr PD2Element = PLiftedClosed PD2Element
    haskToRepr (D2Element r i) = mkPLiftedClosed $ pcon $ PD2Element (pconstant r) (pconstant i)
    reprToHask t = do
        realPart :: Integer <- plutToRepr $ mkPLifted (prealPart # getPLiftedClosed t)
        imaginaryPart :: Integer <- plutToRepr $ mkPLifted (pimaginaryPart # getPLiftedClosed t)
        if
            | realPart < 0 -> Left . OtherLiftError $ "Negative real part is not valid for PD2Element"
            | imaginaryPart < 0 -> Left . OtherLiftError $ "Negative imaginary part is not valid for PD2Element"
            | otherwise -> pure $ D2E (fromIntegral realPart) (fromIntegral imaginaryPart)
    reprToPlut = pliftedFromClosed
    plutToRepr = Right . pliftedToClosed

-- | @since wip
pd2FromPoint ::
    forall (r :: S -> Type) (s :: S).
    Term s PD2Element ->
    (Term s PNatural -> Term s PNatural -> Term s r) ->
    Term s r
pd2FromPoint t f = pmatch t $ \(PD2Element x y) -> f x y

-- | @since wip
pd2ToPoint ::
    forall (s :: S).
    Term s PNatural ->
    Term s PNatural ->
    Term s PNatural ->
    Term s PD2Element
pd2ToPoint r i fieldMod =
    let r' = punsafeCoerce (pmod # pupcast r # pupcast fieldMod)
        i' = punsafeCoerce (pmod # pupcast i # pupcast fieldMod)
     in pcon . PD2Element r' $ i'

{- | The zero element (the additive identity), which exists in every
second-degree extension of any finite field. More precisely, this has the
zero element as both its \'real\' and its \'imaginary\' part.

@since wip
-}
pd2Zero :: forall (s :: S). Term s PD2Element
pd2Zero = pconstant . D2E 0 $ 0

{- | The one element (the multiplicative identity), which exists in every
second-degree extension of any finite field. More precisely, this has the one
element as its \'real\' part, and the zero element as its \'imaginary\' part.

@since wip
-}
pd2One :: forall (s :: S). Term s PD2Element
pd2One = pconstant . D2E 1 $ 0

-- Helpers

prealPart :: forall (s :: S). Term s (PD2Element :--> PNatural)
prealPart = phoistAcyclic $ plam $ \t -> pmatch t $ \case
    PD2Element r _ -> r

pimaginaryPart :: forall (s :: S). Term s (PD2Element :--> PNatural)
pimaginaryPart = phoistAcyclic $ plam $ \t -> pmatch t $ \case
    PD2Element _ i -> i
