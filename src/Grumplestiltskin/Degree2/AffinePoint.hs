{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Grumplestiltskin.Degree2.AffinePoint (
    -- * Types

    -- ** Haskell
    EC2Point (..),

    -- ** Plutarch
    PEC2Point (..),

    -- * Functions
    pec2FromElems,
    pec2OnCurve,
) where

import GHC.Generics (Generic)
import Generics.SOP qualified as SOP
import Grumplestiltskin.Degree2.Element (
    D2Element,
    PD2Element,
 )
import Grumplestiltskin.Degree2.Galois (
    pd2FromElem,
    pd2ToElem,
 )
import Plutarch.Internal.Lift (PLifted (PLifted))
import Plutarch.Prelude (
    DeriveAsSOPStruct (DeriveAsSOPStruct),
    PBool (PTrue),
    PEq,
    PLiftable,
    PPositive,
    PShow,
    PlutusType,
    S,
    Term,
    pcon,
    plet,
    pmatch,
    (#*),
    (#+),
    (#==),
 )
import Plutarch.Repr.Derive (DerivePLiftableAsRepr)
import Plutarch.Unsafe (punsafeCoerce)

-- | @since wip
data EC2Point
    = EC2Infinity
    | EC2Point D2Element D2Element
    deriving stock
        ( -- | @since wip
          Eq
        , -- | @since wip
          Show
        , -- | @since wip
          Generic
        )
    deriving anyclass (SOP.Generic)

-- | @since wip
data PEC2Point (s :: S)
    = PEC2Infinity
    | PEC2Point (Term s PD2Element) (Term s PD2Element)
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
        via (DeriveAsSOPStruct PEC2Point)

-- | @since wip
deriving via DerivePLiftableAsRepr PEC2Point EC2Point instance PLiftable PEC2Point

-- | @since wip
pec2FromElems :: forall (s :: S). Term s PD2Element -> Term s PD2Element -> Term s PEC2Point
pec2FromElems x = pcon . PEC2Point x

{- | Given a field order (as a 'PPositive'), an irreducible (also as a
'PPositive') and @A@ and @B@ constants for an
elliptic curve (both 'PInteger's), check if a 'PEC2Point' is on that curve.
The point at infinity is considered to be on every curve.

@since wip
-}
pec2OnCurve ::
    forall (s :: S).
    Term s PPositive ->
    Term s PPositive ->
    Term s PD2Element ->
    Term s PD2Element ->
    Term s PEC2Point ->
    Term s PBool
pec2OnCurve fieldOrder rSquared constantA constantB p = pmatch p $ \case
    PEC2Infinity -> pcon PTrue
    PEC2Point x y -> plet (pd2FromElem x) $ \x' ->
        plet (pd2FromElem y) $ \y' ->
            let lhs = y' #* y'
                rhs = (x' #* (x' #* x')) #+ ((pd2FromElem constantA #* x') #+ pd2FromElem constantB)
                rSquared' = punsafeCoerce rSquared
             in pd2ToElem rSquared' fieldOrder lhs #== pd2ToElem rSquared' fieldOrder rhs
