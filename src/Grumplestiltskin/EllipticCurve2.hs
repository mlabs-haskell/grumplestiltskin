{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Grumplestiltskin.EllipticCurve2 where

import Data.Kind (Type)
import GHC.Generics (Generic)
import Generics.SOP qualified as SOP
import Grumplestiltskin.Degree2 (
    PD2Element,
    PD2Intermediate,
    pd2Divide,
    pd2FromElem,
    pd2ToElem,
    pd2Zero,
 )
import Plutarch.Internal.Case (punsafeCase)
import Plutarch.Internal.PlutusType (PlutusType (PInner, pcon', pmatch'))
import Plutarch.Prelude (
    DeriveAsSOPStruct (DeriveAsSOPStruct),
    PAdditiveGroup (pnegate, pscaleInteger, (#-)),
    PAdditiveMonoid (pscaleNatural, pzero),
    PAdditiveSemigroup (pscalePositive, (#+)),
    PBool (PTrue),
    PEq,
    PInteger,
    PNatural,
    PPositive,
    PShow,
    PlutusType,
    S,
    Term,
    pcon,
    pif,
    plam,
    plet,
    pmatch,
    pone,
    popaque,
    pscaleInteger,
    pupcast,
    (#),
    (#*),
    (#+),
    (#-),
    (#==),
    (:-->),
 )
import Plutarch.Unsafe (punsafeCoerce)

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
    Term s PInteger ->
    Term s PInteger ->
    Term s PEC2Point ->
    Term s PBool
pec2OnCurve fieldOrder rSquared constantA constantB p = pmatch p $ \case
    PEC2Infinity -> pcon PTrue
    PEC2Point x y -> plet (pd2FromElem x) $ \x' ->
        plet (pd2FromElem y) $ \y' ->
            plet (x' #* x') $ \xSquared ->
                let lhs = y' #* y'
                    rhs = ((x' #* xSquared) #+ pscaleInteger xSquared constantA) #+ pscaleInteger pone constantB
                 in pd2ToElem lhs _ #== pd2ToElem rhs _

newtype PEC2Intermediate (s :: S)
    = PEC2Intermediate
        ( forall (r :: S -> Type).
          Term
            s
            ( -- Field modulus
              PPositive
                :-->
                -- Irreducible
                PNatural
                :-->
                -- Curve A as a pair
                PInteger
                :--> PInteger
                :-->
                -- Take both points as separate X, Y pairs, with _singular_ Z, as it can
                -- only be 0 or 1
                (PInteger :--> PInteger :--> PInteger :--> PInteger :--> PNatural :--> r)
                :--> r
            )
        )

-- | @since wip
instance PlutusType PEC2Intermediate where
    type PInner PEC2Intermediate = PEC2Intermediate
    pcon' (PEC2Intermediate t) = punsafeCoerce t
    pmatch' t f = f (PEC2Intermediate $ punsafeCoerce t)

-- | @since wip
instance PAdditiveSemigroup PEC2Intermediate where
    t1 #+ t2 = pmatch t1 $ \(PEC2Intermediate k1) ->
        pmatch t2 $ \(PEC2Intermediate k2) ->
            pcon $ PEC2Intermediate $ plam $ \fieldModulus rSquared aR aI k ->
                k1
                    # fieldModulus
                    # rSquared
                    # aR
                    # aI
                    # plam
                        ( \xR1 xI1 yR1 yI1 z1 ->
                            k2
                                # fieldModulus
                                # rSquared
                                # aR
                                # aI
                                # plam
                                    ( \xR2 xI2 yR2 yI2 z2 ->
                                        -- Note (Koz, 27/02/26): We use this somewhat odd form to save on
                                        -- code size. We essentially need a four-way branch:
                                        --
                                        -- \* If z1 = 0 and z2 = 0, we want to just give the normalized point
                                        --   at infinity
                                        -- \* If z1 = 0, then we want to produce the second argument
                                        -- \* If z2 = 0, then we want to produce the first argument
                                        -- \* If z1 = 1 and z2 = 1, we need to go through 'regular' addition
                                        --
                                        -- No matter how we do this, we need at least two builtin calls to
                                        -- distinguish the cases. The naive method (using nested `pif`s)
                                        -- generates a lot more code, as we have to have `Case` inside of
                                        -- `Case`. By using a bit of arithmetic (still using two builtin
                                        -- calls), we can collapse this into a single `Case`, saving a bit
                                        -- of code size.
                                        punsafeCase
                                            ((z1 #* pnatTwo) #+ z2)
                                            [ -- z1 = 0, z2 = 0, as 2 * 0 + 0 = 0
                                              popaque (k # 0 # 0 # 1 # 0 # pnatZero)
                                            , -- z1 = 0, z2 = 1, as 2 * 0 + 1 = 1
                                              popaque (k # xR2 # xI2 # yR2 # yI2 # z2)
                                            , -- z1 = 1, z2 = 0, as 2 * 1 + 0 = 2
                                              popaque (k # xR1 # xI1 # yR1 # yI1 # z1)
                                            , -- z1 = 1, z2 = 1, as 2 * 1 + 1 = 3
                                              popaque
                                                ( plet (xR2 #- xR1) $ \xRDiff ->
                                                    plet (xI2 #- xI1) $ \xIDiff ->
                                                        pif
                                                            (xRDiff #== 0)
                                                            ( pif
                                                                (xIDiff #== 0)
                                                                ( plet (yR2 #- yR1) $ \yRDiff ->
                                                                    pif
                                                                        (yRDiff #== 0)
                                                                        ( plet (yI2 #- yI1) $ \yIDiff ->
                                                                            pif
                                                                                (yIDiff #== 0)
                                                                                -- Double
                                                                                _
                                                                                -- Infinity
                                                                                (k # 0 # 0 # 1 # 0 # pnatZero)
                                                                        )
                                                                        -- Infinity
                                                                        (k # 0 # 0 # 1 # 0 # pnatZero)
                                                                )
                                                                -- Do regular add
                                                                _
                                                            )
                                                            -- Do regular add
                                                            _
                                                )
                                            ]
                                    )
                        )
    pscalePositive = _

-- | @since wip
instance PAdditiveMonoid PEC2Intermediate where
    pzero = _
    pscaleNatural = _

-- | @since wip
instance PAdditiveGroup PEC2Intermediate where
    pnegate = _
    (#-) = _
    pscaleInteger = _

-- Helpers

pnatZero :: forall (s :: S). Term s PNatural
pnatZero = punsafeCoerce @_ @PInteger 0

pnatOne :: forall (s :: S). Term s PNatural
pnatOne = punsafeCoerce @_ @PInteger 1

pnatTwo :: forall (s :: S). Term s PNatural
pnatTwo = punsafeCoerce @_ @PInteger 2
