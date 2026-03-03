{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Grumplestiltskin.EllipticCurve2 (
    PEC2Point,
    PEC2Intermediate,
    pec2OnCurve,
    pec2Double,
) where

import Data.Kind (Type)
import GHC.Generics (Generic)
import Generics.SOP qualified as SOP
import Grumplestiltskin.Degree2 (
    PD2Element,
    pd2FromElem,
    pd2ToElem,
 )
import Plutarch.Builtin.Integer (pexpModInteger)
import Plutarch.Internal.Case (punsafeCase)
import Plutarch.Internal.PlutusType (PlutusType (PInner, pcon', pmatch'))
import Plutarch.Prelude (
    DeriveAsSOPStruct (DeriveAsSOPStruct),
    PAdditiveGroup (pnegate, pscaleInteger, (#-)),
    PAdditiveMonoid (pzero),
    PAdditiveSemigroup ((#+)),
    PBool (PTrue),
    PEq,
    PInteger,
    PNatural,
    PPositive,
    PShow,
    S,
    Term,
    pcon,
    phoistAcyclic,
    pif,
    plam,
    plet,
    pmatch,
    pmod,
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
                 in pd2ToElem (punsafeCoerce rSquared) fieldOrder lhs #== pd2ToElem (punsafeCoerce rSquared) fieldOrder rhs

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
                                              popaque (callZero # k)
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
                                                                                (doubleCPS # fieldModulus # rSquared # aR # aI # xR1 # xI1 # yR1 # yI1 # k)
                                                                                -- Infinity
                                                                                (callZero # k)
                                                                        )
                                                                        -- Infinity
                                                                        (callZero # k)
                                                                )
                                                                -- Do regular add
                                                                (ecAddCPS # fieldModulus # rSquared # xR1 # xI1 # yR1 # yI1 # yR1 # yI2 # xRDiff # xIDiff # k)
                                                            )
                                                            -- Do regular add
                                                            (ecAddCPS # fieldModulus # rSquared # xR1 # xI1 # yR1 # yI1 # yR1 # yI2 # xRDiff # xIDiff # k)
                                                )
                                            ]
                                    )
                        )

-- | @since wip
instance PAdditiveMonoid PEC2Intermediate where
    pzero = pcon $ PEC2Intermediate $ plam $ \_ _ _ _ k -> callZero # k

-- | @since wip
instance PAdditiveGroup PEC2Intermediate where
    pnegate = phoistAcyclic $ plam $ \t -> pmatch t $ \(PEC2Intermediate k1) ->
        pcon $ PEC2Intermediate $ plam $ \fieldModulus rSquared aR aI k ->
            k1
                # fieldModulus
                # rSquared
                # aR
                # aI
                # plam
                    ( \xR1 xI1 yR1 yI1 z1 ->
                        k # xR1 # xI1 # (pnegate # yR1) # (pnegate # yI1) # z1
                    )

pec2Double ::
    forall (s :: S).
    Term s PEC2Intermediate ->
    Term s PEC2Intermediate
pec2Double t = pmatch t $ \(PEC2Intermediate k1) ->
    pcon $ PEC2Intermediate $ plam $ \fieldModulus rSquared aR aI k ->
        k1
            # fieldModulus
            # rSquared
            # aR
            # aI
            # plam
                ( \xR1 xI1 yR1 yI1 z1 ->
                    punsafeCase
                        z1
                        [ -- When z1 = 0, we have the point at infinity, so we have nothing to
                          -- do.
                          popaque (callZero # k)
                        , -- When z1 = 1, we have an actual point.
                          popaque (doubleCPS # fieldModulus # rSquared # aR # aI # xR1 # xI1 # yR1 # yI1 # k)
                        ]
                )

-- Helpers

ecAddCPS ::
    forall (r :: S -> Type) (s :: S).
    Term
        s
        ( -- Field modulus
          PPositive
            :-->
            -- Irreducible
            PNatural
            :-->
            -- X1
            PInteger
            :--> PInteger
            :-->
            -- Y1
            PInteger
            :--> PInteger
            :-->
            -- Y2
            PInteger
            :--> PInteger
            :-->
            -- X2 - X1
            PInteger
            :--> PInteger
            :-->
            -- Continuation
            (PInteger :--> PInteger :--> PInteger :--> PInteger :--> PNatural :--> r)
            :--> r
        )
ecAddCPS = phoistAcyclic $ plam $ \fieldModulus rSquared x1R x1I y1R y1I y2R y2I xDiffR xDiffI k ->
    squareCPS
        # rSquared
        # xDiffR
        # xDiffI
        # plam
            ( \bigB2R bigB2I ->
                timesCPS
                    # rSquared
                    # bigB2R
                    # bigB2I
                    # xDiffR
                    # xDiffI
                    # plam
                        ( \bigB3R bigB3I ->
                            plet (pmod # bigB3R # pupcast fieldModulus) $ \bigB3ReducedR ->
                                plet (pmod # bigB3I # pupcast fieldModulus) $ \bigB3ReducedI ->
                                    pif
                                        ((bigB3ReducedR #+ bigB3ReducedI) #== 0)
                                        (callZero # k)
                                        ( plet (y2R #- y1R) $ \yDiffR ->
                                            plet (y2I #- y1I) $ \yDiffI ->
                                                squareCPS
                                                    # rSquared
                                                    # yDiffR
                                                    # yDiffI
                                                    # plam
                                                        ( \bigASquaredR bigASquaredI ->
                                                            subCPS
                                                                # bigASquaredR
                                                                # bigASquaredI
                                                                # bigB3ReducedR
                                                                # bigB3ReducedI
                                                                # plam
                                                                    ( \bigCLHSR bigCLHSI ->
                                                                        timesCPS
                                                                            # rSquared
                                                                            # bigB2R
                                                                            # bigB2I
                                                                            # x1R
                                                                            # x1I
                                                                            # plam
                                                                                ( \b2x1R b2x1I ->
                                                                                    scaleCPS
                                                                                        # b2x1R
                                                                                        # b2x1I
                                                                                        # 2
                                                                                        # plam
                                                                                            ( \bigCRHSR bigCRHSI ->
                                                                                                subCPS
                                                                                                    # bigCLHSR
                                                                                                    # bigCLHSI
                                                                                                    # bigCRHSR
                                                                                                    # bigCRHSI
                                                                                                    # plam
                                                                                                        ( \bigCR bigCI ->
                                                                                                            timesCPS
                                                                                                                # rSquared
                                                                                                                # xDiffR
                                                                                                                # xDiffI
                                                                                                                # bigCR
                                                                                                                # bigCI
                                                                                                                # plam
                                                                                                                    ( \newXR newXI ->
                                                                                                                        timesCPS
                                                                                                                            # rSquared
                                                                                                                            # bigB3ReducedR
                                                                                                                            # bigB3ReducedI
                                                                                                                            # y1R
                                                                                                                            # y1I
                                                                                                                            # plam
                                                                                                                                ( \newYRHSR newYRHSI ->
                                                                                                                                    subCPS
                                                                                                                                        # b2x1R
                                                                                                                                        # b2x1I
                                                                                                                                        # bigCR
                                                                                                                                        # bigCI
                                                                                                                                        # plam
                                                                                                                                            ( \newYLHSR newYLHSI ->
                                                                                                                                                timesCPS
                                                                                                                                                    # rSquared
                                                                                                                                                    # yDiffR
                                                                                                                                                    # yDiffI
                                                                                                                                                    # newYLHSR
                                                                                                                                                    # newYLHSI
                                                                                                                                                    # plam
                                                                                                                                                        ( \newYLHSR' newYLHSI' ->
                                                                                                                                                            subCPS
                                                                                                                                                                # newYLHSR'
                                                                                                                                                                # newYLHSI'
                                                                                                                                                                # newYRHSR
                                                                                                                                                                # newYRHSI
                                                                                                                                                                # plam
                                                                                                                                                                    ( \newYR newYI ->
                                                                                                                                                                        divideCPS
                                                                                                                                                                            # fieldModulus
                                                                                                                                                                            # rSquared
                                                                                                                                                                            # newXR
                                                                                                                                                                            # newXI
                                                                                                                                                                            # bigB3ReducedR
                                                                                                                                                                            # bigB3ReducedI
                                                                                                                                                                            # plam
                                                                                                                                                                                ( \newXR' newXI' ->
                                                                                                                                                                                    divideCPS
                                                                                                                                                                                        # fieldModulus
                                                                                                                                                                                        # rSquared
                                                                                                                                                                                        # newYR
                                                                                                                                                                                        # newYI
                                                                                                                                                                                        # bigB3ReducedR
                                                                                                                                                                                        # bigB3ReducedI
                                                                                                                                                                                        # plam
                                                                                                                                                                                            ( \newYR' newYI' ->
                                                                                                                                                                                                k # newXR' # newXI' # newYR' # newYI' # pnatOne
                                                                                                                                                                                            )
                                                                                                                                                                                )
                                                                                                                                                                    )
                                                                                                                                                        )
                                                                                                                                            )
                                                                                                                                )
                                                                                                                    )
                                                                                                        )
                                                                                            )
                                                                                )
                                                                    )
                                                        )
                                        )
                        )
            )

callZero ::
    forall (r :: S -> Type) (s :: S).
    Term
        s
        ( (PInteger :--> PInteger :--> PInteger :--> PInteger :--> PNatural :--> r)
            :--> r
        )
callZero = phoistAcyclic $ plam $ \k -> k # 0 # 0 # 0 # 0 # pnatZero

pnatZero :: forall (s :: S). Term s PNatural
pnatZero = punsafeCoerce @_ @PInteger 0

pnatOne :: forall (s :: S). Term s PNatural
pnatOne = punsafeCoerce @_ @PInteger 1

pnatTwo :: forall (s :: S). Term s PNatural
pnatTwo = punsafeCoerce @_ @PInteger 2

doubleCPS ::
    forall (r :: S -> Type) (s :: S).
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
            -- X point as pair
            PInteger
            :--> PInteger
            :-->
            -- Y point as pair
            PInteger
            :--> PInteger
            :-->
            -- Continuation
            (PInteger :--> PInteger :--> PInteger :--> PInteger :--> PNatural :--> r)
            :--> r
        )
doubleCPS = phoistAcyclic $ plam $ \fieldMod rSquared aR aI xR xI yR yI k ->
    squareCPS
        # rSquared
        # yR
        # yI
        # plam
            ( \y2R y2I ->
                timesCPS
                    # rSquared
                    # y2R
                    # y2I
                    # yR
                    # yI
                    # plam
                        ( \y3R y3I ->
                            scaleCPS
                                # y3R
                                # y3I
                                # 8
                                # plam
                                    ( \newZR newZI ->
                                        plet (pmod # newZR # pupcast fieldMod) $ \newZReducedR ->
                                            plet (pmod # newZI # pupcast fieldMod) $ \newZReducedI ->
                                                pif
                                                    ((newZReducedR #+ newZReducedI) #== 0)
                                                    (callZero # k)
                                                    (go # fieldMod # rSquared # aR # aI # xR # xI # yR # yI # y2R # y2I # newZReducedR # newZReducedI # k)
                                    )
                        )
            )
  where
    go ::
        forall (r' :: S -> Type) (s' :: S).
        Term
            s'
            ( -- Field modulus
              PPositive
                :-->
                -- Irreducible
                PNatural
                :-->
                -- Curve A as pair
                PInteger
                :--> PInteger
                :-->
                -- X point as pair
                PInteger
                :--> PInteger
                :-->
                -- Y point as pair
                PInteger
                :--> PInteger
                :-->
                -- Y^2
                PInteger
                :--> PInteger
                :-->
                -- 8Y^3
                PInteger
                :--> PInteger
                :-->
                -- Continuation
                (PInteger :--> PInteger :--> PInteger :--> PInteger :--> PNatural :--> r')
                :--> r'
            )
    go = phoistAcyclic $ plam $ \fieldMod rSquared aR aI xR xI yR yI y2R y2I newZR newZI k ->
        squareCPS
            # rSquared
            # xR
            # xI
            # plam
                ( \x2R x2I ->
                    scaleCPS
                        # x2R
                        # x2I
                        # 3
                        # plam
                            ( \threeX2R threeX2I ->
                                addCPS
                                    # aR
                                    # aI
                                    # threeX2R
                                    # threeX2I
                                    # plam
                                        ( \bigAR bigAI ->
                                            squareCPS
                                                # rSquared
                                                # bigAR
                                                # bigAI
                                                # plam
                                                    ( \bigA2R bigA2I ->
                                                        timesCPS
                                                            # rSquared
                                                            # xR
                                                            # xI
                                                            # y2R
                                                            # y2I
                                                            # plam
                                                                ( \cR cI ->
                                                                    scaleCPS
                                                                        # cR
                                                                        # cI
                                                                        # (-8)
                                                                        # plam
                                                                            ( \neg8CR neg8CI ->
                                                                                addCPS
                                                                                    # bigA2R
                                                                                    # bigA2I
                                                                                    # neg8CR
                                                                                    # neg8CI
                                                                                    # plam
                                                                                        ( \bigDR bigDI ->
                                                                                            timesCPS
                                                                                                # rSquared
                                                                                                # yR
                                                                                                # yI
                                                                                                # bigDR
                                                                                                # bigDI
                                                                                                # plam
                                                                                                    ( \bdR bdI ->
                                                                                                        scaleCPS
                                                                                                            # bdR
                                                                                                            # bdI
                                                                                                            # 2
                                                                                                            # plam
                                                                                                                ( \newXR newXI ->
                                                                                                                    squareCPS
                                                                                                                        # rSquared
                                                                                                                        # y2R
                                                                                                                        # y2I
                                                                                                                        # plam
                                                                                                                            ( \y4R y4I ->
                                                                                                                                scaleCPS
                                                                                                                                    # y4R
                                                                                                                                    # y4I
                                                                                                                                    # (-8)
                                                                                                                                    # plam
                                                                                                                                        ( \newYRHSR newYRHSI ->
                                                                                                                                            scaleCPS
                                                                                                                                                # cR
                                                                                                                                                # cI
                                                                                                                                                # 4
                                                                                                                                                # plam
                                                                                                                                                    ( \fourCR fourCI ->
                                                                                                                                                        subCPS
                                                                                                                                                            # fourCR
                                                                                                                                                            # fourCI
                                                                                                                                                            # bigDR
                                                                                                                                                            # bigDI
                                                                                                                                                            # plam
                                                                                                                                                                ( \newYInnerLHSR newYInnerLHSI ->
                                                                                                                                                                    timesCPS
                                                                                                                                                                        # rSquared
                                                                                                                                                                        # bigAR
                                                                                                                                                                        # bigAI
                                                                                                                                                                        # newYInnerLHSR
                                                                                                                                                                        # newYInnerLHSI
                                                                                                                                                                        # plam
                                                                                                                                                                            ( \newYLHSR newYLHSI ->
                                                                                                                                                                                subCPS
                                                                                                                                                                                    # newYLHSR
                                                                                                                                                                                    # newYLHSI
                                                                                                                                                                                    # newYRHSR
                                                                                                                                                                                    # newYRHSI
                                                                                                                                                                                    # plam
                                                                                                                                                                                        ( \newYR newYI ->
                                                                                                                                                                                            divideCPS
                                                                                                                                                                                                # fieldMod
                                                                                                                                                                                                # rSquared
                                                                                                                                                                                                # newXR
                                                                                                                                                                                                # newXI
                                                                                                                                                                                                # newZR
                                                                                                                                                                                                # newZI
                                                                                                                                                                                                # plam
                                                                                                                                                                                                    ( \newXR' newXI' ->
                                                                                                                                                                                                        divideCPS
                                                                                                                                                                                                            # fieldMod
                                                                                                                                                                                                            # rSquared
                                                                                                                                                                                                            # newYR
                                                                                                                                                                                                            # newYI
                                                                                                                                                                                                            # newZR
                                                                                                                                                                                                            # newZI
                                                                                                                                                                                                            # plam
                                                                                                                                                                                                                ( \newYR' newYI' ->
                                                                                                                                                                                                                    k # newXR' # newXI' # newYR' # newYI' # pnatOne
                                                                                                                                                                                                                )
                                                                                                                                                                                                    )
                                                                                                                                                                                        )
                                                                                                                                                                            )
                                                                                                                                                                )
                                                                                                                                                    )
                                                                                                                                        )
                                                                                                                            )
                                                                                                                )
                                                                                                    )
                                                                                        )
                                                                            )
                                                                )
                                                    )
                                        )
                            )
                )

divideCPS ::
    forall (r :: S -> Type) (s :: S).
    Term
        s
        ( -- Field modulus
          PPositive
            :-->
            -- Irreducible :-->
            PNatural
            :-->
            -- Dividend as pair
            PInteger
            :--> PInteger
            :-->
            -- Divisor as pair
            PInteger
            :--> PInteger
            :-->
            -- Continuation
            (PInteger :--> PInteger :--> r)
            :--> r
        )
divideCPS = phoistAcyclic $ plam $ \fieldModulus rSquared u v x y k ->
    let recipExpr = (x #* x) #- (pupcast rSquared #* (y #* y))
        ux = u #* x
        yv = y #* v
        xv = x #* v
        uy = u #* y
     in plet (pexpModInteger # recipExpr # (-1) # pupcast fieldModulus) $ \recipr ->
            k # ((ux #- (5 #* yv)) #* recipr) # ((xv #- uy) #* recipr)

squareCPS ::
    forall (r :: S -> Type) (s :: S).
    Term
        s
        ( -- Irreducible
          PNatural
            :-->
            -- Point as pair
            PInteger
            :--> PInteger
            :-->
            -- Continuation
            (PInteger :--> PInteger :--> r)
            :--> r
        )
squareCPS = phoistAcyclic $ plam $ \rSquared xR xI k ->
    let xRSquared = xR #* xR
        xISquared = xI #* xI
        xRxI = xR #* xI
     in k # (xRSquared #+ (pupcast rSquared #* xISquared)) # (2 #* xRxI)

scaleCPS ::
    forall (r :: S -> Type) (s :: S).
    Term
        s
        ( -- Point as a pair
          PInteger
            :--> PInteger
            :-->
            -- Scalar
            PInteger
            :-->
            -- Continuation
            (PInteger :--> PInteger :--> r)
            :--> r
        )
scaleCPS = phoistAcyclic $ plam $ \xR xI scalar k ->
    let xRScaled = xR #* scalar
        xIScaled = xI #* scalar
     in k # xRScaled # xIScaled

addCPS ::
    forall (r :: S -> Type) (s :: S).
    Term
        s
        ( -- First point as pair
          PInteger
            :--> PInteger
            :-->
            -- Second point as pair
            PInteger
            :--> PInteger
            :-->
            -- Continuation
            (PInteger :--> PInteger :--> r)
            :--> r
        )
addCPS = phoistAcyclic $ plam $ \xR xI yR yI k ->
    let zR = xR #+ yR
        zI = xI #+ yI
     in k # zR # zI

subCPS ::
    forall (r :: S -> Type) (s :: S).
    Term
        s
        ( -- First point as pair
          PInteger
            :--> PInteger
            :-->
            -- Second point as pair
            PInteger
            :--> PInteger
            :-->
            -- Continuation
            (PInteger :--> PInteger :--> r)
            :--> r
        )
subCPS = phoistAcyclic $ plam $ \xR xI yR yI k ->
    let zR = xR #- yR
        zI = xI #- yI
     in k # zR # zI

timesCPS ::
    forall (r :: S -> Type) (s :: S).
    Term
        s
        ( -- Irreducible
          PNatural
            :-->
            -- First point as pair
            PInteger
            :--> PInteger
            :-->
            -- Second point as pair
            PInteger
            :--> PInteger
            :-->
            -- Continuation
            (PInteger :--> PInteger :--> r)
            :--> r
        )
timesCPS = phoistAcyclic $ plam $ \rSquared xR xI yR yI k ->
    let xRyR = xR #* yR
        imaginaryPart = (xR #* yI) #+ (xI #* yR)
        rest = pupcast rSquared #* (yR #* yI)
     in k # (xRyR #+ rest) # imaginaryPart
