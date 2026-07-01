{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Grumplestiltskin.Degree2.EllipticCurveDI (
    -- * Types

    -- ** Plutarch
    PEC2Intermediate (..),

    -- * Functions
    pec2Double,
    pec2Add,
    pec2ToIntermediate,
    pec2FromIntermediate,
    pec2Negate,
    pec2Scale,
) where

import GHC.Generics (Generic)
import Generics.SOP qualified as SOP
import Grumplestiltskin.Degree2.AffinePoint (PEC2Point (PEC2Infinity, PEC2Point))
import Grumplestiltskin.Degree2.Element (
    PD2Element,
    pd2Zero,
 )
import Grumplestiltskin.Degree2.Galois (
    PD2Intermediate,
    pd2Divide,
    pd2FromElem,
    pd2Square,
    pd2ToElem,
 )
import Plutarch.Internal.Case (punsafeCase)
import Plutarch.Prelude (
    DeriveAsSOPStruct (DeriveAsSOPStruct),
    PAdditiveGroup (pnegate, (#-)),
    PAdditiveSemigroup (pscalePositive, (#+)),
    PInteger,
    PNatural,
    PPositive,
    PlutusType,
    S,
    Term,
    pcon,
    pcond,
    pfix,
    phoistAcyclic,
    pif,
    plam,
    plet,
    pmatch,
    popaque,
    pquot,
    prem,
    (#),
    (#$),
    (#*),
    (#+),
    (#-),
    (#<=),
    (#==),
    (:-->),
 )
import Plutarch.Unsafe (punsafeCoerce)

-- | @since wip
data PEC2Intermediate (s :: S)
    = PEC2InfinityI
    | PEC2PointI (Term s PD2Intermediate) (Term s PD2Intermediate)
    deriving stock
        ( -- | @since wip
          Generic
        )
    deriving anyclass
        ( -- | @since wip
          SOP.Generic
        )
    deriving
        ( -- | @since wip
          PlutusType
        )
        via (DeriveAsSOPStruct PEC2Intermediate)

-- | @since wip
pec2ToIntermediate ::
    forall (s :: S).
    Term s PEC2Point ->
    Term s PEC2Intermediate
pec2ToIntermediate t = pmatch t $ \case
    PEC2Infinity -> pcon PEC2InfinityI
    PEC2Point x y -> pcon . PEC2PointI (pd2FromElem x) . pd2FromElem $ y

-- | @since wip
pec2FromIntermediate ::
    forall (s :: S).
    Term s PPositive ->
    Term s PNatural ->
    Term s PEC2Intermediate ->
    Term s PEC2Point
pec2FromIntermediate fieldMod rSquared t = pmatch t $ \case
    PEC2InfinityI -> pcon PEC2Infinity
    PEC2PointI x y -> pcon . PEC2Point (pd2ToElem rSquared fieldMod x) . pd2ToElem rSquared fieldMod $ y

-- | @since wip
pec2Add ::
    forall (s :: S).
    Term s PPositive ->
    Term s PNatural ->
    Term s PD2Element ->
    Term s PEC2Intermediate ->
    Term s PEC2Intermediate ->
    Term s PEC2Intermediate
pec2Add fieldMod rSquared curveA t1 t2 = pmatch t1 $ \case
    PEC2InfinityI -> t2
    PEC2PointI x1 y1 -> pmatch t2 $ \case
        PEC2InfinityI -> t1
        PEC2PointI x2 y2 -> plet (pd2ToElem rSquared fieldMod x1) $ \x1' ->
            plet (pd2ToElem rSquared fieldMod x2) $ \x2' ->
                plet (y1 #- y2) $ \yDiff ->
                    pif
                        (x1' #== x2')
                        ( pif
                            (pd2ToElem rSquared fieldMod yDiff #== pd2Zero)
                            -- Double
                            (pec2Double' # fieldMod # rSquared # curveA # x1 # y1)
                            -- Infinity
                            (pcon PEC2InfinityI)
                        )
                        -- Add normally
                        ( plet (pd2Divide yDiff (x1 #- x2)) $ \lambda ->
                            plet ((pd2Square lambda #- x1) #- x2) $ \newX ->
                                pcon . PEC2PointI newX $ (lambda #* (x1 #- newX)) #- y1
                        )

-- | @since wip
pec2Double ::
    forall (s :: S).
    Term s PPositive ->
    Term s PNatural ->
    Term s PD2Element ->
    Term s PEC2Intermediate ->
    Term s PEC2Intermediate
pec2Double fieldMod rSquared curveA t = pmatch t $ \case
    PEC2InfinityI -> pcon PEC2InfinityI
    PEC2PointI x y -> pec2Double' # fieldMod # rSquared # curveA # x # y

-- | @since wip
pec2Negate ::
    forall (s :: S).
    Term s PEC2Intermediate ->
    Term s PEC2Intermediate
pec2Negate t = pmatch t $ \case
    PEC2InfinityI -> t
    PEC2PointI x y -> pcon . PEC2PointI x $ pnegate # y

-- | @since wip
pec2Scale ::
    forall (s :: S).
    Term s PPositive ->
    Term s PNatural ->
    Term s PD2Element ->
    Term s PEC2Intermediate ->
    Term s PInteger ->
    Term s PEC2Intermediate
pec2Scale fieldMod rSquared curveA t e = pmatch t $ \case
    PEC2InfinityI -> t
    PEC2PointI _ _ ->
        pcond
            [ (e #== 0, pcon PEC2InfinityI)
            , (e #<= (-1), pec2Negate $ pec2Scale' # fieldMod # rSquared # curveA # t #$ pnegate # e)
            ]
            (pec2Scale' # fieldMod # rSquared # curveA # t # e)

-- Helpers

pec2Double' ::
    forall (s :: S).
    Term
        s
        ( PPositive
            :--> PNatural
            :--> PD2Element
            :--> PD2Intermediate
            :--> PD2Intermediate
            :--> PEC2Intermediate
        )
pec2Double' = phoistAcyclic $ plam $ \fieldMod rSquared curveA x y ->
    pif
        (pd2ToElem rSquared fieldMod y #== pd2Zero)
        (pcon PEC2InfinityI)
        ( let posTwo = punsafeCoerce @_ @PInteger 2
              posThree = punsafeCoerce @_ @PInteger 3
              topOfLambda = pscalePositive (pd2Square x) posThree #+ pd2FromElem curveA
           in plet (pd2Divide topOfLambda (pscalePositive y posTwo)) $ \lambda ->
                plet (pd2Square lambda #- pscalePositive x posTwo) $ \newX ->
                    let newY = (lambda #* (x #- newX)) #- y
                     in pcon . PEC2PointI newX $ newY
        )

pec2Scale' ::
    forall (s :: S).
    Term
        s
        ( PPositive
            :--> PNatural
            :--> PD2Element
            :--> PEC2Intermediate
            :--> PInteger
            :--> PEC2Intermediate
        )
pec2Scale' = phoistAcyclic $ pfix $ \self -> plam $ \fieldMod rSquared curveA t e ->
    pif
        (e #== 1)
        t
        ( plet (pec2Double fieldMod rSquared curveA (self # fieldMod # rSquared # curveA # t #$ pquot # e # 2)) $ \doubled ->
            punsafeCase
                (prem # e # 2)
                [ popaque doubled
                , popaque $ pec2Add fieldMod rSquared curveA doubled t
                ]
        )
