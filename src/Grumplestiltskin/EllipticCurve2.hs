{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Grumplestiltskin.EllipticCurve2 (
    -- * Types

    -- ** Haskell
    EC2Point,

    -- ** Plutarch
    PEC2Point,
    PEC2Intermediate,

    -- * Functions
    pec2FromElems,
    pec2OnCurve,
    pec2Double,
    pec2ToIntermediate,
    pec2FromIntermediate,
) where

import Data.Kind (Type)
import GHC.Generics (Generic)
import Generics.SOP qualified as SOP
import Grumplestiltskin.Degree2 (
    D2Element,
    PD2Element,
    PD2Intermediate,
    pd2Divide,
    pd2FromElem,
    pd2Square,
    pd2ToElem,
    pd2Zero,
 )
import Plutarch.Internal.Lift (PLifted (PLifted))
import Plutarch.Internal.PlutusType (PlutusType (PInner, pcon', pmatch'))
import Plutarch.Prelude (
    DeriveAsSOPStruct (DeriveAsSOPStruct),
    PAdditiveGroup (pscaleInteger, (#-)),
    PAdditiveSemigroup (pscalePositive, (#+)),
    PBool (PTrue),
    PDelayed,
    PEq,
    PInteger,
    PLiftable,
    PPositive,
    PShow,
    S,
    Term,
    pcon,
    pdelay,
    pforce,
    phoistAcyclic,
    pif,
    plam,
    plet,
    pmatch,
    pone,
    pscaleInteger,
    (#),
    (#*),
    (#+),
    (#-),
    (#==),
    (:-->),
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

-- | @since wip
newtype PEC2Intermediate (s :: S)
    = PEC2Intermediate
        ( forall (r :: S -> Type).
          Term
            s
            ( PPositive
                :--> PPositive
                :--> PD2Element
                :--> PDelayed r
                :--> (PD2Element :--> PD2Element :--> r)
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
            pcon $ PEC2Intermediate $ plam $ \fieldMod rSquared curveA whenInf whenNot ->
                k1
                    # fieldMod
                    # rSquared
                    # curveA
                    # pdelay (k2 # fieldMod # rSquared # curveA # whenInf # whenNot)
                    # plam
                        ( \x1 y1 ->
                            k2
                                # fieldMod
                                # rSquared
                                # curveA
                                # pdelay (k1 # fieldMod # rSquared # curveA # whenInf # whenNot)
                                # plam
                                    ( \x2 y2 ->
                                        plet (pd2FromElem x1) $ \x1' ->
                                            plet (pd2FromElem x2) $ \x2' ->
                                                plet (pd2FromElem y1) $ \y1' ->
                                                    plet (pd2FromElem y2) $ \y2' ->
                                                        let rSquared' = punsafeCoerce rSquared
                                                         in plet (y1' #- y2') $ \yDiff' ->
                                                                pif
                                                                    (x1 #== x2)
                                                                    ( pif
                                                                        (pd2ToElem rSquared' fieldMod yDiff' #== pd2Zero)
                                                                        -- Double
                                                                        (pec2Double' # fieldMod # rSquared # curveA # whenInf # whenNot # x1' # y1' # y1)
                                                                        -- Infinity
                                                                        (pforce whenInf)
                                                                    )
                                                                    -- Add
                                                                    ( plet (x1' #- x2') $ \xDiff' ->
                                                                        plet (pd2Divide yDiff' xDiff') $ \lambda ->
                                                                            plet (pd2Square lambda #- xDiff') $ \newX ->
                                                                                plet ((lambda #* (x1' #- newX)) #- y1') $ \newY ->
                                                                                    whenNot # pd2ToElem rSquared' fieldMod newX # pd2ToElem rSquared' fieldMod newY
                                                                    )
                                    )
                        )

-- | @since wip
pec2ToIntermediate ::
    forall (s :: S).
    Term s PEC2Point ->
    Term s PEC2Intermediate
pec2ToIntermediate p = pmatch p $ \case
    PEC2Infinity -> pcon $ PEC2Intermediate $ plam $ \_ _ _ whenInf _ -> pforce whenInf
    PEC2Point x y -> pcon $ PEC2Intermediate $ plam $ \_ _ _ _ whenNot -> whenNot # x # y

-- | @since wip
pec2FromIntermediate ::
    forall (s :: S).
    Term s PPositive ->
    Term s PPositive ->
    Term s PD2Element ->
    Term s PEC2Intermediate ->
    Term s PEC2Point
pec2FromIntermediate fieldMod rSquared curveA p = pmatch p $ \(PEC2Intermediate k) ->
    k # fieldMod # rSquared # curveA # pdelay (pcon PEC2Infinity) # plam (\x -> pcon . PEC2Point x)

-- | @since wip
pec2Double ::
    forall (s :: S).
    Term s PEC2Intermediate -> Term s PEC2Intermediate
pec2Double t = pmatch t $ \(PEC2Intermediate k1) ->
    pcon $ PEC2Intermediate $ plam $ \fieldMod rSquared curveA whenInf whenNot ->
        k1
            # fieldMod
            # rSquared
            # curveA
            # whenInf
            # plam
                ( \x y ->
                    pec2Double' # fieldMod # rSquared # curveA # whenInf # whenNot # pd2FromElem x # pd2FromElem y # y
                )

-- Helpers

pec2Double' ::
    forall (r :: S -> Type) (s :: S).
    Term
        s
        ( -- Field modulus
          PPositive
            :-->
            -- Irreducible
            PPositive
            :-->
            -- Curve A constant
            PD2Element
            :-->
            -- Point at infinity continuation
            PDelayed r
            :-->
            -- Regular point continuation
            (PD2Element :--> PD2Element :--> r)
            :-->
            -- X
            PD2Intermediate
            :-->
            -- Y
            PD2Intermediate
            :-->
            -- Y in reduced form
            PD2Element
            :--> r
        )
pec2Double' = phoistAcyclic $ plam $ \fieldMod rSquared curveA whenInf whenNot x' y' y ->
    pif
        (y #== pd2Zero)
        (pforce whenInf)
        ( let posTwo = punsafeCoerce @_ @PInteger 2
              posThree = punsafeCoerce @_ @PInteger 3
              topOfLambda = pscalePositive (pd2Square x') posThree #+ pd2FromElem curveA
           in plet (pd2Divide topOfLambda (pscalePositive y' posTwo)) $ \lambda ->
                plet (pd2Square lambda #- pscalePositive x' posTwo) $ \newX ->
                    let newY = (lambda #* (x' #- newX)) #- y'
                        rSquared' = punsafeCoerce rSquared
                     in whenNot # pd2ToElem rSquared' fieldMod newX # pd2ToElem rSquared' fieldMod newY
        )
