{-# LANGUAGE ImpredicativeTypes #-}

module Grumplestiltskin.Degree2.EllipticCurveID (
    -- * Types

    -- ** Plutarch
    PEC2Intermediate,

    -- * Functions
    pec2Double,
    pec2ToIntermediate,
    pec2FromIntermediate,
) where

import Data.Kind (Type)
import Grumplestiltskin.Degree2.AffinePoint (PEC2Point (PEC2Infinity, PEC2Point))
import Grumplestiltskin.Degree2.Element (
    PD2Element,
    pd2Zero,
 )
import Grumplestiltskin.Degree2.GaloisDirect (
    PD2Intermediate,
    pd2Divide,
    pd2FromElem,
    pd2Square,
    pd2Times,
    pd2ToElem,
 )
import Plutarch.Internal.Case (punsafeCase)
import Plutarch.Internal.PlutusType (PlutusType (PInner, pcon', pmatch'))
import Plutarch.Prelude (
    PAdditiveGroup (pnegate, (#-)),
    PAdditiveMonoid (pzero),
    PAdditiveSemigroup (pscalePositive, (#+)),
    PDelayed,
    PInteger,
    PPositive,
    S,
    Term,
    pcon,
    pdelay,
    pfix,
    pforce,
    phoistAcyclic,
    pif,
    plam,
    plet,
    pmatch,
    popaque,
    pquot,
    prem,
    pupcast,
    (#),
    (#$),
    (#+),
    (#-),
    (#==),
    (:-->),
 )
import Plutarch.Unsafe (punsafeCoerce)

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
                                                        plet (y1' #- y2') $ \yDiff' ->
                                                            pif
                                                                (x1 #== x2)
                                                                ( pif
                                                                    (pd2ToElem fieldMod yDiff' #== pd2Zero)
                                                                    (pec2Double' # fieldMod # rSquared # curveA # whenInf # whenNot # x1' # y1' # y1)
                                                                    (pforce whenInf)
                                                                )
                                                                ( plet (pd2Divide fieldMod rSquared yDiff' (x1' #- x2')) $ \lambda ->
                                                                    plet ((pd2Square rSquared lambda #- x1') #- x2') $ \newX ->
                                                                        let newY = pd2Times rSquared lambda (x1' #- newX) #- y1'
                                                                         in whenNot # pd2ToElem fieldMod newX # pd2ToElem fieldMod newY
                                                                )
                                    )
                        )
    pscalePositive t p = go # t # pupcast p
      where
        go :: forall (s :: S). Term s (PEC2Intermediate :--> PInteger :--> PEC2Intermediate)
        go = phoistAcyclic $ pfix $ \self -> plam $ \t' p' -> pmatch t' $ \(PEC2Intermediate k1) ->
            pcon $ PEC2Intermediate $ plam $ \fieldMod rSquared curveA whenInf whenNot ->
                k1
                    # fieldMod
                    # rSquared
                    # curveA
                    # whenInf
                    # plam
                        ( \x y ->
                            pif
                                (p' #== 1)
                                (whenNot # x # y)
                                ( plet (pec2Double (self # t' #$ pquot # p' # 2)) $ \doubled ->
                                    punsafeCase
                                        (prem # p' # 2)
                                        [ popaque $ pmatch doubled $ \(PEC2Intermediate k2) ->
                                            k2 # fieldMod # rSquared # curveA # whenInf # whenNot
                                        , popaque $ pmatch (doubled #+ t') $ \(PEC2Intermediate k2) ->
                                            k2 # fieldMod # rSquared # curveA # whenInf # whenNot
                                        ]
                                )
                        )

-- | @since wip
instance PAdditiveMonoid PEC2Intermediate where
    pzero = pcon $ PEC2Intermediate $ plam $ \_ _ _ whenInf _ -> pforce whenInf

-- | @since wip
instance PAdditiveGroup PEC2Intermediate where
    pnegate = phoistAcyclic $ plam $ \t -> pmatch t $ \(PEC2Intermediate k1) ->
        pcon $ PEC2Intermediate $ plam $ \fieldMod rSquared curveA whenInf whenNot ->
            k1
                # fieldMod
                # rSquared
                # curveA
                # whenInf
                # plam
                    ( \x y ->
                        whenNot # x # pd2ToElem fieldMod (pnegate # pd2FromElem y)
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
              topOfLambda = pscalePositive (pd2Square rSquared x') posThree #+ pd2FromElem curveA
           in plet (pd2Divide fieldMod rSquared topOfLambda (pscalePositive y' posTwo)) $ \lambda ->
                plet (pd2Square rSquared lambda #- pscalePositive x' posTwo) $ \newX ->
                    let newY = pd2Times rSquared lambda (x' #- newX) #- y'
                     in whenNot # pd2ToElem fieldMod newX # pd2ToElem fieldMod newY
        )
