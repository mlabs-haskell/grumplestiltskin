{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

{- | Elliptic curves over finite fields. The general formula for these functions
is @y^2 = x^3 + ax + b (mod r)@, where @r@ is the field order.

@since 1.1.0
-}
module Grumplestiltskin.EllipticCurve (
    -- * Types

    -- ** Plutarch

    -- *** @Data@ encoded
    PECPointData,

    -- *** SOP encoded
    PECPoint (PECPoint, PECInfinity),
    PECIntermediatePoint (PECIntermediatePoint, PECIntermediateInfinity),

    -- * Functions

    --

    -- ** Representation change
    pecFromData,
    pecToData,

    -- ** Operations
    pecAdd,
    pecDouble,
    pecScale,
    pecInvert,

    -- ** FInalizing computations
    ptoPoint,
) where

import Data.Kind (Type)
import GHC.Generics (Generic)
import Generics.SOP qualified as SOP
import Grumplestiltskin.Galois (PGFElement, PGFIntermediate, pgfFromElem, pgfRecip, pgfToElem, pgfZero)
import Plutarch.Internal.Case (punsafeCase)
import Plutarch.Internal.PlutusType (PlutusType, pmatch)
import Plutarch.Internal.Term (S, Term, plet, punsafeCoerce)
import Plutarch.Prelude (
    DeriveAsDataStruct (DeriveAsDataStruct),
    PAsData,
    PBool,
    PBuiltinList,
    PBuiltinPair (PBuiltinPair),
    PData,
    PEq,
    PInteger,
    PIsData,
    PNatural,
    POpaque,
    PPositive,
    PShow,
    PString,
    PTryFrom (ptryFrom'),
    pabs,
    pasConstr,
    pcon,
    pcond,
    pdata,
    pfix,
    pfromData,
    pheadBuiltin,
    pheadTailBuiltin,
    pif,
    plam,
    pmod,
    pnegate,
    popaque,
    pquot,
    prem,
    ptraceInfoError,
    ptryFrom,
    pupcast,
    (#),
    (#$),
    (#*),
    (#+),
    (#-),
    (#<=),
    (#==),
    (#>=),
    (:-->),
 )
import Plutarch.Repr.SOP (DeriveAsSOPStruct (DeriveAsSOPStruct))

{-
Calculators:
- "https://www.graui.de/code/elliptic2/"
- "https://andrea.corbellini.name/ecc/interactive/modk-add.html"

Resources:
- "https://www.secg.org/sec1-v2.pdf"
- "https://rareskills.io/post/elliptic-curves-finite-fields"
- Handbook of Elliptic and Hyperelliptic Curve Cryptography -- Henri Cohen, ...
- "http://koclab.cs.ucsb.edu/teaching/ecc/eccPapers/Washington-ch04.pdf" (some examples and proofs)
- "https://andrea.corbellini.name/2015/05/17/elliptic-curve-cryptography-a-gentle-introduction/"

Functionality of Elliptic curve over finite field. (cyclic groups)

curve order = number of points on the curve (including point in infinity)
field modulus = is the modulo we apply to the values

## Functions

-- Doing P + Q
-- This should be able to return point at infinity
addPoints :: Point -> Point -> Point

-- Doing 2P
doublePoint :: Point -> Point

-- P being the point
-- k being the number of times we add `P` to itself. I.e. 3P = P + P + P
-- this function calculates the kP
mulPoint :: Integer -> Point -> Point

-- Vertical symmetry
-- x axis stays the same, and y is inversed using modulo, i.e. P.y + inv(P).y == field modulus
invPoint :: Point -> Point

## Tests
Some tests may not be feasible since we don't know the curve's order.

Associativity `(aP + bP) + cP == aP + (bP + cP)`
Inverse `P + inv(P) = Identity`
`doublePoint(P) == P + P`
`xP == (x + k)P` when k is the order of the curve
`(a + b % curve_order)P == aP + bP` (since we don't know curve order we should pick sufficiently small numbers)
`invPoint P == P` when P is identity (in case we represent identity in some special way)

## Notes

From the resource:
> What about optimized_bn128?

Examining the library, you will see an implementation called optimized_bn128.
If you benchmark the execution time, you will see this version runs much quicker,
and it is the implementation used by pyEvm. For educational purposes however,
it is preferable to use the non-optimized version as it structures the points in a more intuitive way (the usual x, y tuple).
The optimized version structures EC points as 3-tuples, which are harder to interpret.

13.2 section in Handbook of Elliptic and Hyperelliptic Curve Cryptography -- Henri Cohen
-}

{- | @Data@-encoded point on some elliptic curve, represented as a combination
of:

* The point's @x@ and @y@ co-ordinates, as elements of some finite field;
* The order of the field used to define those co-ordinates; and
* The curve's @A@ and @B@ constants.

This type is primarily designed as an exchange format (such as for use in
datums); to do any work with such points, we recommend first converting to
'PECPoint' using 'pecFromData'.

@since 1.1.0
-}
data PECPointData (s :: S)
    = -- Note (Koz, 5/1/2026): We order the fields in this rather odd way, as it
      -- allows us to speculatively decode (or validate) the field order and
      -- curve constants before we even check what tag we have. This would
      -- _ideally_ be done by factoring the curve information into a separate
      -- data type, but that would make the encoding larger due to list nesting.
      PECInfinityData
        (Term s (PAsData PPositive))
        (Term s (PAsData PInteger))
        (Term s (PAsData PInteger))
    | PECPointData
        (Term s (PAsData PPositive))
        (Term s (PAsData PInteger))
        (Term s (PAsData PInteger))
        (Term s (PAsData PNatural))
        (Term s (PAsData PNatural))
    deriving stock
        ( -- | @since 1.1.0
          Generic
        )
    deriving anyclass
        ( -- | @since 1.1.0
          SOP.Generic
        , -- | @since 1.1.0
          PIsData
        )

-- | @since 1.1.0
deriving via (DeriveAsDataStruct PECPointData) instance PlutusType PECPointData

{- | This instance validates. Specifically, it will check the following:

  1. Whether the @x@ and @y@ coordinates of the provided point are smaller than
     the field order; and
  2. Whether the point @(x, y)@ is on the curve as specified by the field
     order and the @A@ and @B@ constants.

@since 1.1.0
-}
instance PTryFrom PData (PAsData PECPointData) where
    ptryFrom' ::
        forall (s :: S) (r :: S -> Type).
        Term s PData ->
        ((Term s (PAsData PECPointData), ()) -> Term s r) ->
        Term s r
    ptryFrom' opq k = pmatch (pasConstr # opq) $ \(PBuiltinPair tag fields) ->
        -- As we know that in any valid case, the first three fields are
        -- identical, we speculatively validate them right now.
        pheadTailBuiltin fields $ \fieldOrder' rest1 ->
            ptryFrom @(PAsData PPositive) fieldOrder' $ \(fieldOrder, _) ->
                pheadTailBuiltin rest1 $ \curveA' rest2 ->
                    ptryFrom @(PAsData PInteger) curveA' $ \(curveA, _) ->
                        pheadTailBuiltin rest2 $ \curveB' rest3 ->
                            ptryFrom @(PAsData PInteger) curveB' $ \(curveB, _) ->
                                -- Now check the tag, and further 'unwind' the fields if
                                -- needed.
                                k
                                    ( punsafeCase
                                        tag
                                        [ popaque opq
                                        , go (pfromData fieldOrder) (pfromData curveA) (pfromData curveB) rest3
                                        ]
                                    , ()
                                    )
      where
        go ::
            Term s PPositive ->
            Term s PInteger ->
            Term s PInteger ->
            Term s (PBuiltinList PData) ->
            Term s POpaque
        go fieldOrder curveA curveB rest = pheadTailBuiltin rest $ \x' rest' ->
            ptryFrom @(PAsData PNatural) x' $ \(x, _) ->
                plet (pheadBuiltin # rest') $ \y' ->
                    ptryFrom @(PAsData PNatural) y' $ \(y, _) ->
                        plet (pfromData x) $ \decodedX ->
                            plet (pfromData y) $ \decodedY ->
                                pcond
                                    [ (pupcast @PInteger decodedX #>= pupcast fieldOrder, ptraceInfoError badX)
                                    , (pupcast @PInteger decodedY #>= pupcast fieldOrder, ptraceInfoError badY)
                                    , (ponCurve decodedX decodedY fieldOrder curveA curveB, popaque opq)
                                    ]
                                    (ptraceInfoError notOnCurve)
        badX :: Term s PString
        badX = "PTryFrom PECPointData: Unsuitable X coordinate for given field order"
        badY :: Term s PString
        badY = "PTryFrom PECPointData: Unsuitable Y coordinate for given field order"
        notOnCurve :: Term s PString
        notOnCurve = "PTryFrom PECPointData: Specified point not on specified curve"
        ponCurve ::
            Term s PNatural ->
            Term s PNatural ->
            Term s PPositive ->
            Term s PInteger ->
            Term s PInteger ->
            Term s PBool
        ponCurve x y fieldOrder curveA curveB =
            let fieldOrder' = pupcast @PInteger fieldOrder
             in plet (pupcast (x #* x)) $ \xSquared ->
                    let rhs = (pupcast x #* xSquared) #+ ((curveA #* xSquared) #+ curveB)
                     in (pmod # pupcast (y #* y) # fieldOrder') #== (pmod # rhs # fieldOrder')

-- | @since 1.1.0
pecFromData ::
    forall (r :: S -> Type) (s :: S).
    Term s PECPointData ->
    (Term s PECPoint -> Term s PPositive -> Term s PInteger -> Term s PInteger -> Term s r) ->
    Term s r
pecFromData x f = pmatch x $ \case
    PECInfinityData fieldOrder curveA curveB -> f (pcon PECInfinity) (pfromData fieldOrder) (pfromData curveA) (pfromData curveB)
    -- Note (Koz, 5/1/2026): The `punsafeCoerce`ing is safe here, because we know
    -- that the `PNatural`s have been reduced already.
    PECPointData fieldOrder curveA curveB pointX pointY ->
        f (pcon $ PECPoint (punsafeCoerce $ pfromData pointX) (punsafeCoerce $ pfromData pointY)) (pfromData fieldOrder) (pfromData curveA) (pfromData curveB)

-- | @since 1.1.0
pecToData ::
    forall (s :: S).
    Term s PECPoint ->
    Term s PPositive ->
    Term s PInteger ->
    Term s PInteger ->
    Term s PECPointData
pecToData p fieldOrder curveA curveB = pmatch p $ \case
    PECPoint x y -> pcon . PECPointData (pdata fieldOrder) (pdata curveA) (pdata curveB) (pdata $ punsafeCoerce x) . pdata . punsafeCoerce $ y
    PECInfinity -> pcon . PECInfinityData (pdata fieldOrder) (pdata curveA) . pdata $ curveB

{- | A point on some elliptic curve. The order of the field for the @x@ and @y@
co-ordinates of the curve point is implicit, for reasons of efficiency.

@since 1.1.0
-}
data PECPoint (s :: S)
    = PECPoint (Term s PGFElement) (Term s PGFElement)
    | PECInfinity
    deriving stock
        ( -- | @since 1.1.0
          Generic
        )
    deriving anyclass
        ( -- | @since 1.1.0
          SOP.Generic
        , -- | @since 1.1.0
          PEq
        , -- | @since 1.1.0
          PShow
        )
    deriving
        ( -- | @since 1.1.0
          PlutusType
        )
        via (DeriveAsSOPStruct PECPoint)

{- | An intermediate computation over an elliptic curve point. This type exists
for efficiency: thus, you want to do all your calculations in
'PECIntermediatePoint', then convert to 'PECPoint' at the end.

@since 1.1.0
-}
data PECIntermediatePoint (s :: S)
    = PECIntermediatePoint (Term s PGFIntermediate) (Term s PGFIntermediate)
    | PECIntermediateInfinity
    deriving stock
        ( -- | @since 1.1.0
          Generic
        )
    deriving anyclass
        ( -- | @since 1.1.0
          SOP.Generic
        )
    deriving
        ( -- | @since 1.1.0
          PlutusType
        )
        via (DeriveAsSOPStruct PECIntermediatePoint)

{- | Convert a 'PECIntermediatePoint' into a valid point on an elliptic curve,
based on a finite field of order specified by the 'PPositive' argument. Said
argument should be prime, although 'ptoPoint' doesn't require this.

@since 1.1.0
-}
ptoPoint ::
    forall (s :: S).
    Term s PPositive -> Term s PECIntermediatePoint -> Term s PECPoint
ptoPoint fieldModulus p = pmatch p $ \case
    PECIntermediateInfinity -> pcon PECInfinity
    PECIntermediatePoint x y -> pcon $ PECPoint (pgfToElem x fieldModulus) (pgfToElem y fieldModulus)

{- | Add two elliptic curve points, where both points are based on a finite
field of order specified by the 'PPositive' argument, with the curve having
an @a@ constant specified by the 'PInteger' argument.

More precisely, adding points @P@ and @Q@ produces the point @R@ such that
@R@ is the inverse of a point on the intersection of the curve and the line
through @P@ and @Q@. If @P = Q@, we instead calculate @2P@.

@since 1.1.0
-}
pecAdd ::
    forall (s :: S).
    Term s PPositive ->
    Term s PInteger ->
    Term s PECIntermediatePoint ->
    Term s PECIntermediatePoint ->
    Term s PECIntermediatePoint
pecAdd fieldModulus curveA point1 point2 = pmatch point1 $ \case
    -- Point at infinity is an identity for addition
    PECIntermediateInfinity -> point2
    PECIntermediatePoint point1X point1Y -> pmatch point2 $ \case
        PECIntermediateInfinity -> point1
        PECIntermediatePoint point2X point2Y ->
            plet (point1Y #- point2Y) $ \yDiff ->
                plet (point1X #- point2X) $ \xDiff ->
                    pif
                        (pgfToElem xDiff fieldModulus #== pgfZero)
                        ( pif
                            (pgfToElem yDiff fieldModulus #== pgfZero)
                            -- If both points are equal, we double the first one
                            (pecDouble fieldModulus curveA point1)
                            -- If both points have X = 0 but different Y, their sum is
                            -- the point at infinity
                            (pcon PECIntermediateInfinity)
                        )
                        ( -- Note (Koz, 18/12/2025): We force a reduction here,
                          -- as `lambda` is likely to be a huge term, and will
                          -- only get huger later. This forced reduction
                          -- massively improves exunit costs.
                          plet (preduce fieldModulus (yDiff #* pgfFromElem (pgfRecip # xDiff # fieldModulus))) $ \lambda ->
                            plet (((lambda #* lambda) #- point1X) #- point2X) $ \point3X ->
                                pcon . PECIntermediatePoint point3X $ (lambda #* (point1X #- point3X)) #- point1Y
                        )

{- | Double an elliptic curve point, where the point is based on a finite field
of order specified by the 'PPositive' argument, with the curve having an @a@
constant specified by the 'PInteger' argument.

More precisely, for a point @P@, this calculates @2P = R@ such that @R@ is
the inverse of a point at the intersection of a tangent to @P@ and the curve
itself.

@since 1.1.0
-}
pecDouble ::
    forall (s :: S).
    Term s PPositive ->
    Term s PInteger ->
    Term s PECIntermediatePoint ->
    Term s PECIntermediatePoint
pecDouble fieldModulus curveA point = pmatch point $ \case
    PECIntermediateInfinity -> pcon PECIntermediateInfinity
    PECIntermediatePoint pointX pointY -> plet (pgfToElem pointY fieldModulus) $ \pointYReduced ->
        pif
            (pointYReduced #== pgfZero)
            (pcon PECIntermediateInfinity)
            ( let lambdaNum = (pgf3 #* (pointX #* pointX)) #+ punsafeCoerce curveA
                  lambdaDen = pgfFromElem $ pgfRecip # (pgf2 #* pgfFromElem pointYReduced) # fieldModulus
               in -- Note (Koz, 18/12/2025): We force a reduction here, as
                  -- `lambda` is likely to be a huge term, which only gets huger
                  -- later. This massively reduces the cost in exunits for
                  -- doubling operations, especially when scaling becomes
                  -- involved.
                  plet (preduce fieldModulus (lambdaNum #* lambdaDen)) $ \lambda ->
                    let newPointX = (lambda #* lambda) #- (pgf2 #* pointX)
                        newPointY = (lambda #* (pointX #- newPointX)) #- pgfFromElem pointYReduced
                     in pcon . PECIntermediatePoint newPointX $ newPointY
            )

{- | @'pecScale' fieldOrder curveA scaleFactor p@ performs a scalar
multiplication of @p@ by @scaleFactor@, assuming that @p@ is defined over a
finite field of order @fieldOrder@, and that @p@'s curve has an @a@ constant
of @curveA@. In particular:

* @'pecScale' fieldOrder curveA 0 p@ yields the point at infinity;
* @'pecScale' fieldOrder curveA 1 p@ yields @p@;
* @'pecScale' fieldOrder curveA (-1) p@ yields @'pecInvert' p@; and
* @'pecScale' fieldOrder curveA 2 p@ yields @'pecDouble' fieldOrder curveA p@.

Furthermore, 'pecScale' obeys the following laws:

* @'pecScale' fieldOrder curveA (-n) = 'pecInvert' ('pecScale' fieldOrder curveA n)@
* @'pecAdd' fo cA ('pecScale' fo cA n p) ('pecScale' fo cA m p) =
   'pecScale' fo cA (n #+ m) p@
* @'pecScale' fo cA m ('pecScale' fo cA n p) = 'pecScale' fo cA (n #* m) p@

@since 1.1.0
-}
pecScale ::
    forall (s :: S).
    Term s PPositive ->
    Term s PInteger ->
    Term s PInteger ->
    Term s PECIntermediatePoint ->
    Term s PECIntermediatePoint
pecScale fieldModulus curveA scaleFactor point =
    pcond
        [ (scaleFactor #== 0, pcon PECIntermediateInfinity)
        , (scaleFactor #<= 0, pecInvert (go #$ pabs # scaleFactor))
        ]
        (go # scaleFactor)
  where
    go :: Term s (PInteger :--> PECIntermediatePoint)
    go = pfix $ \self -> plam $ \i ->
        pif
            (i #<= 1)
            point
            ( plet (self #$ pquot # i # 2) $ \below ->
                plet (pecDouble fieldModulus curveA below) $ \doubled ->
                    pif
                        ((prem # i # 2) #== 1)
                        (pecAdd fieldModulus curveA doubled point)
                        doubled
            )

{- | Constructs the inverse of a point, such that for any @p@, @pecAdd
fieldOrder curveA p (pecInvert p)@ is the point at infinity.

@since 1.1.0
-}
pecInvert ::
    forall (s :: S).
    Term s PECIntermediatePoint ->
    Term s PECIntermediatePoint
pecInvert point = pmatch point $ \case
    PECIntermediateInfinity -> pcon PECIntermediateInfinity
    PECIntermediatePoint x y -> pcon $ PECIntermediatePoint x (pnegate # y)

-- Helpers

-- The constant @2@
pgf2 :: Term s PGFIntermediate
pgf2 = punsafeCoerce (2 :: Term s PInteger)

-- The constant @3@
pgf3 :: Term s PGFIntermediate
pgf3 = punsafeCoerce (3 :: Term s PInteger)

-- Force a reduction by field modulus
preduce :: forall (s :: S). Term s PPositive -> Term s PGFIntermediate -> Term s PGFIntermediate
preduce modulus p = pgfFromElem $ pgfToElem p modulus
