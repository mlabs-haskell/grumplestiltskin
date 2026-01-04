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
    ptoPoint,

    -- ** Operations
    paddPoints,
    ppointDouble,
    pscalePoint,
    pinvPoint,
) where

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
    PPositive,
    PShow,
    PString,
    PTryFrom (ptryFrom'),
    pabs,
    pasConstr,
    pcon,
    pcond,
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
    runTermCont,
    tcont,
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
    = PECInfinityData
    | PECPointData
        (Term s (PAsData PNatural))
        (Term s (PAsData PNatural))
        (Term s (PAsData PPositive))
        (Term s (PAsData PInteger))
        (Term s (PAsData PInteger))
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
    ptryFrom' opq = runTermCont $ do
        p <- tcont $ plet (pasConstr # opq)
        PBuiltinPair tag fields <- tcont (pmatch p)
        let res =
                punsafeCase
                    tag
                    [ -- Point at infinity case
                      popaque opq
                    , -- Actual point case
                      popaque (go opq fields)
                    ]
        pure (punsafeCoerce res, ())
      where
        go :: forall (s :: S). Term s PData -> Term s (PBuiltinList PData) -> Term s PData
        go whole fields =
            -- Disassemble and decode all five components in order
            pheadTailBuiltin fields $ \x rest1 ->
                ptryFrom @(PAsData PNatural) x $ \(x', _) ->
                    pheadTailBuiltin rest1 $ \y rest2 ->
                        ptryFrom @(PAsData PNatural) y $ \(y', _) ->
                            pheadTailBuiltin rest2 $ \fieldOrder rest3 ->
                                ptryFrom @(PAsData PPositive) fieldOrder $ \(fieldOrder', _) ->
                                    pheadTailBuiltin rest3 $ \curveA rest4 ->
                                        ptryFrom @(PAsData PInteger) curveA $ \(curveA', _) ->
                                            plet (pheadBuiltin # rest4) $ \curveB ->
                                                ptryFrom @(PAsData PInteger) curveB $ \(curveB', _) ->
                                                    -- We will need the field order and `x` and `y` a
                                                    -- bunch.
                                                    plet (pfromData fieldOrder') $ \decodedFieldOrder ->
                                                        plet (pfromData x') $ \decodedX ->
                                                            plet (pfromData y') $ \decodedY ->
                                                                pcond
                                                                    [ (pupcast @PInteger decodedX #>= pupcast decodedFieldOrder, ptraceInfoError badX)
                                                                    , (pupcast @PInteger decodedY #>= pupcast decodedFieldOrder, ptraceInfoError badY)
                                                                    , (ponCurve decodedX decodedY decodedFieldOrder (pfromData curveA') (pfromData curveB'), whole)
                                                                    ]
                                                                    (ptraceInfoError notOnCurve)
        badX :: forall (s :: S). Term s PString
        badX = "PTryFrom PECPointData: Unsuitable X coordinate for given field order"
        badY :: forall (s :: S). Term s PString
        badY = "PTryFrom PECPointData: Unsuitable Y coordinate for given field order"
        notOnCurve :: forall (s :: S). Term s PString
        notOnCurve = "PTryFrom PECPointData: Specified point not on specified curve"
        ponCurve ::
            forall (s :: S).
            Term s PNatural ->
            Term s PNatural ->
            Term s PPositive ->
            Term s PInteger ->
            Term s PInteger ->
            Term s PBool
        ponCurve x y fieldOrder curveA curveB =
            let fieldOrder' = pupcast @PInteger fieldOrder
                rhs = pupcast (x #* (x #* x)) #+ ((curveA #* pupcast x) #+ curveB)
             in (pmod # pupcast (y #* y) # fieldOrder') #== (pmod # rhs # fieldOrder')

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
paddPoints ::
    forall (s :: S).
    Term s PPositive ->
    Term s PInteger ->
    Term s PECIntermediatePoint ->
    Term s PECIntermediatePoint ->
    Term s PECIntermediatePoint
paddPoints fieldModulus curveA point1 point2 = pmatch point1 $ \case
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
                            (ppointDouble fieldModulus curveA point1)
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
ppointDouble ::
    forall (s :: S).
    Term s PPositive ->
    Term s PInteger ->
    Term s PECIntermediatePoint ->
    Term s PECIntermediatePoint
ppointDouble fieldModulus curveA point = pmatch point $ \case
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

{- | @'pscalePoint' fieldOrder curveA scaleFactor p@ performs a scalar
multiplication of @p@ by @scaleFactor@, assuming that @p@ is defined over a
finite field of order @fieldOrder@, and that @p@'s curve has an @a@ constant
of @curveA@. In particular:

* @'pscalePoint' fieldOrder curveA 0 p@ yields the point at infinity;
* @'pscalePoint' fieldOrder curveA 1 p@ yields @p@;
* @'pscalePoint' fieldOrder curveA (-1) p@ yields @'pinvPoint' p@; and
* @'pscalePoint' fieldOrder curveA 2 p@ yields @'ppointDouble' fieldOrder curveA p@.

Furthermore, 'pscalePoint' obeys the following laws:

* @'pscalePoint' fieldOrder curveA (-n) = 'pinvPoint' ('pscalePoint' fieldOrder curveA n)@
* @'paddPoints' fo cA ('pscalePoint' fo cA n p) ('pscalePoint' fo cA m p) =
   'pscalePoint' fo cA (n #+ m) p@
* @'pscalePoint' fo cA m ('pscalePoint' fo cA n p) = 'pscalePoint' fo cA (n #* m) p@

@since 1.1.0
-}
pscalePoint ::
    forall (s :: S).
    Term s PPositive ->
    Term s PInteger ->
    Term s PInteger ->
    Term s PECIntermediatePoint ->
    Term s PECIntermediatePoint
pscalePoint fieldModulus curveA scaleFactor point =
    pcond
        [ (scaleFactor #== 0, pcon PECIntermediateInfinity)
        , (scaleFactor #<= 0, pinvPoint (go #$ pabs # scaleFactor))
        ]
        (go # scaleFactor)
  where
    go :: Term s (PInteger :--> PECIntermediatePoint)
    go = pfix $ \self -> plam $ \i ->
        pif
            (i #<= 1)
            point
            ( plet (self #$ pquot # i # 2) $ \below ->
                plet (ppointDouble fieldModulus curveA below) $ \doubled ->
                    pif
                        ((prem # i # 2) #== 1)
                        (paddPoints fieldModulus curveA doubled point)
                        doubled
            )

{- | Constructs the inverse of a point, such that for any @p@, @paddPoints
fieldOrder curveA p (pinvPoint p)@ is the point at infinity.

@since 1.1.0
-}
pinvPoint ::
    forall (s :: S).
    Term s PECIntermediatePoint ->
    Term s PECIntermediatePoint
pinvPoint point = pmatch point $ \case
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
