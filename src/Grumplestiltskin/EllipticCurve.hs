{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

{- | A general implementation for elliptic curves over finite field.

The general formula for these functions is: @y^2 = x^3 + a * x + b (mod r)@.
-}
module Grumplestiltskin.EllipticCurve (
    paddPoints,
    ppointDouble,
    ptoPoint,
    pscalePoint,
    invPoint,
    PECIntermediatePoint (PECIntermediatePoint, PECIntermediateInfinity),
    PECPoint (PECPoint, PECInfinity),
) where

import GHC.Generics (Generic)
import Generics.SOP qualified as SOP
import Grumplestiltskin.Galois (PGFElement, PGFIntermediate, pgfFromElem, pgfRecip, pgfToElem, pgfZero)
import Plutarch.Internal.PlutusType (PlutusType, pmatch)
import Plutarch.Internal.Term (S, Term, plet, punsafeCoerce)
import Plutarch.Prelude (
    PEq,
    PInteger,
    PPositive,
    PShow,
    pabs,
    pcon,
    pcond,
    pfix,
    pif,
    plam,
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
import Plutarch.Repr.SOP (DeriveAsSOPStruct (DeriveAsSOPStruct))

{-
Calculators:
- "https://www.graui.de/code/elliptic2/"
- "https://andrea.corbellini.name/ecc/interactive/modk-add.html"

Resources:
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

data PECPoint (s :: S)
    = PECPoint (Term s PGFElement) (Term s PGFElement)
    | PECInfinity
    deriving stock (Generic)
    deriving anyclass (SOP.Generic)
    deriving
        (PlutusType)
        via (DeriveAsSOPStruct PECPoint)

instance PEq PECPoint

instance PShow PECPoint

data PECIntermediatePoint (s :: S)
    = PECIntermediatePoint (Term s PGFIntermediate) (Term s PGFIntermediate)
    | PECIntermediateInfinity
    deriving stock (Generic)
    deriving anyclass (SOP.Generic)
    deriving
        (PlutusType)
        via (DeriveAsSOPStruct PECIntermediatePoint)

ptoPoint :: forall (s :: S). Term s PPositive -> Term s PECIntermediatePoint -> Term s PECPoint
ptoPoint fieldModulus p = pmatch p $ \case
    PECIntermediateInfinity -> pcon PECInfinity
    PECIntermediatePoint x y -> pcon $ PECPoint (pgfToElem x fieldModulus) (pgfToElem y fieldModulus)

{- | @P + Q = R@ where @R@ is the inverse of a point on the intersection of the curve and the line defined by @P@ and @Q@.
In case @P == Q@, we calculate the @2P@.
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
                        ( plet (yDiff #* pgfFromElem (pgfRecip # xDiff # fieldModulus)) $ \lambda ->
                            plet (((lambda #* lambda) #- point1X) #- point2X) $ \point3X ->
                                pcon . PECIntermediatePoint point3X $ (lambda #* (point1X #- point3X)) #- point1Y
                        )

-- | @2P = R@ where @R@ is the inverse of a point at the intersection of the @P@'s tangent and the curve.
ppointDouble ::
    forall (s :: S). Term s PPositive -> Term s PInteger -> Term s PECIntermediatePoint -> Term s PECIntermediatePoint
ppointDouble fieldModulus curveA point = pmatch point $ \case
    PECIntermediateInfinity -> pcon PECIntermediateInfinity
    PECIntermediatePoint pointX pointY ->
        pif
            -- TODO: we're reducing the y coordinate here. Let's use that going forward.
            (pgfToElem pointY fieldModulus #== pgfZero)
            (pcon PECIntermediateInfinity)
            ( let lambdaNum = (pgf3 #* (pointX #* pointX)) #+ punsafeCoerce curveA
                  lambdaDen = pgfFromElem $ pgfRecip # (pgf2 #* pointY) # fieldModulus
               in plet (lambdaNum #* lambdaDen) $ \lambda ->
                    let newPointX = (lambda #* lambda) #- (pgf2 #* pointX)
                        newPointY = (lambda #* (pointX #- newPointX)) #- pointY
                     in pcon . PECIntermediatePoint newPointX $ newPointY
            )

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
        , (scaleFactor #<= 0, invPoint (go #$ pabs # scaleFactor))
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

invPoint ::
    forall (s :: S).
    Term s PECIntermediatePoint ->
    Term s PECIntermediatePoint
invPoint point =
    pmatch
        point
        ( \case
            PECIntermediateInfinity -> pcon PECIntermediateInfinity
            PECIntermediatePoint x y -> pcon $ PECIntermediatePoint x (pgfFromElem pgfZero #- y)
        )

-- | A constant @2@
pgf2 :: Term s PGFIntermediate
pgf2 = punsafeCoerce (2 :: Term s PInteger)

-- | A constant @3@
pgf3 :: Term s PGFIntermediate
pgf3 = punsafeCoerce (3 :: Term s PInteger)
