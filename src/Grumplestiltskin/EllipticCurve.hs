{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

{- | A general implementation for elliptic curves over finite field.

The general formula for these functions is: @y^2 = X^2 + a * x + b (mod r)@.
-}
module Grumplestiltskin.EllipticCurve (
    pAddPoints,
    pPointDouble,
    pToPoint,
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
    pcon,
    pif,
    pletC,
    unTermCont,
    (#),
    (#*),
    (#+),
    (#-),
    (#==),
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
    deriving stock
        (Generic)
    deriving anyclass
        (SOP.Generic)
    deriving
        (PlutusType)
        via (DeriveAsSOPStruct PECPoint)

instance PEq PECPoint

data PECIntermediatePoint (s :: S)
    = PECIntermediatePoint (Term s PGFIntermediate) (Term s PGFIntermediate)
    | PECIntermediateInfinity
    deriving stock
        (Generic)
    deriving anyclass
        (SOP.Generic)
    deriving
        (PlutusType)
        via (DeriveAsSOPStruct PECIntermediatePoint)

pToPoint :: forall (s :: S). Term s PPositive -> Term s PECIntermediatePoint -> Term s PECPoint
pToPoint fieldModulus p =
    pmatch
        p
        ( \case
            PECIntermediateInfinity -> pcon PECInfinity
            PECIntermediatePoint x y -> pcon $ PECPoint (pgfToElem x fieldModulus) (pgfToElem y fieldModulus)
        )

{- | @P + Q = R@ where @R@ is the inverse of a point on the intersection of the curve and the line defined by @P@ and @Q@.
In case @P == Q@, we calculate the @2P@.
-}
pAddPoints :: forall (s :: S). Term s PPositive -> Term s PInteger -> Term s PECIntermediatePoint -> Term s PECIntermediatePoint -> Term s PECIntermediatePoint
pAddPoints fieldModulus curveA point1 point2 =
    pmatch
        point1
        ( \case
            -- Point at infinity behaves as addition identity element
            PECIntermediateInfinity -> point2
            (PECIntermediatePoint pointX1 pointY1) ->
                pmatch
                    point2
                    ( \case
                        -- Point at infinity behaves as addition identity element
                        PECIntermediateInfinity -> point1
                        PECIntermediatePoint pointX2 pointY2 ->
                            unTermCont
                                ( do
                                    yDiff <- pletC (pointY1 #- pointY2)
                                    xDiff <- pletC (pointX1 #- pointX2)
                                    pure $
                                        pif
                                            -- Doing the modulo normalisation 2x as part of `pgfToElem`. Can we do better?
                                            (pgfToElem xDiff fieldModulus #== pgfZero)
                                            ( pif
                                                (pgfToElem yDiff fieldModulus #== pgfZero)
                                                -- The case when both of the points are equal.
                                                (pPointDouble fieldModulus curveA point1)
                                                -- Having X coordinates of both of points the same results in Point at infinity.
                                                (pcon PECIntermediateInfinity)
                                            )
                                            ( let lambdaNum = yDiff
                                                  lambdaDenum = pgfFromElem $ pgfRecip # xDiff # fieldModulus
                                               in plet
                                                    (lambdaNum #* lambdaDenum)
                                                    ( \lambda ->
                                                        plet
                                                            (((lambda #* lambda) #- pointX1) #- pointX2)
                                                            ( \pointX3 ->
                                                                let pointY3 = (lambda #* (pointX1 #- pointX3)) #- pointY1
                                                                 in pcon $ PECIntermediatePoint pointX3 pointY3
                                                            )
                                                    )
                                            )
                                )
                    )
        )

-- | @2P = R@ where @R@ is the inverse of a point at the intersection of the @P@'s tangent and the curve.
pPointDouble :: forall (s :: S). Term s PPositive -> Term s PInteger -> Term s PECIntermediatePoint -> Term s PECIntermediatePoint
pPointDouble fieldModulus curveA point =
    pmatch
        point
        ( \case
            PECIntermediateInfinity -> pcon PECIntermediateInfinity
            PECIntermediatePoint pointX1 pointY1 ->
                let lambdaNum = (pgf3 #* (pointX1 #* pointX1)) #+ punsafeCoerce curveA
                    lambdaDenum = pgfFromElem $ pgfRecip # (pgf2 #* pointY1) # fieldModulus
                    lambda = lambdaNum #* lambdaDenum
                    pointX2 = (lambda #* lambda) #- (pgf2 #* pointX1)
                    pointY2 = (lambda #* (pointX1 #- pointX2)) #- pointY1
                 in pcon $ PECIntermediatePoint pointX2 pointY2
        )

-- | A constant @2@
pgf2 :: Term s PGFIntermediate
pgf2 = punsafeCoerce (2 :: Term s PInteger)

-- | A constant @3@
pgf3 :: Term s PGFIntermediate
pgf3 = punsafeCoerce (3 :: Term s PInteger)
