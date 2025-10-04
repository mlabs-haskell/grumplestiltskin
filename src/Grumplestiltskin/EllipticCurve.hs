{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-local-binds #-}

module Grumplestiltskin.EllipticCurve (pAddPoints, pToPoint, PECIntermediatePoint (PECIntermediatePoint), PECPoint (PECPoint)) where

import GHC.Generics (Generic)
import Generics.SOP qualified as SOP
import Grumplestiltskin.Galois (PGFElement, PGFIntermediate, pgfFromData, pgfFromElem, pgfRecip, pgfToElem)
import Plutarch.Builtin.Bool (PBool)
import Plutarch.Internal.PlutusType (pmatch)
import Plutarch.Internal.Term (S, Term)
import Plutarch.Pair (PPair (PPair))
import Plutarch.Prelude (DeriveNewtypePlutusType (DeriveNewtypePlutusType), PEq, PPositive, PShow, PlutusType, pcon, pconstant, pupcast, (#), (#*), (#-))

{-
Calculator: https://www.graui.de/code/elliptic2/

Resources:
- "https://rareskills.io/post/elliptic-curves-finite-fields"
- Handbook of Elliptic and Hyperelliptic Curve Cryptography -- Henri Cohen, ...
- "http://koclab.cs.ucsb.edu/teaching/ecc/eccPapers/Washington-ch04.pdf" (some examples and proofs)

Functionality of Elliptic curve over finite field. (cyclic groups)

curve order = number of points on the curve (including point in infinity)
field modulus = is the modulo we apply to the values

## Functions

-- TODO: representing the point at infinity?

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

newtype PECPoint (s :: S) = PECPoint (Term s (PPair PGFElement PGFElement))
    deriving stock
        (Generic)
    deriving anyclass
        (SOP.Generic)
    deriving
        (PlutusType)
        via (DeriveNewtypePlutusType PECPoint)

instance PEq PECPoint

newtype PECIntermediatePoint (s :: S) = PECIntermediatePoint (Term s (PPair PGFIntermediate PGFIntermediate))
    deriving stock
        (Generic)
    deriving anyclass
        (SOP.Generic)
    deriving
        (PlutusType)
        via (DeriveNewtypePlutusType PECIntermediatePoint)

pToPoint :: forall (s :: S). Term s PECIntermediatePoint -> Term s PPositive -> Term s PECPoint
pToPoint p fieldModulus =
    pcon $
        PECPoint $
            pmatch
                (pupcast p)
                (\(PPair x y) -> pcon $ PPair (pgfToElem x fieldModulus) (pgfToElem y fieldModulus))

pAddPoints :: forall (s :: S). Term s PPositive -> Term s PECIntermediatePoint -> Term s PECIntermediatePoint -> Term s PECIntermediatePoint
pAddPoints fieldModulus point1 point2 =
    pcon $
        PECIntermediatePoint $
            pmatch
                (pupcast point1)
                ( \(PPair point1x point1y) ->
                    pmatch
                        (pupcast point2)
                        ( \(PPair point2x point2y) ->
                            let lambdaNum = point1y #- point2y
                                lambdaDenum = pgfFromElem $ pgfRecip # (point1x #- point2x) # fieldModulus
                                lambda = lambdaNum #* lambdaDenum
                                point3x = ((lambda #* lambda) #- point1x) #- point2x
                                point3y = (lambda #* (point1x #- point3x)) #- point1y
                             in pcon $ PPair point3x point3y
                        )
                )
