{-# LANGUAGE ImpredicativeTypes #-}

{- | Second-degree extensions of finite fields. This is an analogy to complex
numbers being an extension of the reals, but generalized to any finite field.
Thus, throughout, we will refer to the \'real\' and \'imaginary\' parts of an
element of such a field, with the appropriate transfer of meaning from
complex numbers.

= More information

* [Field extensions](https://en.wikipedia.org/wiki/Field_extension)
* [Complex numbers](https://en.wikipedia.org/wiki/Complex_number)

@since wip
-}
module Grumplestiltskin.Degree2.Galois (
    -- * Types

    -- ** SOP-encoded
    PD2Intermediate,

    -- * Functions

    -- ** Operations
    pd2Square,
    pd2Pow,
    pd2Divide,

    -- ** Element to intermediate
    pd2FromElem,

    -- ** Finalizing computations
    pd2ToElem,
) where

import Data.Kind (Type)
import Grumplestiltskin.Degree2.Element (PD2Element (PD2Element))
import Plutarch.Builtin.Integer (pexpModInteger)
import Plutarch.Internal.Case (punsafeCase)
import Plutarch.Internal.PlutusType (PlutusType (PInner, pcon', pmatch'))
import Plutarch.Prelude (
    PAdditiveGroup (pnegate, pscaleInteger, (#-)),
    PAdditiveMonoid (pscaleNatural, pzero),
    PAdditiveSemigroup (pscalePositive, (#+)),
    PInteger,
    PMultiplicativeMonoid (pone, ppowNatural),
    PMultiplicativeSemigroup (ppowPositive, (#*)),
    PNatural,
    PPositive,
    S,
    Term,
    pcon,
    pfix,
    phoistAcyclic,
    pif,
    plam,
    plet,
    pmatch,
    pmod,
    popaque,
    pquot,
    prem,
    pupcast,
    (#),
    (#$),
    (#<=),
    (:-->),
 )
import Plutarch.Unsafe (punsafeCoerce, punsafeDowncast)
import Test.QuickCheck.Instances.Natural ()

{- | Convert an element into an intermediate form, suitable for computation.

@since wip
-}
pd2FromElem ::
    forall (s :: S).
    Term s PD2Element ->
    Term s PD2Intermediate
pd2FromElem t = pmatch t $ \(PD2Element x y) ->
    pcon $ PD2Intermediate $ plam $ \_ _ k -> k # pupcast x # pupcast y

{- | An intermediate computation over the second-order extension of some finite
field. This type exists for efficiency: you want to do all calculations in
'PD2Intermediate', then use 'pd2ToElem' to produce a result.

@since wip
-}
newtype PD2Intermediate (s :: S)
    = PD2Intermediate
        (forall (r :: S -> Type). Term s (PNatural :--> PPositive :--> (PInteger :--> PInteger :--> r) :--> r))

-- | @since wip
instance PlutusType PD2Intermediate where
    type PInner PD2Intermediate = PD2Intermediate
    pcon' (PD2Intermediate t) = punsafeCoerce t
    pmatch' t f = f (PD2Intermediate $ punsafeCoerce t)

-- | @since wip
instance PAdditiveSemigroup PD2Intermediate where
    t1 #+ t2 = pmatch t1 $ \(PD2Intermediate k1) ->
        pmatch t2 $ \(PD2Intermediate k2) ->
            pcon $ PD2Intermediate $ plam $ \rSquared order k ->
                k1
                    # rSquared
                    # order
                    # plam
                        ( \x1 y1 ->
                            k2 # rSquared # order # plam (\x2 y2 -> k # (x1 #+ x2) # (y1 #+ y2))
                        )
    pscalePositive t p = pmatch t $ \(PD2Intermediate k1) ->
        pcon $ PD2Intermediate $ plam $ \rSquared order k ->
            k1 # rSquared # order # plam (\x1 y1 -> k # pscalePositive x1 p # pscalePositive y1 p)

-- | @since wip
instance PAdditiveMonoid PD2Intermediate where
    pzero = pcon $ PD2Intermediate $ plam $ \_ _ k -> k # pzero # pzero
    pscaleNatural t n = pmatch t $ \(PD2Intermediate k1) ->
        pcon $ PD2Intermediate $ plam $ \rSquared order k ->
            k1 # rSquared # order # plam (\x1 y1 -> k # pscaleNatural x1 n # pscaleNatural y1 n)

-- | @since wip
instance PAdditiveGroup PD2Intermediate where
    pnegate = phoistAcyclic $ plam $ \t ->
        pmatch t $ \(PD2Intermediate k1) ->
            pcon $ PD2Intermediate $ plam $ \rSquared order k ->
                k1 # rSquared # order # plam (\x1 y1 -> k # (pnegate # x1) # (pnegate # y1))
    t1 #- t2 = pmatch t1 $ \(PD2Intermediate k1) ->
        pmatch t2 $ \(PD2Intermediate k2) ->
            pcon $ PD2Intermediate $ plam $ \rSquared order k ->
                k1
                    # rSquared
                    # order
                    # plam
                        ( \x1 y1 ->
                            k2 # rSquared # order # plam (\x2 y2 -> k # (x1 #- x2) # (y1 #- y2))
                        )
    pscaleInteger t i = pmatch t $ \(PD2Intermediate k1) ->
        pcon $ PD2Intermediate $ plam $ \rSquared order k ->
            k1 # rSquared # order # plam (\x1 y1 -> k # pscaleInteger x1 i # pscaleInteger y1 i)

-- | @since wip
instance PMultiplicativeSemigroup PD2Intermediate where
    -- \| = Note
    --
    -- Avoid doing something like @x #* x@, as this is less efficient. In such
    -- cases, use 'pd2Square' instead.
    t1 #* t2 = pmatch t1 $ \(PD2Intermediate k1) ->
        pmatch t2 $ \(PD2Intermediate k2) ->
            pcon $ PD2Intermediate $ plam $ \rSquared order k ->
                k1
                    # rSquared
                    # order
                    # plam
                        ( \x1 y1 ->
                            k2
                                # rSquared
                                # order
                                # plam
                                    ( \x2 y2 ->
                                        let x1x2 = x1 #* x2
                                            imaginaryPart = (x1 #* y2) #+ (x2 #* y1)
                                            rest = pupcast rSquared #* (y1 #* y2)
                                         in k # (x1x2 #+ rest) # imaginaryPart
                                    )
                        )
    ppowPositive ::
        forall (s :: S).
        Term s PD2Intermediate ->
        Term s PPositive ->
        Term s PD2Intermediate
    ppowPositive t p = go # pupcast p
      where
        go :: Term s (PInteger :--> PD2Intermediate)
        go = pfix $ \self -> plam $ \i ->
            pif
                (i #<= 1)
                t
                ( plet (pd2Square (self #$ pquot # i # 2)) $ \squared ->
                    -- Note (Koz, 26/02/2026): We can use casing on integers here,
                    -- as there are only two possible answers (0 and 1), which means
                    -- the default erroring behaviour cannot trigger. This allows us
                    -- to avoid having to call `BuiltinEquals` against a constant,
                    -- which makes things slightly smaller and faster.
                    punsafeCase
                        (prem # i # 2)
                        [ -- When 0
                          popaque squared
                        , -- When 1
                          popaque (t #* squared)
                        ]
                )

-- | @since wip
instance PMultiplicativeMonoid PD2Intermediate where
    pone = pcon $ PD2Intermediate $ plam $ \_ _ k -> k # pone # pzero

{- | Given an irreducible (the 'PNatural' argument) and a field order (the
'PPositive' argument), \'complete\' the computation described by the
'PD2Intermediate' argument to produce a 'PD2Element'. The field order should
be prime, but this is not checked.

= Note on irreducibles

An /irreducible/ is some @r@ such that @x^2 = r@ has no solution in the field
of the given field order. If an argument not satisfying this property is
given as an irreducible, the computation can fail with a strange, and
unrelated, error message, so choose this carefully.

@since wip
-}
pd2ToElem ::
    forall (s :: S).
    Term s PNatural ->
    Term s PPositive ->
    Term s PD2Intermediate ->
    Term s PD2Element
pd2ToElem rSquared order t = pmatch t $ \(PD2Intermediate k1) ->
    k1 # rSquared # order # plam (\x y -> pcon . PD2Element (preduce # x # order) $ preduce # y # order)

{- | Squares the given element. @pd2Square x@ is slightly more efficient than @x
#* x@, as it avoids a redundant multiplication and 'pmatch'.

@since wip
-}
pd2Square ::
    forall (s :: S).
    Term s PD2Intermediate -> Term s PD2Intermediate
pd2Square t = pmatch t $ \(PD2Intermediate k1) ->
    pcon $ PD2Intermediate $ plam $ \rSquared order k ->
        k1
            # rSquared
            # order
            # plam
                ( \x y ->
                    let xSquared = x #* x
                        ySquared = y #* y
                        xy = x #* y
                     in k # (xSquared #+ (pupcast rSquared #* ySquared)) # (2 #* xy)
                )

{- | Raises the first argument to the power of the second argument: this acts as
repeated multiplication.

@since wip
-}
pd2Pow ::
    forall (s :: S).
    Term s PD2Intermediate -> Term s PInteger -> Term s PD2Intermediate
pd2Pow t i =
    pif
        (i #<= (-1))
        (pd2Recip . ppowNatural t . punsafeCoerce $ pnegate # i)
        (ppowNatural t . punsafeCoerce $ i)

{- | Divides the first argument by the second argument. The second argument must
not be zero: that is, either its \'real\' or \'imaginary\' part must be
nonzero. If given a zero second argument, this will error.

@since wip
-}
pd2Divide ::
    forall (s :: S).
    Term s PD2Intermediate -> Term s PD2Intermediate -> Term s PD2Intermediate
pd2Divide w z = pmatch w $ \(PD2Intermediate k1) ->
    pmatch z $ \(PD2Intermediate k2) ->
        pcon $ PD2Intermediate $ plam $ \rSquared order k ->
            k1
                # rSquared
                # order
                # plam
                    ( \u v ->
                        k2
                            # rSquared
                            # order
                            # plam
                                ( \x y ->
                                    let rSquared' = pupcast rSquared
                                        recipExpr = (x #* x) #- (rSquared' #* (y #* y))
                                        ux = u #* x
                                        yv = y #* v
                                        xv = x #* v
                                        uy = u #* y
                                     in plet (pexpModInteger # recipExpr # (-1) # pupcast order) $ \recipr ->
                                            k # ((ux #- (rSquared' #* yv)) #* recipr) # ((xv #- uy) #* recipr)
                                )
                    )

-- Helpers

preduce ::
    forall (s :: S).
    Term s (PInteger :--> PPositive :--> PNatural)
preduce = phoistAcyclic $ plam $ \x order ->
    punsafeDowncast (pmod # x # pupcast order)

pd2Recip ::
    forall (s :: S).
    Term s PD2Intermediate -> Term s PD2Intermediate
pd2Recip t = pmatch t $ \(PD2Intermediate k1) ->
    pcon $ PD2Intermediate $ plam $ \rSquared order k ->
        k1
            # rSquared
            # order
            # plam
                ( \x y ->
                    let recipExpr = (x #* x) #- (pupcast rSquared #* (y #* y))
                     in plet (pexpModInteger # recipExpr # (-1) # pupcast order) $ \recipr ->
                            k # (x #* recipr) #$ pnegate # (y #* recipr)
                )
