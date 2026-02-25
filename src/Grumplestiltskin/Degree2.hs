{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE MultiWayIf #-}

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
module Grumplestiltskin.Degree2 (
    -- * Types

    -- ** Haskell
    D2Element,

    -- ** SOP-encoded
    PD2Element,
    PD2Intermediate,

    -- * Functions

    -- ** Element introduction
    mkD2Element,
    mkSubD2Element,
    pd2Zero,
    pd2One,

    -- ** Operations
    fromD2Element,
    pd2Square,
    pd2Pow,
    pd2Divide,

    -- ** Element to intermediate
    pd2FromElem,

    -- ** Finalizing computations
    pd2ToElem,
) where

import Data.Kind (Type)
import GHC.Generics (Generic)
import Generics.SOP qualified as SOP
import Numeric.Natural (Natural)
import Plutarch.Builtin.Integer (pexpModInteger)
import Plutarch.Internal.Case (punsafeCase)
import Plutarch.Internal.Lift (
    LiftError (OtherLiftError),
    PLiftable (
        AsHaskell,
        PlutusRepr,
        haskToRepr,
        plutToRepr,
        reprToHask,
        reprToPlut
    ),
    PLiftedClosed,
    getPLiftedClosed,
    mkPLifted,
    mkPLiftedClosed,
    pliftedFromClosed,
    pliftedToClosed,
 )
import Plutarch.Internal.PlutusType (PlutusType (PInner, pcon', pmatch'))
import Plutarch.Prelude (
    DeriveAsSOPStruct (DeriveAsSOPStruct),
    PAdditiveGroup (pnegate, pscaleInteger, (#-)),
    PAdditiveMonoid (pscaleNatural, pzero),
    PAdditiveSemigroup (pscalePositive, (#+)),
    PEq,
    PInteger,
    PMultiplicativeMonoid (pone, ppowNatural),
    PMultiplicativeSemigroup (ppowPositive, (#*)),
    PNatural,
    PPositive,
    PShow,
    S,
    Term,
    pcon,
    pconstant,
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
import Test.QuickCheck (
    Arbitrary (arbitrary, shrink),
    Gen,
    chooseInt,
 )
import Test.QuickCheck.Instances.Natural ()

{- | Haskell-level representation of an element of a second-degree extension of
some finite field. The field order is implicit, but the assumption is that
both the \'real\' and \'imaginary\' parts of the element are already in
reduced form.

@since wip
-}
data D2Element = D2Element Natural Natural
    deriving stock
        ( -- | @since wip
          Eq
        , -- | @since wip
          Show
        )

{- | This generates elements of the second-degree extension of @GF(97)@. While a
somewhat arbitrary choice, the field order is both prime and within the
default QuickCheck size of 100, hence the choice.

= Important note

Ensure you choose a suitable irreducible! @5@ is an example of a suitable
choice: in @GF(97)@, @x^2 = 5@ has no solutions.

@since wip
-}
instance Arbitrary D2Element where
    arbitrary = D2Element <$> go <*> go
      where
        go :: Gen Natural
        go = fromIntegral <$> chooseInt (0, 96)
    shrink (D2Element r i) = do
        r' <- shrink r
        i' <- shrink i
        pure . D2Element r' $ i'

{- | Given a \'real part\', an \'imaginary part\' and a field modulus, construct
the corresponding 'D2Element' in the field extension corresponding to that
modulus. The modulus should be prime, but this is not checked.

= Note

If given a zero modulus, this will error.

@since wip
-}
mkD2Element :: Natural -> Natural -> Natural -> D2Element
mkD2Element r i b = D2Element (r `mod` b) (i `mod` b)

{- | As 'mkD2Element', but with the \'imaginary part\' always zero.

@since wip
-}
mkSubD2Element :: Natural -> Natural -> D2Element
mkSubD2Element r b = D2Element (r `mod` b) 0

{- | Convert a 'D2Element' into its \'real\' and \'imaginary\' components, as
'Natural's.

@since wip
-}
fromD2Element :: D2Element -> (Natural, Natural)
fromD2Element (D2Element r i) = (r, i)

{- | Plutarch-level representation of an element of a second-degree extension of
some finite field. The field order is implicit, but the assumption is that
both the \'real\' and \'imaginary\' parts of the element are already in
reduced form.

@since wip
-}
data PD2Element (s :: S) = PD2Element (Term s PNatural) (Term s PNatural)
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
        via (DeriveAsSOPStruct PD2Element)

-- | @since wip
instance PLiftable PD2Element where
    type AsHaskell PD2Element = D2Element
    type PlutusRepr PD2Element = PLiftedClosed PD2Element
    haskToRepr (D2Element r i) = mkPLiftedClosed $ pcon $ PD2Element (pconstant r) (pconstant i)
    reprToHask t = do
        realPart :: Integer <- plutToRepr $ mkPLifted (prealPart # getPLiftedClosed t)
        imaginaryPart :: Integer <- plutToRepr $ mkPLifted (pimaginaryPart # getPLiftedClosed t)
        if
            | realPart < 0 -> Left . OtherLiftError $ "Negative real part is not valid for PD2Element"
            | imaginaryPart < 0 -> Left . OtherLiftError $ "Negative imaginary part is not valid for PD2Element"
            | otherwise -> pure $ D2Element (fromIntegral realPart) (fromIntegral imaginaryPart)
    reprToPlut = pliftedFromClosed
    plutToRepr = Right . pliftedToClosed

{- | The zero element (the additive identity), which exists in every
second-degree extension of any finite field. More precisely, this has the
zero element as both its \'real\' and its \'imaginary\' part.

@since wip
-}
pd2Zero :: forall (s :: S). Term s PD2Element
pd2Zero = pconstant . D2Element 0 $ 0

{- | The one element (the multiplicative identity), which exists in every
second-degree extension of any finite field. More precisely, this has the one
element as its \'real\' part, and the zero element as its \'imaginary\' part.

@since wip
-}
pd2One :: forall (s :: S). Term s PD2Element
pd2One = pconstant . D2Element 1 $ 0

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
                                    let recipExpr = (x #* x) #- (pupcast rSquared #* (y #* y))
                                        ux = u #* x
                                        yv = y #* v
                                        xv = x #* v
                                        uy = u #* y
                                     in plet (pexpModInteger # recipExpr # (-1) # pupcast order) $ \recipr ->
                                            k # ((ux #- (5 #* yv)) #* recipr) # ((xv #- uy) #* recipr)
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

prealPart :: forall (s :: S). Term s (PD2Element :--> PNatural)
prealPart = phoistAcyclic $ plam $ \t -> pmatch t $ \case
    PD2Element r _ -> r

pimaginaryPart :: forall (s :: S). Term s (PD2Element :--> PNatural)
pimaginaryPart = phoistAcyclic $ plam $ \t -> pmatch t $ \case
    PD2Element _ i -> i
