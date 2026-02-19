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

    -- ** Plutarch

    -- *** SOP encoded
    PD2Element,
    PD2Intermediate,

    -- * Functions

    -- ** Element introduction
    mkD2Element,
    mkSubD2Element,
    pd2Zero,
    pd2One,
    pd2I,

    -- ** Operations
    pd2Square,
    pd2Divide,

    -- ** Element to intermediate
    pd2FromElem,

    -- ** Finalizing computations
    pd2ToElem,
) where

import GHC.Generics (Generic)
import Generics.SOP qualified as SOP
import Numeric.Natural (Natural)
import Plutarch.Builtin.Integer (pexpModInteger)
import Plutarch.Internal.Case (punsafeCase)
import Plutarch.Internal.Lift (
    LiftError (OtherLiftError),
    PLiftedClosed,
    getPLiftedClosed,
    mkPLifted,
    mkPLiftedClosed,
    pliftedFromClosed,
    pliftedToClosed,
 )
import Plutarch.Prelude (
    DeriveAsSOPStruct (DeriveAsSOPStruct),
    PAdditiveGroup (pnegate, pscaleInteger, (#-)),
    PAdditiveMonoid (pscaleNatural, pzero),
    PAdditiveSemigroup (pscalePositive, (#+)),
    PEq,
    PInteger,
    PLiftable (
        AsHaskell,
        PlutusRepr,
        haskToRepr,
        plutToRepr,
        reprToHask,
        reprToPlut
    ),
    PMultiplicativeMonoid (pone),
    PMultiplicativeSemigroup (ppowPositive, (#*)),
    PNatural,
    PPositive,
    PShow,
    PlutusType,
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
import Plutarch.Unsafe (punsafeCoerce)
import Test.QuickCheck (
    Arbitrary (arbitrary, shrink),
    Gen,
    chooseInt,
 )
import Test.QuickCheck.Instances.Natural ()

-- | @since wip
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

mkSubD2Element :: Natural -> Natural -> D2Element
mkSubD2Element r b = D2Element (r `mod` b) 0

{- | An element in the second-degree extension of some finite field. The order
of the field in question is implicit for reasons of efficiency.

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
        )
    deriving
        ( -- | @since wip
          PlutusType
        )
        via (DeriveAsSOPStruct PD2Element)

-- | @since wip
instance PEq PD2Element

-- | @since wip
instance PShow PD2Element

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
pd2One = pconstant . D2Element 1 $ 1

{- | The element corresponding to $i$ in the complex numbers, which exists in
every second-degree extension of any finite field. More precisely, this has
the zero element as its \'real\' part, and the one element as its
\'imaginary\' part.

@since wip
-}
pd2I :: forall (s :: S). Term s PD2Element
pd2I = pconstant . D2Element 0 $ 1

{- | Convert an element into an intermediate form for computation. This
operation is essentially free.

@since wip
-}
pd2FromElem :: forall (s :: S). Term s PD2Element -> Term s PD2Intermediate
pd2FromElem = punsafeCoerce

{- | An intermediate computation over the second-order extension of some finite
field. This type exists for efficiency: thus, you want to do all your
calculations in 'PD2Intermediate', then convert to 'PD2Element' at the end.

@since wip
-}
data PD2Intermediate (s :: S) = PD2Intermediate (Term s PInteger) (Term s PInteger)
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
        via (DeriveAsSOPStruct PD2Intermediate)

-- | @since wip
instance PAdditiveSemigroup PD2Intermediate where
    t1 #+ t2 = pmatch t1 $ \case
        PD2Intermediate r1 i1 -> pmatch t2 $ \case
            PD2Intermediate r2 i2 -> pcon . PD2Intermediate (r1 #+ r2) $ i1 #+ i2
    pscalePositive t p = pmatch t $ \case
        PD2Intermediate r i -> pcon . PD2Intermediate (pscalePositive r p) . pscalePositive i $ p

-- | @since wip
instance PAdditiveMonoid PD2Intermediate where
    pzero = pcon . PD2Intermediate 0 $ 0
    pscaleNatural t n = pmatch t $ \case
        PD2Intermediate r i -> pcon . PD2Intermediate (pscaleNatural r n) . pscaleNatural i $ n

-- | @since wip
instance PAdditiveGroup PD2Intermediate where
    pnegate = phoistAcyclic $ plam $ \t -> pmatch t $ \case
        PD2Intermediate r i -> pcon . PD2Intermediate (pnegate # r) $ pnegate # i
    t1 #- t2 = pmatch t1 $ \case
        PD2Intermediate r1 i1 -> pmatch t2 $ \case
            PD2Intermediate r2 i2 -> pcon . PD2Intermediate (r1 #- r2) $ i1 #- i2
    pscaleInteger t scalar = pmatch t $ \case
        PD2Intermediate r i -> pcon . PD2Intermediate (pscaleInteger r scalar) . pscaleInteger i $ scalar

-- | @since wip
instance PMultiplicativeSemigroup PD2Intermediate where
    t1 #* t2 = pmatch t1 $ \case
        PD2Intermediate a b -> pmatch t2 $ \case
            PD2Intermediate c d ->
                let ac = a #* c
                    bd = b #* d
                    ad = a #* d
                    bc = b #* c
                 in pcon . PD2Intermediate (ac #- bd) $ ad #+ bc

    -- Note (Koz, 20/02/2026): In theory, it would be good to make use of
    -- `ExpModInteger` for this operation like we did for ordinary Galois fields.
    -- However, the only way we can do this is by constructing a binomial, which
    -- has a number of terms linear in the size of the exponent. On the other
    -- hand, exponentiation by squaring only needs an amount of work logarithmic
    -- in the size of the exponent. On the whole, we thus end up doing less work.
    ppowPositive :: forall (s :: S). Term s PD2Intermediate -> Term s PPositive -> Term s PD2Intermediate
    ppowPositive t e = go # pupcast e
      where
        go :: Term s (PInteger :--> PD2Intermediate)
        go = pfix $ \self -> plam $ \i ->
            pif
                (i #<= 1)
                t
                ( plet (pd2Square (self #$ pquot # i # 2)) $ \squared ->
                    -- Note (Koz, 20/02/2026): We can use casing on integers here, as
                    -- there are only two possible answers (0 and 1), which means the
                    -- default erroring behaviour cannot trigger. This allows us to
                    -- avoid having to call `BuiltinEquals` against a constant, which
                    -- makes things slightly smaller and faster.
                    punsafeCase
                        (prem # i # 2)
                        [ -- When 0
                          popaque squared
                        , -- When 1
                          popaque (squared #+ t)
                        ]
                )

-- | @since wip
instance PMultiplicativeMonoid PD2Intermediate where
    pone = pcon . PD2Intermediate 1 $ 0

{- | Squares the given element. @pd2Square x@ is slightly more efficient than @x
#* x@, as it avoids a redundant multiplication and 'pmatch'.

@since wip
-}
pd2Square :: forall (s :: S). Term s PD2Intermediate -> Term s PD2Intermediate
pd2Square t = pmatch t $ \case
    PD2Intermediate a b ->
        let aSquared = a #* a
            bSquared = b #* b
            abTwice = 2 #* (a #* b)
         in pcon . PD2Intermediate (aSquared #- bSquared) $ abTwice

{- | @'pd2Divide' x y n@ performs the division of @x@ by @y@, assuming @x@ and
@y@ are elements of the second-degree extension of the finite field of order
@n@. @y@ must be non-zero or this function will error.

@since wip
-}
pd2Divide ::
    forall (s :: S).
    Term s PD2Intermediate ->
    Term s PD2Intermediate ->
    Term s PPositive ->
    Term s PD2Intermediate
pd2Divide w z b = pmatch w $ \case
    PD2Intermediate u v -> pmatch z $ \case
        PD2Intermediate x y -> plet (pexpModInteger # ((x #* x) #+ (y #* y)) # (-1) # pupcast b) $ \denom ->
            let ux = u #* x
                vy = v #* y
                vx = v #* x
                uy = u #* y
             in pcon . PD2Intermediate ((ux #+ vy) #* denom) $ (vx #- uy) #* denom

{- | \'Complete\' an intermediate computation with the result being an element
of a second-degree extension of the given order. The order should be prime,
but this is not checked.

@since wip
-}
pd2ToElem :: forall (s :: S). Term s PD2Intermediate -> Term s PPositive -> Term s PD2Element
pd2ToElem t p = pmatch t $ \case
    PD2Intermediate r i ->
        pcon
            . PD2Element (punsafeCoerce (pmod # r # pupcast p))
            . punsafeCoerce
            $ pmod # i # pupcast p

-- Helpers

prealPart :: forall (s :: S). Term s (PD2Element :--> PNatural)
prealPart = phoistAcyclic $ plam $ \t -> pmatch t $ \case
    PD2Element r _ -> r

pimaginaryPart :: forall (s :: S). Term s (PD2Element :--> PNatural)
pimaginaryPart = phoistAcyclic $ plam $ \t -> pmatch t $ \case
    PD2Element _ i -> i
