{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}

module Grumplestiltskin.Degree2.GaloisDirect (
    -- * Types

    -- ** Haskell
    D2Element (D2Element),

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
    pd2FromPoint,
    pd2ToPoint,
    pd2Square,
    pd2Pow,
    pd2OneI,
    pd2Times,
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
import Plutarch.Prelude (
    DeriveAsSOPStruct (DeriveAsSOPStruct),
    PAdditiveGroup (pnegate, (#-)),
    PAdditiveMonoid (pzero),
    PAdditiveSemigroup (pscalePositive, (#+)),
    PEq,
    PInteger,
    PMultiplicativeSemigroup ((#*)),
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
import Test.QuickCheck.Instances.Natural ()

{- | Haskell-level representation of an element of a second-degree extension of
some finite field. The field order is implicit, but the assumption is that
both the \'real\' and \'imaginary\' parts of the element are already in
reduced form.

@since wip
-}
data D2Element = D2E Natural Natural
    deriving stock
        ( -- | @since wip
          Eq
        )

-- | @since wip
instance Show D2Element where
    show (D2Element x y) = "(" <> show x <> " + " <> show y <> "u)"

-- | @since wip
pattern D2Element :: Natural -> Natural -> D2Element
pattern D2Element x y <- D2E x y

{-# COMPLETE D2Element #-}

{- | Given a \'real part\', an \'imaginary part\' and a field modulus, construct
the corresponding 'D2Element' in the field extension corresponding to that
modulus. The modulus should be prime, but this is not checked.

= Note

If given a zero modulus, this will error.

@since wip
-}
mkD2Element :: Natural -> Natural -> Natural -> D2Element
mkD2Element r i b = D2E (r `mod` b) (i `mod` b)

{- | As 'mkD2Element', but with the \'imaginary part\' always zero.

@since wip
-}
mkSubD2Element :: Natural -> Natural -> D2Element
mkSubD2Element r b = D2E (r `mod` b) 0

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
            | otherwise -> pure $ D2E (fromIntegral realPart) (fromIntegral imaginaryPart)
    reprToPlut = pliftedFromClosed
    plutToRepr = Right . pliftedToClosed

-- | @since wip
pd2FromPoint ::
    forall (r :: S -> Type) (s :: S).
    Term s PD2Element ->
    (Term s PNatural -> Term s PNatural -> Term s r) ->
    Term s r
pd2FromPoint t f = pmatch t $ \(PD2Element x y) -> f x y

-- | @since wip
pd2ToPoint ::
    forall (s :: S).
    Term s PNatural ->
    Term s PNatural ->
    Term s PNatural ->
    Term s PD2Element
pd2ToPoint r i fieldMod =
    let r' = punsafeCoerce (pmod # pupcast r # pupcast fieldMod)
        i' = punsafeCoerce (pmod # pupcast i # pupcast fieldMod)
     in pcon . PD2Element r' $ i'

{- | The zero element (the additive identity), which exists in every
second-degree extension of any finite field. More precisely, this has the
zero element as both its \'real\' and its \'imaginary\' part.

@since wip
-}
pd2Zero :: forall (s :: S). Term s PD2Element
pd2Zero = pconstant . D2E 0 $ 0

{- | The one element (the multiplicative identity), which exists in every
second-degree extension of any finite field. More precisely, this has the one
element as its \'real\' part, and the zero element as its \'imaginary\' part.

@since wip
-}
pd2One :: forall (s :: S). Term s PD2Element
pd2One = pconstant . D2E 1 $ 0

-- | @since wip
data PD2Intermediate (s :: S) = PD2Intermediate (Term s PInteger) (Term s PInteger)
    deriving stock
        ( -- | @since wip
          Generic
        )
    deriving anyclass
        ( -- | @since wip
          SOP.Generic
        , -- | @since wip
          PShow
        )
    deriving
        ( -- | @since wip
          PlutusType
        )
        via (DeriveAsSOPStruct PD2Intermediate)

-- | @since wip
instance PAdditiveSemigroup PD2Intermediate where
    t1 #+ t2 = pmatch t1 $ \(PD2Intermediate x1 y1) ->
        pmatch t2 $ \(PD2Intermediate x2 y2) ->
            pcon $ PD2Intermediate (x1 #+ x2) (y1 #+ y2)
    pscalePositive t p = pmatch t $ \(PD2Intermediate x1 y1) ->
        pcon $ PD2Intermediate (pscalePositive x1 p) (pscalePositive y1 p)

-- | @since wip
instance PAdditiveMonoid PD2Intermediate where
    pzero = pcon $ PD2Intermediate 0 0

-- | @since wip
instance PAdditiveGroup PD2Intermediate where
    pnegate = phoistAcyclic $ plam $ \t -> pmatch t $ \(PD2Intermediate x y) ->
        pcon $ PD2Intermediate (pnegate # x) (pnegate # y)
    t1 #- t2 = pmatch t1 $ \(PD2Intermediate x1 y1) ->
        pmatch t2 $ \(PD2Intermediate x2 y2) ->
            pcon $ PD2Intermediate (x1 #- x2) (y1 #- y2)

-- | @since wip
pd2Square ::
    forall (s :: S).
    Term s PPositive ->
    Term s PD2Intermediate ->
    Term s PD2Intermediate
pd2Square rSquared t = pmatch t $ \(PD2Intermediate x y) ->
    let xSquared = x #* x
        ySquared = y #* y
        xy = x #* y
        newX = xSquared #+ (pupcast rSquared #* ySquared)
        newY = 2 #* xy
     in pcon $ PD2Intermediate newX newY

-- | @since wip
pd2Pow ::
    forall (s :: S).
    Term s PPositive ->
    Term s PPositive ->
    Term s PD2Intermediate ->
    Term s PInteger ->
    Term s PD2Intermediate
pd2Pow fieldMod rSquared x e =
    pif
        (e #<= (-1))
        (pd2Recip # fieldMod # rSquared #$ pd2Pow' # rSquared # x #$ pnegate # e)
        (pd2Pow' # rSquared # x # e)

-- | @since wip
pd2Times ::
    forall (s :: S).
    Term s PPositive ->
    Term s PD2Intermediate ->
    Term s PD2Intermediate ->
    Term s PD2Intermediate
pd2Times rSquared t1 t2 = pmatch t1 $ \(PD2Intermediate x1 y1) ->
    pmatch t2 $ \(PD2Intermediate x2 y2) ->
        let x1x2 = x1 #* x2
            imaginaryPart = (x1 #* y2) #+ (x2 #* y1)
            rest = pupcast rSquared #* (y1 #* y2)
         in pcon $ PD2Intermediate (x1x2 #+ rest) imaginaryPart

-- | @since wip
pd2OneI :: forall (s :: S). Term s PD2Intermediate
pd2OneI = pcon $ PD2Intermediate 1 0

-- | @since wip
pd2Divide ::
    forall (s :: S).
    Term s PPositive ->
    Term s PPositive ->
    Term s PD2Intermediate ->
    Term s PD2Intermediate ->
    Term s PD2Intermediate
pd2Divide fieldMod rSquared t1 t2 = pmatch t1 $ \(PD2Intermediate u v) ->
    pmatch t2 $ \(PD2Intermediate x y) ->
        let rSquared' = pupcast rSquared
            recipExpr = (x #* x) #- (rSquared' #* (y #* y))
            ux = u #* x
            yv = y #* v
            xv = x #* v
            uy = u #* y
         in plet (pexpModInteger # recipExpr # (-1) # pupcast fieldMod) $ \recipr ->
                pcon $ PD2Intermediate ((ux #- (rSquared' #* yv)) #* recipr) ((xv #- uy) #* recipr)

-- | @since wip
pd2FromElem ::
    forall (s :: S).
    Term s PD2Element ->
    Term s PD2Intermediate
pd2FromElem = punsafeCoerce

-- | @since wip
pd2ToElem ::
    forall (s :: S).
    Term s PPositive ->
    Term s PD2Intermediate ->
    Term s PD2Element
pd2ToElem fieldMod t = pmatch t $ \(PD2Intermediate x y) ->
    pcon $ PD2Element (punsafeCoerce $ pmod # x # pupcast fieldMod) (punsafeCoerce $ pmod # y # pupcast fieldMod)

-- Helpers

prealPart :: forall (s :: S). Term s (PD2Element :--> PNatural)
prealPart = phoistAcyclic $ plam $ \t -> pmatch t $ \case
    PD2Element r _ -> r

pimaginaryPart :: forall (s :: S). Term s (PD2Element :--> PNatural)
pimaginaryPart = phoistAcyclic $ plam $ \t -> pmatch t $ \case
    PD2Element _ i -> i

pd2Recip ::
    forall (s :: S).
    Term
        s
        ( PPositive
            :--> PPositive
            :--> PD2Intermediate
            :--> PD2Intermediate
        )
pd2Recip = phoistAcyclic $ plam $ \fieldMod rSquared t -> pmatch t $ \(PD2Intermediate x y) ->
    let recipExpr = (x #* x) #- (pupcast rSquared #* (y #* y))
     in plet (pexpModInteger # recipExpr # (-1) # pupcast fieldMod) $ \recipr ->
            pcon $ PD2Intermediate (x #* recipr) (pnegate # (y #* recipr))

pd2Pow' :: forall (s :: S). Term s (PPositive :--> PD2Intermediate :--> PInteger :--> PD2Intermediate)
pd2Pow' = phoistAcyclic $ pfix $ \self -> plam $ \rSquared x e ->
    pif
        (e #<= 1)
        x
        ( plet (pd2Square rSquared (self # rSquared # x #$ pquot # e # 2)) $ \squared ->
            punsafeCase
                (prem # e # 2)
                [ popaque squared
                , popaque (pd2Times rSquared x squared)
                ]
        )
