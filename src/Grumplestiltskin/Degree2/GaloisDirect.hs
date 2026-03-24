{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Grumplestiltskin.Degree2.GaloisDirect (
    -- * Types

    -- ** SOP-encoded
    PD2Intermediate,

    -- * Functions

    -- ** Operations
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

import GHC.Generics (Generic)
import Generics.SOP qualified as SOP
import Grumplestiltskin.Degree2.Element (PD2Element (PD2Element))
import Plutarch.Builtin.Integer (pexpModInteger)
import Plutarch.Internal.Case (punsafeCase)
import Plutarch.Prelude (
    DeriveAsSOPStruct (DeriveAsSOPStruct),
    PAdditiveGroup (pnegate, pscaleInteger, (#-)),
    PAdditiveMonoid (pscaleNatural, pzero),
    PAdditiveSemigroup (pscalePositive, (#+)),
    PInteger,
    PMultiplicativeSemigroup ((#*)),
    PPositive,
    PShow,
    PlutusType,
    S,
    Term,
    pcon,
    pcond,
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
    (#==),
    (:-->),
 )
import Plutarch.Unsafe (punsafeCoerce)
import Test.QuickCheck.Instances.Natural ()

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
    pscaleNatural t n = pmatch t $ \(PD2Intermediate x y) ->
        pcon $ PD2Intermediate (pscaleNatural x n) (pscaleNatural y n)

-- | @since wip
instance PAdditiveGroup PD2Intermediate where
    pnegate = phoistAcyclic $ plam $ \t -> pmatch t $ \(PD2Intermediate x y) ->
        pcon $ PD2Intermediate (pnegate # x) (pnegate # y)
    t1 #- t2 = pmatch t1 $ \(PD2Intermediate x1 y1) ->
        pmatch t2 $ \(PD2Intermediate x2 y2) ->
            pcon $ PD2Intermediate (x1 #- x2) (y1 #- y2)
    pscaleInteger t i = pmatch t $ \(PD2Intermediate x y) ->
        pcon $ PD2Intermediate (pscaleInteger x i) (pscaleInteger y i)

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
    pcond
        [ (e #== 0, pd2OneI)
        , (e #<= (-1), pd2Recip # fieldMod # rSquared #$ pd2Pow' # rSquared # x #$ pnegate # e)
        ]
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
