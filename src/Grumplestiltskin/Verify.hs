module Grumplestiltskin.Verify (verify) where

import Plutarch.Builtin.BLS (
    PBuiltinBLS12_381_G1_Element,
    PBuiltinBLS12_381_G2_Element,
    pbls12_381_G1_scalarMul,
    pbls12_381_G2_scalarMul,
    pbls12_381_finalVerify,
    pbls12_381_millerLoop,
 )
import Plutarch.Internal.Term (S, Term)
import Plutarch.Prelude (
    PBool,
    PInteger,
    phoistAcyclic,
    plam,
    (#),
    (#-),
    (:-->),
 )

verify ::
    forall (s :: S).
    Term
        s
        ( -- G1 (kind of from the setup)
          PBuiltinBLS12_381_G1_Element
            -- tau | G_2 (from setup)
            :--> PBuiltinBLS12_381_G2_Element
            -- G_2 (from setup, presumably)
            :--> PBuiltinBLS12_381_G2_Element
            -- P(tau) | G_1 (from prover)
            :--> PBuiltinBLS12_381_G1_Element
            -- r (scalar, per proof, provided by agreed-upon CSPRNG)
            :--> PInteger
            -- P(r) (from the prover)
            :--> PInteger
            -- Q(tau) | G_1 (from prover)
            :--> PBuiltinBLS12_381_G1_Element
            :--> PBool
        )
verify = phoistAcyclic $ plam $ \g1 tau_X_G2 g2 pTau_X_G1 r pR qTau_X_G1 ->
    let lhs = pbls12_381_millerLoop # qTau_X_G1 # (tau_X_G2 #- (pbls12_381_G2_scalarMul # r # g2))
        rhs = pbls12_381_millerLoop # (pTau_X_G1 #- (pbls12_381_G1_scalarMul # pR # g1)) # g2
     in pbls12_381_finalVerify # lhs # rhs
