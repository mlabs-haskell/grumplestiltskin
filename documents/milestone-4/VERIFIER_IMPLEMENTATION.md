# Implementation of KZG using BLS12-381 Plutus primitives

## Introduction

We implemented [KZG-style][kzg] single polynomial opening verifier using the BLS12-381 pair of
elliptic curves, with the builtins provided by Plutus Core. This was designed to
serve two functions in the overall project, specifically relative Milestone 3
functionality:

* A correctness reference; and
* A performance comparison point.

To this end, we implemented a basic verifier for single polynomial commitments, 
(with a set of assumptions, to be described), as well as tests to verify it 
works correctly. The verifier was implemented as the `verify` function in the 
`Grumplestiltskin.Verify` module. We also defined a set of property-based tests 
in `test/bls-verifier`, which check both 'should verify' and 'shouldn't verify' cases. 

We did not implement a full PLONK-like system, but the single polynomial commitment
scheme used here serves as the foundation upon which a more sophisticated PLONK-like 
system may be built.

## Goals and priorities

Our goals with this implementation were a minimal useful demonstration of ZKP
functionality, using the most efficient and simple method available to Cardano
developers at the current time. In particular, we needed such an implementation
to both acts as a correctness reference for something implemented using
Grumplestiltskin primitives, but also as a benchmark for performance.

In particular, we made several decisions around the implementation, and its
testing, with this in mind. We elaborate these further in the Implementation
and Testing sections of this report.

## Overview of ZKP and KZG

For clarity, we give an overview of zero-knowledge proofs, and the KZG-style
commitment scheme. This is not designed to be a definitive description: we
provide only the information needed to make our implementation choices clear. 

### Zero-knowledge proof

A [zero-knowledge proof][zkp] is a method of one party (the _prover_) having
knowledge of some information to another party (the _verifier_), without
revealing anything beyond the fact that the prover knows the information. In our
specific case, the process is broadly as follows:

1. The prover sends a _commitment_ to the verifier, demonstrating their knowledge.
2. The verifier responds with a _challenge_ to the prover.
3. The prover sends a second commitment to a combination of the challenge and
   their knowledge to the verifier.
4. Using both commitments, the verifier checks whether the prover's
   demonstration of their knowledge holds.

Although we describe the process as an interaction between the prover and the
verifier, it can also be performed non-interactively. We will describe the
specifics of how this could be achieved and our related implementation
assumptions in a later section.

In general, any zero-knowledge proof scheme must satisfy the following
requirements:

* If the verifier is honest and following the protocol correctly, a prover that
  has knows some information must be able to demonstrate this fact to that verifier 
  (_completeness_);
* If a prover does not know some information, they should not be able to
  demonstrate to an honest verifier that they do know it, except with very low
  probability (_soundness_); and
* If a prover knows some information and successfully demonstrates this to a
  verifier, the verifier learns nothing more about the information than the fact
  the prover knows it (_zero-knowledge_).

### KZG over BLS12-381 preliminaries

Our zero-knowledge scheme is KZG-style single polynomial open verification. In this 
scheme, the information provers want to demonstrate knowledge of is represented as a
[polynomial][polynomial] $P$, of degree $d$, with all coefficients being
elements of a finite field. While seemingly restrictive, this is in fact sufficient to represent
any data: given a binary string $B = b_0, b_1, \ldots b_k$, we can encode it as the
polynomial

$$
B_p(x) = b_0 \cdot x^0 + b_1 \cdot x^1 + \ldots + b_k \cdot x^k
$$

Furthermore, polynomials of this kind can also encode [circuits][plonk-circuit],
which allows provers to demonstrate knowledge of computations. More sophisticated PLONK-style 
scheme allow provers to demonstrate knowledge of multiple polynomials at once. We will
not consider these here, as they do not change the core of the verification process itself.

In order to be useful, a KZG scheme requires a pair of [elliptic curves][elliptic-curve] 
connected by a [bilinear map][bilinear-map], with both curves being
defined over some [finite field][finite-field]. We use the [BLS12-381-G1 and
BLS12-381-G2 curves][bls12-381] for this purpose. For our specific purpose, it
is enough for us to know the following:

* Both elliptic curves form an [abelian groups][abelian-group-ec]; and
* Given the curves $E_1, E_2$, there exists a function $e : (E_1, E_2) \rightarrow E$
  such that for any $p_1 \in E_1, p_2 \in E_2, k \in \mathbb{F}_n$, $e(k \cdot
  p_1, p_2) = e(p_1, k \cdot p_2)$, where $\cdot$ is group exponentiation
  (repeated group operation).

We note the following algebraic identities. Given some elliptic curve (as
restricted above) $E$ over a finite field $\mathbb{F}_n$, $p_1 \in E$ and $k, \ell \in \mathbb{F}_n$, with $\mathbb{+}$ as the
group operation and $\mathbb{0}$ as the group identity, we have:

* $k \cdot p_1 \mathbb{+} \ell \cdot p_1 = (k + \ell) \cdot p_1$
* $k \cdot (\ell \cdot p_1) = (k \cdot \ell) \cdot p_1$
* $0 \cdot p_1 = \mathbb{0}$
* $1 \cdot p_1 = p_1$

From this, we can see that given any such elliptic curve, we can evaluate any polynomial
of interest to us using a point $p$ on such a curve as an indeterminate,
replacing multiplication by a coefficient with group exponentiation, where a
zero coefficient yields the group identity and a negative coefficient scales the
group inverse of the indeterminate instead.

An important component of KZG is the _trusted setup_, which consists of a set
of values available to both the prover and verifier. A trusted setup consists of
the following:

* Some $\tau$, an element of a finite field. This value is never directly revealed to either
  the prover or verifier.
* Some $p_1 \in E_1, p_2 \in E_2$. These are public information to both prover
  and verifier.
* For some $d \in \mathbb{N}$ and each $i \in 0, 1, \ldots d$, $\tau^i \cdot
  p_1$. We call this collection the _'powers'_ of $\tau$. These are public
  information to both prover and verifier.
* $\tau \cdot p_2$. This is public information to both prover and verifier.

Effectively, the trusted setup 'hides' $\tau$ by using group exponentiation over
$E_1$ and $E_2$, which ensures neither prover nor verifier can easily recover
it. The security of this process is based on the assumed hardness of the
[discrete logarithm problem][discrete-logarithm] over elliptic curves of this
form. Provided that $d$ is large enough (specifically, not less than the degree
of any polynomial we need to evaluate for verification), however, we can still
use $\tau$ as required by the KZG protocol. We will explain this process in
the subsequent section.

### Description of KZG verification over BLS12-381

Throughout this section, we use $E_1$ to refer to the elliptic curve defined
over the BLS12-381-G1 finite field, and $E_2$ to refer to the elliptic curve
defined over the BLS12-381-G2 finite field. Let $e : (E_1, E_2) \rightarrow E$ represent
a bilinear map. We will use $g_1 \in E_1, g2 \in E_2$ to represent designated
points on each curve as provided by the trusted setup, and $\tau$ to represent
the (hidden) constant used to evaluate commitments. We use $\mathbb{+}$ to
represent the group operation, and $\mathbb{-}$ to represent $\mathbb{+}$ with
the group inverse of the second argument.

Let $P$ be the polynomial the prover wants to demonstrate knowledge of to the
verifier. First, the prover constructs a _commitment_ to $P$ by producing  

$$
\tau \cdot P(g_1) \in E_1
$$

This can be done by the prover as, if $P$ with indeterminate $x$ is

$$
P(x) = c_0 \cdot x^0 + c_1 \cdot x^1 + \ldots + c_k \cdot x^k
$$

provided that the trusted setup contains 'powers' up to at least $\tau^k \cdot
g_1$, we have

$$
\tau \cdot P(g_1) = c_0 \cdot (\tau^0 \cdot g_1) + c_1 \cdot (\tau^1 \cdot g_1) + \ldots + c_k \cdot (\tau^k \cdot g_1)
$$

by the algebraic identities given previously. The prover then sends the
commitment to $P$ to the verifier. In response, the verifier sends a _challenge_
$k \in \mathbb{F}_{k}$. The prover then constructs a polynomial $Q$, which, with
indeterminate $x$ is defined as

$$
Q(x) = \frac{P(x) - P(r)}{x - r}
$$

This division is guaranteed to be exact by [little Bézout's
theorem][polynomial-remainder]. This is required, as polynomials are not closed under
division even if evaluated at a field. The prover then constructs a commitment
to $Q$ by producing

$$
\tau \cdot Q(g_1) \in E_1
$$

using the same method as the commitment to $P$. The prover sends the commitment
to $Q$ to the verifier, as well as the evaluation $P(r)$.

To verify that the prover knows $P$, the verifier checks that

$$
e(\tau \cdot Q(g_1), \tau \cdot g_2 \mathbb{-} (r \cdot g_2)) = e(\tau \cdot P(g_1) \mathbb{-} (P(r) \cdot g_1), g_2)
$$

If this holds, the verifier knows that at least one of the following is true:

* The prover knows $P$; 
* The prover has solved the discrete logarithm problem for the curves $E_1,
  E_2$.

Due to the intractability assumption for the discrete logarithm problem, the
prover can thus conclude that the prover does indeed know $P$. 

## Implementation

Based on our goals, we decided to implement KZG verification as a single
Plutarch function. In particular, we made the following decisions:

* Not making a full validator; 
* Resolving the issue of trusted setup; and
* Making the process non-interactive by assumption.

These require some justification. We felt that a full validator, while arguably
more realistic, wouldn't add any benefit given our goals. Our primary concern
was ensuring that we had a correct baseline to compare to implementations using
Grumplestitskin itself, as well as having a basis for performance benchmarking.
A full validator would not give us any new information relative either of these
concerns, but would significantly increase the work we would have to do. Thus,
we decided that a single function would be sufficient.

We assumed that the trusted setup (or rather, the parts required by the prover)
already exist. While this poses some difficulties in practice (particularly the
need to generate a cryptographically-random $tau$ without revealing it to either
party), it is achievable using a combination of the blockchain's capabilities
with regard to distributed consensus (even in the presence of adversaries), as
well as techniques similar to [the multiplayer RNG][multiplayer-rng]. Thus, we
assume that this problem has been solved.

Lastly, the interactive description of the KZG verification process does not
lend itself well to an implementation on the blockchain, where this kind of
interaction is costly. The main reason the interaction is required is that the
choice of $r$ is adversarial relative the prover: effectively, the verifier
should choose 'the most difficult' $r$ possible in order to challenge the
prover's claims to knowledge. What this means in practice is that the verifier
is incentivized to choose a number that's as random as possible: essentially, it
must resemble the output of a [cryptographically-secure
PRNG][cryptographically-secure-prng]. Indeed, without knowing more about the $P$
that the prover wants to demonstrate knowledge of, the verifier cannot choose a
'worse' challenge in general. Given the assumption that a trusted setup exists,
and that it is capable of producing $\tau$ pseudorandomly, without revealing
$\tau$ to either party, having the same setup produce $r$ _without_ the
requirement that it be hidden seems to be a safe simplifying assumption for
the purpose of testing. (It is likely a necessary simplifying assumption for testing, 
as having a third party generate $r$ would require a suite of fully-developed contracts.)

Based on the above decisions, we implemented the verification functionality in
`Grumplestiltskin.Verify` as follows:

```haskell
verify ::
    forall (s :: S).
    Term
        s
        ( PBuiltinBLS12_381_G1_Element
            :--> PBuiltinBLS12_381_G2_Element 
            :--> PBuiltinBLS12_381_G2_Element
            :--> PBuiltinBLS12_381_G1_Element
            :--> PInteger
            :--> PInteger
            :--> PBuiltinBLS12_381_G1_Element
            :--> PBool
        )
verify = phoistAcyclic $ plam $ \g1 tau_X_G2 g2 pTau_X_G1 r pR qTau_X_G1 ->
    let lhs = pbls12_381_millerLoop # qTau_X_G1 # (tau_X_G2 #- (pbls12_381_G2_scalarMul # r # g2))
        rhs = pbls12_381_millerLoop # (pTau_X_G1 #- (pbls12_381_G1_scalarMul # pR # g1)) # g2
     in pbls12_381_finalVerify # lhs # rhs
```

Essentially, we assume that all of the following are provided to the verifier
'at once':

* $g_1$
* Commitments to $P$ and $Q$
* $r$
* $P(r)$
* $\tau \cdot g_2$

Given this information, we can perform the last step of the process directly as
described above. We use the BLS12-381 functionality provided by
[CIP-381][cip-381] to implement the elliptic curve operations required by this
operation, as well as the bilinear pairing over the BLS12-381 curves. 

## Testing

To ensure that our implementation was correct, we defined property tests in
`test/bls-verifier`. In particular, we wanted to check that:

* If given valid arguments, `verify` should produce `PTrue`; and
* If given invalid arguments, `verify` should produce `PFalse`.

While what constitutes 'valid arguments' is clear from our description above,
'invalid arguments' requires some explanation. We can see that issues with
$g_1$, $r$ or $\tau \cdot g_2$ are essentially impossible: these values are
provided by the trusted setup, and thus, could be validated by the verifier if
in doubt. This leaves only values based on $P$ or $Q$, which are the two
commitments, plus $P(r)$. Thus, the primary 'failure mode' is if the commitment
to $P$ and commitment to $Q$ are incorrectly correlated: that is, if the
commitment to $Q$ is constructed as a quotient of a different polynomial to $P$.
This mimics the situation where a prover supplies an arbitrary curve point as a
commitment to $P$, then 'makes up' $Q$ and $P(r)$. 

To this end, we need to generate the following:

* $P$
* $\tau$
* $r$
* $P^{\prime} \neq P$

For all polynomial operations (including generation) we used the [`poly`][poly]
library. As $\tau$ and $r$ are both `Integer`s to simplify testing (though 
conceptually they could be elements of an arbitrary finite field) they could be generated
directly. We excluded certain specific generated results:

* Any zero polynomial; firstly, as knowledge of the zero polynomial is trivial
  (and thus, would never need to be proved in practice), and secondly as any
  commitment to the zero polynomial is the group identity irrespective of $\tau$
  or $g_1$.
* $\tau$ values in the range $[-100, 100]$, as these are too trivial to provide
  useful test data.

We defined two properties:

1. Given a commitment to $P$, and a correctly corresponding commitment to $Q$
   (constructed based on $P$ using the values provided by the trusted setup),
   `verify` should accept; and
2. Given a commitment to $P$, and a commitment to $Q$ based on a _different_
   polynomial $P^{\prime}$ (using the values provided by the trusted setup),
   `verify` should reject.

These properties together demonstrate both that the 'happy path' works, but also
that a fabricated commitment will be rejected.

[kzg]: https://www.zkdocs.com/docs/zkdocs/commitments/kzg_polynomial_commitment/
[plonk]: https://eprint.iacr.org/2019/953
[zkp]: https://en.wikipedia.org/wiki/Zero-knowledge_proof
[polynomial]: https://en.wikipedia.org/wiki/Polynomial
[plonk-circuit]: https://medium.com/@cryptofairy/under-the-hood-of-zksnarks-plonk-protocol-part4-5e74bddebedb
[elliptic-curve]: https://en.wikipedia.org/wiki/Elliptic_curve
[bilinear-map]: https://en.wikipedia.org/wiki/Bilinear_map
[finite-field]: https://en.wikipedia.org/wiki/Finite_field
[bls12-381]: https://link.springer.com/chapter/10.1007/3-540-36413-7_19
[abelian-group-ec]: https://en.wikipedia.org/wiki/Elliptic_curve#Elliptic_curves_over_finite_fields
[polynomial-remainder]: https://en.wikipedia.org/wiki/Polynomial_remainder_theorem
[multiplayer-rng]: https://www.jookia.org/wiki/Multiplayer_RNG
[cryptographically-secure-prng]: https://en.wikipedia.org/wiki/Cryptographically_secure_pseudorandom_number_generator
[cip-381]: https://github.com/cardano-foundation/CIPs/tree/master/CIP-0381
[poly]: https://hackage.haskell.org/package/poly
[discrete-logarithm]: https://en.wikipedia.org/wiki/Discrete_logarithm#Cryptography
