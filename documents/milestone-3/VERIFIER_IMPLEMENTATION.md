# Implementation of ZK Proof Verifier Prototype

## Introduction

In accordance with the goals of Milestone 3, we designed and implemented a ZK proof verifier prototype using existing Plutus BLS primitives and builtin functions, plus a set of basic "offchain" tools which allow us to simulate the steps performed by the prover. We also verified the correctness of the implementation with a simple property test suite. The details of the work on this milestone are as follows:
  - `src/Grumplestiltskin/Verify.hs` contains our implementation of the verifier
  - `test/bls-verifier/Main.hs` contains our property test suite, including the "offchain" code that simulates the prover

All onchain components were written using the Plutarch eDSL. Since there is really only one (sensible, sane) way to implement the verifier, we expect that our implementation is as efficient as any implementation that uses the primitives and builtins could be.

The "offchain" components use the `cardano-crypto-class` library, which is the library that the Plutus primitives and builtin functions use under the hood. This should ensure a high degree of compatibility with the Plutus


## Goals and Priorities

Our main priority was to create an efficient "stock" prover and verifier, using only primitive types and builtin functions supported by Plutus. We did this for several reasons:
  - We were not aware of an existing implementation
  - We wished to have a metric of comparison against which we could check the more flexible (but substantially more complex) Grumplestiltkin verification logic
  - We wished to have a simple and trivial implementation to provide us with a high degree of assurance that we adequately understand the underlying mathematical concepts
  
Because understanding the mathematics that enable ZKP verification was likely the most time-consuming part of work on this milestone, the next section will go over the mathematics at a level that is meant to be "comprehensible for normal programmers". 

## ZKP Mathematics For Programmers (Implementation Overview)

### Preliminaries 

NOTE: All equations were sourced from [Under the hood of zkSNARKs — PLONK protocol](https://medium.com/coinmonks/under-the-hood-of-zksnarks-plonk-protocol-part-1-34bc406d8303), and, unsurprisingly, the ZK proving system we use is PLONK. Since this style of ZK verification requires two elliptic curves, we use the `BLS12-381` and `BLS12-382` curves that Plutus supports with primitive types and builtin functions. For the sake of brevity, we will refer to the former as the `G1` curve and the latter as the `G2` curve. 

The ZKP verification process can be thought of as a kind of game between two entities, the prover and the verifier. Very generally, the prover encodes a piece of information in an indirect manner which allows the verifier to ascertain that the prover knows the information they claim to, without revealing the content of that information.  

If you are familiar with systems built on top of ZKP verification, you are likely acquainted with the concept of a _ZK Circuit_, which provides a mechanism that allows the prover to encode (potentially complex) pieces of information. While you might expect that circuits are a fundamental ingredient of zero-knowledge proofs, we will ignore circuit abstractions here. A circuit (or any other high level abstraction) serves as a user-friendly way to describe (potentially very complex) *commitments to a polynomial*. Put another way: Circuits construct commitments, but the details of how those commitments are constructed is irrelevant to the verification process, which only cares that some commitment has been constructed and is available for verification. 

If commitments are what a ZK verifier verifies, it would be useful to begin by explaining what, exactly, a commitment is. *A commitment is a curve point* that is constructed from a *polynomial* and *a sequence of points on the curve*. The manner in which a commitment is constructed can be seen in the `commit` helper function from the `bls-verifier` test suite: 

```haskell
commit :: Poly Vector Integer -> Vector (Point Curve1) -> G1.Element
commit poly taus
    | null asVec = G1.Element $ Vector.head taus #* 0
    | otherwise = G1.Element . Vector.foldl1' (#+) . Vector.zipWith (#*) taus $ unPoly poly
  where
    asVec :: Vector Integer
    asVec = unPoly poly
```

A few elements of this function require explanation: 
  - For the purposes of commitment construction, the polynomial argument can be regarded as a vector of integers that represent the coefficients of the polynomial. The polynomial `2x^2 + 3x^1 + 5`, for example, can be represented as a list or vector of coefficients `[2,3,5]`. (It is not represented in precisely this way by the `poly` library we use in the test suite, but this is an implementation detail.)
  - Points on a finite ellpitic curve form a commutative group over addition and a monoid over multiplication. In ordinary English, means that we can *add curve points to one another* and *multiply curve points by scalar values*, which in this context, will always be values of type `Integer`. The `#+` and `#*` operators implement addition and scaling (multiplication) respectively. 

Having established that a ZK verifier verifies commitments, and that commitments are constructed from polynomials and a series of points on the curve, astute readers are probably wondering _what exactly the polynomial represents_ and _where we get the series of points on the curve from_. 

The polynomial can represent (effectively) _anything at all_. Specifically, the coefficients of the polynomial can be used to encode any piece of data which can be encoded using an ordered set of integers, and, therefore, can encode arbitrary programs or pieces of data. One might decide that the coefficients, for example, represent individual bits in a byte, or bytes in a longer byte string, etc. 

The _series of points on the curve_, which make up the second ingredient for constructing a commitment to be verified, are not chosen arbitrarily, or indeed chosen by the person or entity constructing the commitment at all. This series (`taus` in the example) is provided by the *trusted setup*, which is a shared source of information common to both the prover and verifier. 

The *trusted setup* provides several bits of information which are necessary for constructing and verifying commitments. Specifically, those bits of information are: 
  - A point on the `G1` curve, which we will call `G1`
  - *The Tau Series* (not the official name): The integrity of the proof and verification process depends upon both the prover and the verifier having access to the scalar value `tau` (an `Integer`) without _knowing the value directly_. This is achieved by constructing a series, containing at least enough elements as there are coefficients in the polynomial being verified, with the shape `G1 #* (tau ^ c0), G1 #* (tau ^ c1), etc` where `c0...cN` corresponds to indices of the coefficients in the polynomial `P` to which we are committing. If `P` is `5x + 1`, for example, it has two coefficients (interpreting the constant `1` as shorthand for `1x^0`), so the `tau` series must have at least two elements. 
  - A point on the `G2` curve, which we will call `G2`
  - Some scalar value `r`, provided by a cryptographically secure random number generator such that it is indistinguishable from random noise. 
  - `G2 #* tau`, that is, the point on the G2 curve scaled by `tau`
  
If the hardness assumption holds, the intractibility of the discrete logarithm problem ensures that the `tau` value cannot be recovered from the `tau` series. The `tau` value itself is consequently kept secret from both the prover and verifier. 
  
Formally, `r` does not strictly need to be provided by the trusted setup, but for presentation purposes it is easier to assume that it is provided by the setup. Similarly, the `G2` point does not strictly need to be provided by the setup, but `G2 #* tau` does, so again, for our purposes we can regard it as provided by the setup. 

One final piece of context needs to be mentioned: In formal presentations of ZK verification logic, the process is frequently explained (for understandable pedagogical purposes) as an _iterative game between the prover and verifier_, such that the prover completes one "move", then sends the result to the verifier, who completes the next "move", and so on. This, however, is an implementation detail, and we can compress the asynchronous iterative process into a synchronous one, such that the prover can construct the commitment and send it to the verifier in one step. Since the non-iterative variant of the verification game is the only sensible choice for an on-chain implementation, we implemented that variant.

### Constructing a Commitment (Prover Side)

In the non-iterative/synchronous variation of ZKP verification that we implemented, the prover constructs everything needed for verification, all at once, then sends it to the verifier. The pieces of information needed for verification are: 
  - The components of the *trusted setup*, which are shared between the prover and verifier 
  - The commitment to some polynomial `P` which represents the information the prover wishes to prove that it knows 
  - Another commitment to some polynomial `Q` which is constructed from `P` and is required for verification 
  - The evaluation of the polynomial `P` at the `r :: Integer` value provided by the *trusted setup*

Note that `P` is *never* directly shared with the verifier, since doing so would defeat the purpose of a zero-knowledge proof. Only the commitments to `P` and `Q` (and the evaluation of `P(r)`) are ever shared with the verifier, which plainly cannot reconstruct the original polynomial from the commitments. Commitments are curve points and do not contain enough information to reconstruct the original polynomials used to construct them. 

Constructing the commitment to `P` is incredibly straightforward: We just plug the polynomial `P` and the tau series into the previously explained function which constructs commitments, a la : 

```haskell
let trustedSetupTauSeries :: Vector (Point Curve1)
    trustedSetupTauSeries = ...
    
    p :: Poly Vector Integer 
    p = ... 
    
    pCommitment :: Point Curve1 
    pCommitment = commit p trustedSetupTauSeries
```

The commitment to `Q`, however, requires some explanation. `Q` is a polynomial derived from the `P` polynomial. Specifically, the `Q` polynomial is defined as: 

```
Q(x) = (P(x) - P(r)) / (x - r)
```

The polynomial remainder theorem assures us that this (Euclidean) division has no remainder, which is necessary for constructing and verifying the commitment, since division is not defined for elliptic curve points. 


It is important to keep in mind here that `P` simply refers to an arbitrary polynomial. While the polynomial remainder theorem assures us that the result of polynomial division will have no remainder, and that we will therefore always arrive at a `Q` from which a commitment can be constructed, Euclidean division must be performed on each arbitrary polynomial `P` to arrive at the corresponding `Q` polynomial.  

Fortunately, we can lean on the Haskell `poly` library to perform Euclidean division in general, like so: 

```haskell
import Data.Euclidean (divide)
import Data.Poly (pattern X, eval, toPoly, ...)

let 
  -- A helper function for constructing constant Polynomials from Integers. Largely an implementation detail
  constPoly :: Integer -> Poly Vector Integer
  constPoly i = toPoly (Vector.fromList [i])
  
  -- P(r)
  pR :: Integer 
  pR = eval p r
  
  -- Q(x), this is a literal translation using the Data.Poly interface
  qX :: Poly Vector Integer 
  qX = fromJust $ (p - constPoly pR) `divide`  (X - constPoly r)
  
  qCommitment :: G1.Element 
  qCommitment = commit qX trustedSetupTaus
  
  ...
```

With that, the prover has constructed everything it needs to send to the verifier. 

### Verifying Commitments (Verifier Side)

The implementation of the verifier is simpler than the prover. In order to verify the prover's commitments, the verifier must employ some function (called `e` in some of the literature, but concretely implemented as the `bls12_381_millerLoop` builtin in Plutus) to construct a set bilinear pairings using the `P` and `Q` commitments and a point on the second curve (`G2`), and check that the pairing are equivalent.

Specifically, the verification logic is: 

```
let e indicate the bilinear pairing function with the type `e :: G1.Element -> G2.Element -> MlResult`
let g2_X_tau indicate `G2 #* tau` from the setup  

e(qCommitment, g2_X_tau - (G2 #* r)) == e(pCommitment - (G1 #* r), G2)
```

A literal translation of this into Plutarch yields the code for our `verify` function, with Plutarch equivalents to `e` and `==` that ought to be obvious from the context, and having renamed the arguments to conform with the names used in the above presentation of the prover: 

```
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
verify = phoistAcyclic $ plam $ \g1 g2_X_tau g2 pCommitment r pR qCommitment ->
    let lhs = pbls12_381_millerLoop # qCommitment # (g2_X_tau #- (pbls12_381_G2_scalarMul # r # g2))
        rhs = pbls12_381_millerLoop # (pCommitment #- (pbls12_381_G1_scalarMul # pR # g1)) # g2 
     in pbls12_381_finalVerify # lhs # rhs
```

Which implements the verification logic using Plutarch versions of Plutus primitives. 

### Testing & Validation

In order to verify that we had correctly implemented ZKP verification, we wrote a property test suite (in the `test/bls-verifier` directory) which contains two property tests (and several helpers). 

The first property checks for successful validation of commitments to arbitrary polynomials. Using `QuickCheck`, each test generates an arbitrary `tau`, `r`, and `P`, then constructs the commitments to `P` and `Q`, and invokes the Plutarch verifier. 

The second property checks that validation should fail in cases where the commitments do not match. To check this, we generate everything we did for the previous property, but also generate an additional polynomial `P'` (which is restricted so as to never be equivalent to `P`). We construct the `P` commitment using `P`, but we construct the `Q` commitment using `P'` and then invoke the verifier. This ought to fail, since the commitments do not match. 

At present our property test suite runs ten thousand test cases for each property. All of the "happy path" tests pass, and all of the "should fail" tests fail. For an extremely high degree of assurance, the author of this report ran one million test cases for each property locally, which passed. 

The only significant restriction on the arbitrarily generated values used by the tests is that we require all arbitrary polynomials to have at least one non-zero coefficient. This is largely an implementation detail relating the the way that the `poly` library works, and does not have major consequences for our verifier, since any useful `P` polynomial should have a nonzero coefficient.



